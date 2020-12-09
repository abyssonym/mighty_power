from randomtools.tablereader import (
    TableObject, get_global_label, tblpath, addresses, get_random_degree,
    get_activated_patches, mutate_normal, shuffle_normal, write_patch)
from randomtools.utils import (
    classproperty, cached_property, get_snes_palette_transformer,
    read_multi, write_multi, utilrandom as random)
from randomtools.interface import (
    get_outfile, get_seed, get_flags, get_activated_codes, activate_code,
    run_interface, rewrite_snes_meta, clean_and_write, finish_interface)
from collections import defaultdict
from os import path
from time import time, sleep, gmtime
from collections import Counter
from itertools import combinations
from sys import argv, exc_info
from traceback import print_exc


VERSION = 1


class ChestObject(TableObject):
    @property
    def name(self):
        return AttributeNameObject.get(self.contents).name

    @cached_property
    def rank(self):
        if not self.intershuffle_valid:
            return -1
        return ItemPriceObject.get(self.contents).rank

    @property
    def contents(self):
        return self.contents_lowbyte | ((self.misc - 0xf9) << 8)

    @property
    def intershuffle_valid(self):
        return self.contents < 0xff


class MoveSelectionObject(TableObject):
    @property
    def num_moves(self):
        assert self.probabilities == sorted(self.probabilities)
        return self.probabilities.index(0xFF) + 1


class AttributeObject(TableObject):
    @property
    def name(self):
        return AttributeNameObject.get(self.index).name

    @property
    def rank(self):
        return -1


class MonsterMeatObject(TableObject): pass
class RobotStatObject(TableObject): pass


class MonsterLevelObject(TableObject):
    @property
    def move_selection_index(self):
        return self.moves_level >> 4

    @property
    def level(self):
        return self.moves_level & 0xF

    @cached_property
    def rank(self):
        return self.level


class UsesObject(TableObject):
    @cached_property
    def rank(self):
        return self.uses


class StatGrowthObject(TableObject): pass
class MutantSkillsObject(TableObject): pass


class FormationObject(TableObject):
    @property
    def name(self):
        s = ','.join(MonsterNameObject.get(i).name for i in self.enemy_indexes)
        s += ' | {0} . {1}'.format(
            FormationCountObject.get(self.unknown[0] & 0x1f).name,
            FormationCountObject.get(self.unknown[1] & 0x1f).name)
        return s

    @property
    def fcounts(self):
        return (FormationCountObject.get(self.unknown[0] & 0x1f),
                FormationCountObject.get(self.unknown[1] & 0x1f))

    @cached_property
    def rank(self):
        rank = 0
        for fcount in self.fcounts:
            for count, enemy_index in zip(fcount.counts, self.enemy_indexes):
                rank += (count * MonsterObject.get(enemy_index).rank)
        return rank


class FormationCountObject(TableObject):
    @property
    def name(self):
        s = '/'.join(['%s-%s' % (c >> 4, c & 0xf) for c in self.counts])
        return s

    @cached_property
    def rank(self):
        return sum([c >> 4 for c in self.counts] +
                   [c & 0xf for c in self.counts])


class MonsterObject(TableObject):
    def __repr__(self):
        s = self.name
        s += '\n{0:>5} {1:>3} {2:>3} {3:>3} {4:>3}'.format(
                'HP', 'STR', 'DEF', 'AGI', 'MAN')
        s += '\n{0:>5} {1:>3} {2:>3} {3:>3} {4:>3}'.format(
                self.hp, self.strength, self.defense, self.agility, self.mana)
        probabilities = self.move_selection.probabilities
        for i, ai in enumerate(self.attribute_indexes):
            if i == 0:
                p0 = 0
            else:
                p0 = probabilities[i-1]
            p1 = probabilities[i]
            p = int(round(((p1 - p0) / 255.0) * 100))
            p = '{0:>3}%'.format(p) if p > 0 else ' -- '
            s += '\n  {0} {1}'.format(p, AttributeNameObject.get(ai).name)
        return s.strip()

    def read_data(self, filename, pointer=None):
        super(MonsterObject, self).read_data(filename, pointer)
        f = open(filename, 'r+b')
        f.seek(self.attacks_pointer | 0x30000)
        self.attribute_indexes = []
        for i in range(self.num_attributes):
            self.attribute_indexes.append(ord(f.read(1)))
        f.close()

    @property
    def move_selection(self):
        return MoveSelectionObject.get(
            MonsterLevelObject.get(self.index).move_selection_index)

    @property
    def num_attributes(self):
        num_attributes = (self.misc_attributes & 0xf) + 1
        assert 1 <= num_attributes <= 8
        return num_attributes

    def set_num_attributes(self):
        num_attributes = len(self.attribute_indexes) - 1
        assert 0 <= num_attributes <= 7
        self.misc_attributes &= 0xf0
        self.misc_attributes |= num_attributes

    @cached_property
    def name(self):
        return MonsterNameObject.get(self.index).name

    @cached_property
    def rank(self):
        rank = sum([self.strength, self.agility, self.mana, self.defense])
        if self.mana > 0:
            return rank / 4
        else:
            return rank / 3

    @property
    def sprite_index(self):
        if self.index >= 0xe1:
            return self.index
        return self.index / 5

    def cleanup(self):
        self.set_num_attributes()

    def write_data(self, filename, pointer=None):
        if not hasattr(MonsterObject, 'attacks_address'):
            MonsterObject.attacks_address = min(
                [m.old_data['attacks_pointer'] for m in MonsterObject.every])
            MonsterObject.attacks_data = bytearray([])
            assert MonsterObject.attacks_address != 0
            f = open(filename, 'r+b')
            f.seek(MonsterObject.attacks_address | 0x30000)
            length = ((addresses.monster_attacks_end & 0xFFFF) -
                      MonsterObject.attacks_address)
            f.write(b'\x00' * length)
            f.close()

        assert len(self.attribute_indexes) == self.num_attributes
        duplicates = [
            m for m in MonsterObject.every if hasattr(m, '_attacks_written')
            and m._attacks_written and self.attribute_indexes
            == m.attribute_indexes[:self.num_attributes]]

        try:
            index = MonsterObject.attacks_data.index(
                bytearray(self.attribute_indexes))
            self.attacks_pointer = MonsterObject.attacks_address + index
        except ValueError:
            #self.attacks_pointer = MonsterObject.attacks_address
            self.attacks_pointer = (MonsterObject.attacks_address +
                                    len(MonsterObject.attacks_data))
            assert self.attacks_pointer <= 0xFFFF

            f = open(filename, 'r+b')
            f.seek(self.attacks_pointer | 0x30000)
            f.write(bytes(self.attribute_indexes))
            assert f.tell() <= addresses.monster_attacks_end
            f.close()

            MonsterObject.attacks_data += bytearray(self.attribute_indexes)

            assert (MonsterObject.attacks_address <=
                    (addresses.monster_attacks_end & 0xFFFF))

        super(MonsterObject, self).write_data(filename, pointer)


class RNGObject(TableObject):
    intershuffle_attributes = ['value']


class NameMixin(TableObject):
    @cached_property
    def name(self):
        codemap = {
            0xee: "'",
            0xf0: '.',
            0xf2: '-',
            0xff: ' ',
        }
        s = ''
        for c in self.name_str:
            if 0xd4 <= c < 0xd4 + 26:
                s += chr(ord('a') + c - 0xd4)
            elif 0xb0 <= c < 0xb0 + 10:
                s += '0123456789'[c - 0xb0]
            elif 0xba <= c < 0xba + 26:
                s += chr(ord('A') + c - 0xba)
            elif c in codemap:
                s += codemap[c]
            else:
                s += '<{0:0>2x}>'.format(c)
        return s


class AttributeNameObject(NameMixin): pass
class MonsterNameObject(NameMixin): pass


class ItemPriceObject(TableObject):
    @property
    def name(self):
        return '{0:<11}: {1:>5}'.format(
            AttributeNameObject.get(self.index).name, self.price)

    @cached_property
    def rank(self):
        if 10 <= self.price <= 65535:
            return self.price
        uses = UsesObject.get(self.index).uses
        if 1 <= uses < 99:
            return 999999
        return -1


class ShopObject(TableObject): pass


if __name__ == '__main__':
    try:
        print ('You are using the Final Fantasy Legend II '
               'randomizer version %s.' % VERSION)
        print

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]

        codes = {
                 }

        run_interface(ALL_OBJECTS, snes=False, codes=codes,
                      custom_degree=False)

        '''
        for c in ChestObject.every:
            print c

        for ano in AttributeNameObject.every:
            print ano

        #for i in ItemPriceObject.every:
        #    print i

        counts = defaultdict(int)
        for f in FormationObject.every:
            print f
            for u in f.unknown:
                counts[u & 0x1f] += 1
        print counts
        print sorted(counts, key=lambda k: counts[k])

        for f in FormationCountObject.every:
            print f
        '''

        clean_and_write(ALL_OBJECTS)

        for m in MonsterObject.ranked:
            print(m)
            print()

        finish_interface()

    except Exception:
        print_exc()
        print('ERROR:', exc_info()[1])
        input('Press Enter to close this program. ')
