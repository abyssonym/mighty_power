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


class VanillaObject(TableObject):
    flag = 'v'
    flag_description = 'nothing'


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

    @property
    def is_equipment(self):
        return bool(self.property_flags & 0xf)

    @cached_property
    def is_buyable(self):
        if self.index >= 0xFF:
            return False

        for s in ShopObject.every:
            if self.index in s.old_data['items']:
                return True

        return False

    @cached_property
    def is_equipped_on_monster(self):
        for m in MonsterObject.every:
            if self.index in m.old_data['attribute_indexes']:
                return True

        return False


class MonsterMeatObject(TableObject):
    flag = 'e'
    flag_description = 'monster evolutions'

    @property
    def meat_family(self):
        return self.meat >> 4

    @property
    def meat_class(self):
        return {0: 'A',
                1: 'B',
                2: 'C'}[self.meat & 0xf]

    @classmethod
    def randomize_all(cls):
        super(MonsterMeatObject, cls).randomize_all()
        random_degree = MonsterMeatObject.random_degree
        families = list(range(12))
        random.shuffle(families)
        meat_map = {}
        for i, f in enumerate(families):
            meat_classes = [0, 1, 2]
            if random.random() < (random_degree ** 0.5):
                random.shuffle(meat_classes)
                checks = ['a', 'b']
                random.shuffle(checks)
                for check in checks:
                    if check == 'a' and (meat_classes[0] == max(meat_classes)
                            and random.random() > random_degree):
                        meat_classes[:2] == list(reversed(meat_classes[:2]))
                    if check == 'b' and (meat_classes[-1] == min(meat_classes)
                            and random.random() > random_degree):
                        meat_classes[-2:] == list(reversed(meat_classes[-2:]))
            assert len(set(meat_classes)) == 3
            for j, c in enumerate(meat_classes):
                old_value = (f << 4) | c
                new_value = (i << 4) | j
                meat_map[old_value] = new_value

        assert sorted(meat_map.keys()) == sorted(meat_map.values())

        for mmo in MonsterMeatObject.every:
            if mmo.meat in meat_map:
                mmo.meat = meat_map[mmo.meat]

class MonsterEvolutionObject(TableObject):
    def validate(self):
        assert len(set(self.monster_indexes)) == 5
        assert len(self.monster_indexes) == 16
        assert self.monster_indexes == sorted(self.monster_indexes)
        assert max(self.monster_indexes) - min(self.monster_indexes) == 4

    def preclean(self):
        # correcting errors in the original rom
        if self.index == 6:
            self.monster_indexes = [0x1E if i == 0xF5 else i
                                    for i in self.monster_indexes]
        if self.index == 19:
            self.monster_indexes = [0x5F if i == 0x6F else i
                                    for i in self.monster_indexes]
        if self.index == 20:
            self.monster_indexes = [0x64 if i == 0xF6 else i
                                    for i in self.monster_indexes]
        if self.index == 31:
            self.monster_indexes = [0x9B if i == 0xF7 else i
                                    for i in self.monster_indexes]

    def cleanup(self):
        self.validate()
        monsters = [MonsterObject.get(i)
                    for i in sorted(set(self.monster_indexes))]
        levels = [m.level for m in monsters]
        assert len(levels) == 5
        assert levels == sorted(levels)
        assert levels[-1] == 0xb
        monster_indexes = []
        for level in range(16):
            candidates = [m for m in monsters if m.level <= level]
            if not candidates:
                candidates = [min(monsters, key=lambda c: c.level)]
            monster_indexes.append(candidates[-1].index)
        self.monster_indexes = monster_indexes
        self.validate()


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
        s = '{0:0>2X} {1}'.format(self.index, self.name)
        s += '\n{5:>2} {0:>5} {1:>3} {2:>3} {3:>3} {4:>3}'.format(
                'HP', 'STR', 'DEF', 'AGI', 'MAN', 'LV')
        s += '\n{5:>2X} {0:>5} {1:>3} {2:>3} {3:>3} {4:>3}'.format(
                self.hp, self.strength, self.defense,
                self.agility, self.mana, self.level)
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

    @property
    def meat(self):
        return MonsterMeatObject.get(self.index)

    def calculate_evolution(self, other):
        new_family = (self.meat.meat_family + other.meat.meat_family + 6)
        if other.meat.meat_family > 6:
            new_family += 1
        new_species = (new_family * 3) + 1
        meat_classes = [self.meat.meat_class, other.meat.meat_class]
        if 'A' in meat_classes:
            new_species -= 1
        if 'C' in meat_classes:
            new_species += 1
        new_species = new_species % len(MonsterEvolutionObject.every)
        indexes = MonsterEvolutionObject.get(new_species).monster_indexes
        level = max(self.level, other.level)
        result = MonsterObject.get(indexes[level])
        return result

    def read_data(self, filename, pointer=None):
        super(MonsterObject, self).read_data(filename, pointer)
        f = open(filename, 'r+b')
        f.seek(self.attacks_pointer | 0x30000)
        self.attribute_indexes = []
        for i in range(self.num_attributes):
            self.attribute_indexes.append(ord(f.read(1)))
        self.old_data['attribute_indexes'] = list(self.attribute_indexes)
        f.close()

    @property
    def level(self):
        return MonsterLevelObject.get(self.index).level

    @property
    def move_selection(self):
        return MoveSelectionObject.get(
            MonsterLevelObject.get(self.index).move_selection_index)

    @property
    def num_attributes(self):
        num_attributes = (self.misc_attributes & 0xf) + 1
        assert 1 <= num_attributes <= 8
        return num_attributes

    @property
    def is_human(self):
        return (self.misc_attributes >> 4) == 0

    @property
    def is_mutant(self):
        return (self.misc_attributes >> 4) == 1

    @property
    def is_robot(self):
        return (self.misc_attributes >> 4) == 3

    @property
    def is_monster(self):
        return (self.misc_attributes >> 4) == 2

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
        if 10 <= self.old_data['price'] <= 65535:
            return self.old_data['price']
        uses = UsesObject.get(self.index).old_data['uses']
        if 1 <= uses <= 99:
            return 999999
        return -1


class ShopObject(TableObject):
    def __repr__(self):
        s = 'SHOP {0:0>2X}\n'.format(self.index)
        for i in self.items:
            if i < 0xFF:
                ipo = ItemPriceObject.get(i)
                s += '  {0}\n'.format(ipo.name)
            else:
                s += '  --\n'
        return s.strip()


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

        for m in MonsterObject.ranked:
            print(m)
            print()

        for ip in ItemPriceObject.every:
            print(ip)

        for s in ShopObject.every:
            print(s)
            print()

        for a in AttributeObject.every:
            if a.is_buyable and a.is_equipped_on_monster:
                print(a)

        for m in MonsterObject.every:
            print(m)
            print()
        '''

        clean_and_write(ALL_OBJECTS)

        finish_interface()

    except Exception:
        print_exc()
        print('ERROR:', exc_info()[1])
        input('Press Enter to close this program. ')
