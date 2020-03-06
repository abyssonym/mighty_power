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
from sys import argv


VERSION = 1

assigned_pointers = {}


class ChestObject(TableObject):
    @property
    def name(self):
        return AttributeNameObject.get(self.contents).name

    @property
    def contents(self):
        return self.contents_lowbyte | ((self.misc - 0xf9) << 8)

    @property
    def intershuffle_valid(self):
        return self.contents < 0xff


class MonsterMeatObject(TableObject): pass
class RobotStatObject(TableObject): pass
class MonsterLevelObject(TableObject): pass
class UsesObject(TableObject): pass
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


class FormationCountObject(TableObject):
    @property
    def name(self):
        s = '/'.join(['%s-%s' % (c >> 4, c & 0xf) for c in self.counts])
        return s


class MonsterObject(TableObject):
    def __repr__(self):
        s = self.name
        s += '\n{0:>5} {1:>3} {2:>3} {3:>3} {4:>3}'.format(
                self.hp, self.strength, self.defense, self.agility, self.mana)
        for ai in self.attribute_indexes:
            s += '\n- {0}'.format(AttributeNameObject.get(ai).name)
        return s.strip()

    def read_data(self, filename, pointer=None):
        super(MonsterObject, self).read_data(filename, pointer)
        f = open(filename, 'r+b')
        f.seek(self.attacks_pointer | 0x30000)
        self.attribute_indexes = []
        for i in xrange(self.num_attributes):
            self.attribute_indexes.append(ord(f.read(1)))
        f.close()

    @property
    def num_attributes(self):
        num_attributes = (self.misc_attributes & 0xf) + 1
        assert 1 <= num_attributes <= 8
        return num_attributes

    @cached_property
    def name(self):
        return MonsterNameObject.get(self.index).name

    @property
    def sprite_index(self):
        if self.index >= 0xe1:
            return self.index
        return self.index / 5


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
            if 0xd4 <= ord(c) < 0xd4 + 26:
                s += chr(ord('a') + ord(c) - 0xd4)
            elif 0xb0 <= ord(c) < 0xb0 + 10:
                s += '0123456789'[ord(c) - 0xb0]
            elif 0xba <= ord(c) < 0xba + 26:
                s += chr(ord('A') + ord(c) - 0xba)
            elif ord(c) in codemap:
                s += codemap[ord(c)]
            else:
                s += '<{0:0>2x}>'.format(ord(c))
        return s


class AttributeNameObject(NameMixin): pass
class MonsterNameObject(NameMixin): pass


class ItemPriceObject(TableObject):
    @property
    def name(self):
        return '{0:<11}: {1:>5}'.format(
            AttributeNameObject.get(self.index).name, self.price)


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

        for m in MonsterObject.every:
            print hex(m.index), hex(m.pointer),
            print m
            print
            #print hex(m.attacks_pointer)

        for c in ChestObject.every:
            print c

        for ano in AttributeNameObject.every:
            print ano

        #for i in ItemPriceObject.every:
        #    print i

        for f in FormationObject.every:
            print f

        clean_and_write(ALL_OBJECTS)

        finish_interface()

    except IOError, e:
        print 'ERROR: %s' % e
        raw_input('Press Enter to close this program. ')
