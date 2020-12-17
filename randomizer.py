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
ALL_OBJECTS = None


class VanillaObject(TableObject):
    flag = 'v'
    flag_description = 'nothing'


class ChestObject(TableObject):
    flag = 't'
    flag_description = 'treasure chests'
    custom_random_enable = 't'

    banned_item_indexes = [0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d]

    @property
    def name(self):
        return self.item.name

    @property
    def item(self):
        return AttributeObject.get(self.contents)

    @cached_property
    def rank(self):
        if not self.intershuffle_valid:
            return -1
        return self.item.rank

    @property
    def contents(self):
        return self.contents_lowbyte | ((self.misc - 0xf9) << 8)

    @classproperty
    def valid_items(cls):
        if hasattr(ChestObject, '_valid_items'):
            return ChestObject._valid_items

        ChestObject._valid_items = [
            a for a in AttributeObject.every if a.index <= 0x7f
            and a.index not in ChestObject.banned_item_indexes
            and not a.get_bit('fixed')]

        return ChestObject.valid_items

    def set_contents(self, index):
        self.contents_lowbyte = index & 0xff
        self.misc = 0xf9 + (index >> 8)

    @property
    def intershuffle_valid(self):
        return self.item in self.valid_items

    def mutate(self):
        if not self.intershuffle_valid:
            return

        old_item = self.item
        new_item = self.item.get_similar(
            candidates=self.valid_items, random_degree=self.random_degree)
        self.set_contents(new_item.index)
        new_item = self.item

    def cleanup(self):
        if self.contents_lowbyte != self.old_data['contents_lowbyte']:
            assert self.intershuffle_valid


class MoveSelectionObject(TableObject):
    @property
    def num_moves(self):
        assert self.probabilities == sorted(self.probabilities)
        return self.probabilities.index(0xFF) + 1


class AttributeObject(TableObject):
    flag = 'i'
    custom_random_enable = 'i'

    @property
    def name(self):
        return AttributeNameObject.get(self.index).name

    @property
    def use_power_rank(self):
        if 0 <= self.index <= 0x7f and not self.get_bit('fixed'):
            return False
        return True

    @property
    def rank(self):
        if not self.use_power_rank:
            if self.index in ChestObject.banned_item_indexes:
                return -1
            if self.is_buyable:
                return ItemPriceObject.get(self.index).rank
            rank = 9999999 + (ItemPriceObject.get(self.index).rank / 100000)
            if self.power_rank >= 0:
                rank += self.power_rank - 50
            return rank
        elif self.index <= 0xff:
            return self.power_rank
        else:
            return -1

    @property
    def power_rank(self):
        if hasattr(AttributeObject, '_cached_ranks'):
            if self.index not in AttributeObject._cached_ranks:
                return -1
            return AttributeObject._cached_ranks[self.index]

        AttributeObject._cached_ranks = {}
        attribute_monster_ranks = defaultdict(list)
        for m in MonsterObject.every:
            if not m.intershuffle_valid:
                continue
            for i in m.old_data['attribute_indexes']:
                attribute_monster_ranks[i].append(m.rank)

        for i, ranks in attribute_monster_ranks.items():
            avg = sum(ranks) / len(ranks)
            AttributeObject._cached_ranks[i] = avg

        return self.power_rank

    def get_similar(self, candidates=None, override_outsider=False,
                    random_degree=None, allow_intershuffle_invalid=False):
        if candidates is not None:
            candidates = [c for c in candidates
                          if c.use_power_rank == self.use_power_rank]
            if not candidates:
                return self
        return super(AttributeObject, self).get_similar(
            candidates=candidates, override_outsider=override_outsider,
            random_degree=random_degree,
            allow_intershuffle_invalid=allow_intershuffle_invalid)

    @property
    def shop_item_class(self):
        if self.is_weapon:
            weapon_type = \
                RobotStatObject.get(self.index).old_data['misc_value'] >> 4
        else:
            weapon_type = None
        return (self.is_weapon, self.is_armor or self.is_shield, weapon_type)

    @property
    def is_weapon(self):
        return (self.get_bit('use_battle') and self.get_bit('target_enemy')
                and not self.get_bit('use_field'))

    @property
    def is_armor(self):
        return bool(self.property_flags & 0xf)

    @property
    def is_shield(self):
        return (self.get_bit('use_battle') and self.get_bit('no_target')
                and not self.get_bit('target_enemy'))

    @cached_property
    def is_buyable(self):
        if self.index >= 0xFF:
            return False

        for s in ShopObject.every:
            if self.index in s.old_data['item_indexes']:
                return True

        return False

    @cached_property
    def is_equipped_on_monster(self):
        for m in MonsterObject.every:
            if self.index in m.old_data['attribute_indexes']:
                return True

        return False

    def mutate(self):
        if self.get_bit('fixed'):
            return

        candidates = None
        if self.is_armor and self.multiplier_element <= 0x1f:
            candidates = [
                a for a in AttributeObject.every if a.is_armor
                and a.multiplier_element <= 0x1f
                and a.property_flags & 0xf == self.property_flags & 0xf]
            max_power = 0x1f
        elif self.is_weapon and 6 <= self.multiplier_element <= 0xf:
            candidates = [
                a for a in AttributeObject.every if a.is_weapon
                and 6 <= a.multiplier_element <= 0xf
                and a.shop_item_class == self.shop_item_class]
            max_power = 0xf

        if candidates and len(candidates) > 1:
            other = self.get_similar(candidates)
            power = other.multiplier_element & max_power
            self.multiplier_element &= (0xFF ^ max_power)
            self.multiplier_element |= power

    def cleanup(self):
        # weapons that hit specific races for critical damage
        if self.is_weapon and self.effect in [0xC, 0xD, 0x1C]:
            race = self.misc_hits
            # fix coral sword bug
            if race == 0x30 and self.index == 6:
                race = 0x40

            monsters = [m for m in MonsterObject.every
                        if m.meat.old_data['meat'] & 0xF0 == race]
            new_meat_codes = {m.meat.meat & 0xF0 for m in monsters}
            if len(new_meat_codes) == 1:
                self.misc_hits = list(new_meat_codes)[0]


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
            if (mmo.meat in meat_map
                    and MonsterObject.get(mmo.index).is_monster):
                mmo.meat = meat_map[mmo.meat]


class MonsterEvolutionObject(TableObject):
    def validate(self):
        assert len(set(self.monster_indexes)) == 5
        assert len(self.monster_indexes) == 16
        assert self.monster_indexes == sorted(self.monster_indexes)
        assert max(self.monster_indexes) - min(self.monster_indexes) == 4

    def preclean(self):
        # correcting (possible) errors in the original rom
        # basically changing it to use one canonical version of each monster
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


class RobotStatObject(TableObject):
    flag = 'i'
    flag_description = 'item and equipment stats'
    custom_random_enable = 'i'

    @property
    def intershuffle_valid(self):
        return ((self.old_data['misc_value'] & 0xD0)
                and not AttributeObject.get(self.index).get_bit('fixed'))

    @property
    def power(self):
        return self.misc_value & 0xf

    @property
    def boost_statuses(self):
        return self.misc_value >> 4

    def randomize(self):
        if not self.intershuffle_valid:
            return

        other = self.get_similar()
        power = mutate_normal(other.power, minimum=0, maximum=0xf,
                              wide=True)
        if random.random() < (self.random_degree / 2):
            power = int(round(power * 2 / 3))
            count_statuses = bin(self.boost_statuses)
            while bin(self.boost_statuses).count('1') == count_statuses:
                new_status = random.choice([0x10, 0x40, 0x80])
                self.misc_value |= new_status


class MonsterLevelObject(TableObject):
    flag = 'm'
    custom_random_enable = 'm'

    @property
    def move_selection_index(self):
        return self.moves_level >> 4

    def set_move_selection_index(self, index):
        assert index == index & 0xf
        self.moves_level &= 0xf
        self.moves_level |= (index << 4)
        assert index == self.move_selection_index

    @property
    def level(self):
        return self.moves_level & 0xF

    def set_level(self, level):
        assert level == level & 0xf
        assert 1 <= level <= 0xb
        self.moves_level &= 0xf0
        self.moves_level |= level
        assert self.level == level

    @cached_property
    def rank(self):
        return self.level

    @classmethod
    def randomize_all(cls):
        meats = {m.meat.old_data['meat'] for m in MonsterObject.every}
        for meat in sorted(meats):
            monsters = [m for m in MonsterObject.every
                        if m.meat.old_data['meat'] == meat
                        and m.index <= MonsterObject.MAX_EVOLVE_INDEX]
            if not monsters:
                assert meat >= 0xc0
                continue
            assert len(monsters) == 5
            assert monsters[-1].level == 0xb
            assert monsters == sorted(monsters, key=lambda m: m.level)
            new_levels = set([])
            for m in monsters[:4]:
                new_level = mutate_normal(
                    m.level, minimum=1, maximum=0xa, wide=True,
                    random_degree=MonsterLevelObject.random_degree)
                new_levels.add(new_level)

            while len(new_levels) < 4:
                new_levels.add(random.randint(1, 0xa))
            new_levels = sorted(new_levels)

            for level, monster in zip(new_levels, monsters):
                assert 1 <= level <= 0xa
                MonsterLevelObject.get(monster.index).set_level(level)

        super(MonsterLevelObject, cls).randomize_all()


class UsesObject(TableObject):
    flag = 'i'
    custom_random_enable = 'i'

    mutate_attributes = {'uses': (1, 99)}

    @cached_property
    def rank(self):
        return self.uses

    @property
    def intershuffle_valid(self):
        return self.uses <= 99

    def cleanup(self):
        if 11 <= self.uses <= 98:
            self.uses = round(self.uses*2, -1) // 2


class StatGrowthObject(TableObject): pass


class MutantSkillsObject(TableObject):
    flag = 'u'
    flag_description = 'mutant skills'
    custom_random_enable = 'u'

    @property
    def name(self):
        a = AttributeObject.get(self.skill_index)
        return '{0:0>2X} {1:0>2X} {2}'.format(self.index, a.index, a.name)

    @classmethod
    def randomize_all(cls):
        attributes = [AttributeObject.get(m.skill_index)
                      for m in MutantSkillsObject.every]
        new_attributes = []
        for old_attribute in attributes:
            candidates = [a for a in AttributeObject.every
                          if a.get_bit('fixed') and a.rank >= 0
                          and a not in new_attributes]
            if old_attribute not in candidates:
                if old_attribute.get_bit('fixed'):
                    # vanilla doesn't have non-fixed attributes
                    # this is for romhack compatibility
                    assert old_attribute in new_attributes

            template = random.choice(attributes)
            temp = [c for c in candidates if
                    c.get_bit('use_battle') == template.get_bit('use_battle')]
            if temp:
                candidates = temp

            new_attribute = old_attribute.get_similar(
                candidates, random_degree=MutantSkillsObject.random_degree,
                override_outsider=True)
            new_attributes.append(new_attribute)

        assert len(new_attributes) == len(MutantSkillsObject.every)
        for new, mu in zip(new_attributes, MutantSkillsObject.every):
            mu.skill_index = new.index

        super(MutantSkillsObject, cls).randomize_all()


class MonsterGraphicObject(TableObject): pass


class FormationObject(TableObject):
    flag = 'f'
    flag_description = 'enemy formations'
    custom_random_enable = 'f'

    @classproperty
    def after_order(cls):
        return [FormationCountObject]

    @property
    def name(self):
        s = ','.join(MonsterNameObject.get(i).name for i in self.enemy_indexes)
        s += ' | {0} . {1}'.format(
            FormationCountObject.get(self.counts[0] & 0x1f).name,
            FormationCountObject.get(self.counts[1] & 0x1f).name)
        return s

    @property
    def monsters(self):
        return [MonsterObject.get(i) for i in self.enemy_indexes]

    @property
    def fcounts(self):
        return (FormationCountObject.get(self.counts[0] & 0x1f),
                FormationCountObject.get(self.counts[1] & 0x1f))

    @cached_property
    def rank(self):
        rank = 0
        for fcount in self.fcounts:
            for count, enemy_index in zip(fcount.counts, self.enemy_indexes):
                rank += (count * MonsterObject.get(enemy_index).rank)
        return rank

    def randomize_counts(self):
        if self.index <= 0xf:
            # boss formation
            enumerated_fcounts = list(enumerate(self.fcounts))
            random.shuffle(enumerated_fcounts)
            aas = [self.enemy_indexes[2] == 0 and self.index > 0, False]
            for ((i, fcount), aa) in zip(enumerated_fcounts, aas):
                counts = fcount.old_data['counts']
                candidates = [f for f in FormationCountObject.every
                              if f.validate_boss(counts, allow_add=aa)]
                if not candidates:
                    chosen = fcount
                else:
                    chosen = random.choice(candidates)
                self.counts[i] = chosen.index
                if aa:
                    old_monsters = [self.monsters[j]
                                    for (j, c) in enumerate(counts) if c > 0]
                    avg_rank = (sum([m.rank for m in old_monsters])
                                / len(old_monsters))
                    avg_hp = (sum([m.hp for m in old_monsters])
                              / len(old_monsters))
                    candidates = [m for m in MonsterObject.ranked
                                  if m.intershuffle_valid
                                  and m.rank < avg_rank
                                  and m.hp < avg_hp]

                    max_index = len(candidates) - 1
                    randval = random.random()
                    randomness = (1-self.random_degree)
                    if randomness > 0:
                        randval = randval ** (1 / randomness)
                    else:
                        randval = 0
                    index = int(round((1-randval) * max_index))
                    chosen = candidates[index]
                    self.enemy_indexes[2] = chosen.index

            return

        for (i, fcount) in enumerate(self.fcounts):
            counts = fcount.old_data['counts']
            candidates = sorted(
                FormationCountObject.every,
                key=lambda fc: (fc.get_distance(counts), fc.signature))
            max_index = len(candidates) - 1
            randval = random.random()
            if self.random_degree > 0:
                randval = randval ** (1 / self.random_degree)
            else:
                randval = 0
            assert 0 <= randval <= 1
            index = int(round(randval * max_index))
            chosen = candidates[index]
            self.counts[i] = chosen.index
            assert self.fcounts[i] is chosen

    def randomize_monsters(self):
        if self.index <= 0xf:
            return

        done_m = []
        for (i, m) in enumerate(self.monsters):
            while True:
                new_m = m.get_similar(random_degree=self.random_degree)
                if new_m not in done_m:
                    break
            done_m.append(new_m)
            self.enemy_indexes[i] = new_m.index
            assert self.monsters[i] is new_m

    def randomize(self):
        self.randomize_counts()
        self.randomize_monsters()
        super(FormationObject, self).randomize()


class FormationCountObject(TableObject):
    flag = 'f'
    custom_random_enable = 'f'

    @property
    def name(self):
        s = '/'.join(['%s-%s' % (c >> 4, c & 0xf) for c in self.counts])
        return s

    @cached_property
    def rank(self):
        return sum([c >> 4 for c in self.counts] +
                   [c & 0xf for c in self.counts])

    def get_distance(self, other):
        if isinstance(other, FormationCountObject):
            other = other.counts

        sqs1 = [((a & 0xf) - (b & 0xf))**2
                for (a, b) in zip(self.counts, other)]
        sqs2 = [((a >> 4) - (b >> 4))**2 for (a, b) in zip(self.counts, other)]
        return sum(sqs1 + sqs2) ** 0.5

    def validate_boss(self, other, allow_add=True):
        if isinstance(other, FormationCountObject):
            other = other.counts

        for (i, (a, b)) in enumerate(zip(self.counts, other)):
            if (b >> 4) == (b & 0xf) and b != a and (
                    b > 0 or i < 2 or not allow_add):
                return False
            if b and not a:
                return False

        return True

    def randomize(self):
        super(FormationCountObject, self).randomize()
        if 0x11 in self.counts[:2]:
            return

        if not (hasattr(FormationCountObject, 'left_boss_add') and
                hasattr(FormationCountObject, 'right_boss_add')):
            new_count = 0
            while new_count < 0x10:
                new_count = random.choice(random.choice(
                    FormationCountObject.every).old_data['counts'])

            if not hasattr(FormationCountObject, 'left_boss_add'):
                self.counts = [0x11, 0, new_count]
                FormationCountObject.left_boss_add = self
                return

            if not hasattr(FormationCountObject, 'right_boss_add'):
                self.counts = [0, 0x11, new_count]
                FormationCountObject.right_boss_add = self
                return

        while True:
            self.counts = [
                random.choice(random.choice(
                    FormationCountObject.every).old_data['counts'])
                for _ in range(3)]

            for f in FormationCountObject.every:
                if (hasattr(f, 'randomized') and f.randomized
                        and self.counts == f.counts):
                    self.counts = []
                    break

            if not any([c >= 0x10 for c in self.counts]):
                continue

            break

    def mutate(self):
        for (i, c) in enumerate(self.counts):
            subcounts = (c >> 4, c & 0xf)
            final_counts = []
            for sc in subcounts:
                if sc >= 2:
                    sc = mutate_normal(sc, 1, 9, wide=True,
                                       random_degree=self.random_degree)
                final_counts.append(sc)
            low, high = sorted(final_counts)
            self.counts[i] = (low << 4) | high


class MonsterSkillObject(TableObject):
    flag = 'k'
    flag_description = 'monster skills and attributes'
    custom_random_enable = 'k'

    def randomize(self):
        MonsterObject.get(self.index).randomize_skills_and_attributes()
        super(MonsterSkillObject, self).randomize()


class MonsterObject(TableObject):
    flag = 'm'
    flag_description = 'monster and enemy stats'
    custom_random_enable = 'm'

    randomselect_attributes = ['strength', 'agility', 'defense']
    mutate_attributes = {'hp': (1, 10000),
                         'strength': None,
                         'agility': None,
                         'mana': None,
                         'defense': None}

    banned_monster_indexes = [0xF4, 0xFE, 0xFF]

    MAX_EVOLVE_INDEX = 0xB3

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
    def intershuffle_valid(self):
        if self.index in MonsterObject.banned_monster_indexes:
            return False
        return (self.graphic != 0
                or self.index <= MonsterObject.MAX_EVOLVE_INDEX)

    @property
    def meat(self):
        return MonsterMeatObject.get(self.index)

    @property
    def family_key(self):
        key = self.meat.old_data['meat']
        if key == 0 and self.index > MonsterObject.MAX_EVOLVE_INDEX:
            return 0xFFFF
        return key

    @cached_property
    def family(self):
        candidates = [m for m in MonsterObject.every
                      if self.is_human == m.is_human
                      and self.is_robot == m.is_robot
                      and self.is_monster == m.is_monster]
        if self.is_monster:
            return [m for m in candidates
                    if m.meat.old_data['meat'] == self.meat.old_data['meat']]
        else:
            return candidates

    @cached_property
    def extended_family(self):
        candidates = [m for m in MonsterObject.every
                      if self.is_human == m.is_human
                      and self.is_robot == m.is_robot
                      and self.is_monster == m.is_monster]
        if self.is_monster:
            return [m for m in candidates
                    if (m.meat.old_data['meat'] & 0xf0)
                    == (self.meat.old_data['meat'] & 0xf0)]
        else:
            return candidates

    @property
    def family_attributes(self):
        if not hasattr(MonsterObject, '_famattr'):
            MonsterObject._famattr = defaultdict(set)
        if self.family_key in MonsterObject._famattr:
            return MonsterObject._famattr[self.family_key]

        for m in MonsterObject.every:
            attributes = [AttributeObject.get(i)
                          for i in m.old_data['attribute_indexes']]
            attributes = [a for a in attributes if a.rank >= 0]
            MonsterObject._famattr[m.family_key] |= set(attributes)

        return self.family_attributes

    @property
    def extended_family_attributes(self):
        if not hasattr(MonsterObject, '_exfamattr'):
            MonsterObject._exfamattr = defaultdict(set)
        if self.family_key >> 4 in MonsterObject._exfamattr:
            return MonsterObject._exfamattr[self.family_key >> 4]

        for m in MonsterObject.every:
            attributes = [AttributeObject.get(i)
                          for i in m.old_data['attribute_indexes']]
            attributes = [a for a in attributes if a.rank >= 0]
            MonsterObject._exfamattr[m.family_key >> 4] |= set(attributes)

        return self.extended_family_attributes

    @property
    def new_family_attributes(self):
        self.family_attributes, self.extended_family_attributes
        if not hasattr(MonsterObject, '_newfamattr'):
            MonsterObject._newfamattr = {}

        if self.family_key in MonsterObject._newfamattr:
            return MonsterObject._newfamattr[self.family_key]

        if self.family_key >= 0xc0:
            MonsterObject._newfamattr[self.family_key] = \
                MonsterObject._famattr[self.family_key]
            return self.new_family_attributes

        num_attributes = len(self.family_attributes)
        min_attributes = 8
        max_attributes = max(
            len(v) for (k, v) in MonsterObject._famattr.items()
            if (k >> 4) <= 0xb)
        num_attributes = mutate_normal(
            num_attributes, minimum=min_attributes, maximum=max_attributes,
            random_degree=self.random_degree, wide=True)

        new_attributes = []
        while len(new_attributes) < num_attributes:
            old_attribute = random.choice(sorted(self.family_attributes))
            if random.random() > self.random_degree:
                # family attributes
                candidates = sorted(self.family_attributes)
            elif random.random() > self.random_degree:
                # extended family attributes
                candidates = sorted(self.extended_family_attributes)
            else:
                # any attributes
                candidates = {a for i in MonsterObject._exfamattr
                              for a in MonsterObject._exfamattr[i] if i < 0xc}
                candidates = sorted(candidates)

            if len(new_attributes) == 0:
                candidates = [c for c in candidates if c.get_bit('use_battle')]

            new_attribute = old_attribute.get_similar(
                candidates=candidates, random_degree=self.random_degree,
                override_outsider=True)
            if new_attribute not in new_attributes:
                new_attributes.append(new_attribute)

        assert any([a.get_bit('use_battle') for a in new_attributes])
        MonsterObject._newfamattr[self.family_key] = sorted(new_attributes)
        return self.new_family_attributes

    @property
    def graphic(self):
        return MonsterGraphicObject.get(self.index).graphic_index

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

    def randomize_skills_and_attributes(self):
        if self.index in MonsterObject.banned_monster_indexes:
            return

        old_attributes = [AttributeObject.get(i)
                          for i in self.attribute_indexes]
        new_attributes = [o for o in old_attributes if o.rank < 0
                          and o.index != 0xFF]
        old_attributes = [o for o in old_attributes if o.rank >= 0]
        num_attributes = len({a for a in new_attributes + old_attributes})
        num_attributes = mutate_normal(num_attributes, minimum=1, maximum=8,
                                       random_degree=self.random_degree,
                                       wide=True)

        if not old_attributes:
            return

        while len(new_attributes) < num_attributes:
            if len([a for a in new_attributes
                    if a.get_bit('use_battle')]) == 0:
                candidates = [a for a in self.new_family_attributes
                              if a.get_bit('use_battle')]
            elif len([a for a in new_attributes
                      if a.get_bit('use_battle')]) == 7:
                candidates = [a for a in self.new_family_attributes
                              if not a.get_bit('use_battle')]
            else:
                candidates = self.new_family_attributes
            candidates = [c for c in candidates
                          if c not in new_attributes]
            old_attribute = random.choice(old_attributes)
            if not candidates:
                if (old_attribute in new_attributes
                        and len(new_attributes) >= self.num_attributes):
                    break
                new_attribute = old_attribute
            else:
                new_attribute = old_attribute.get_similar(
                    candidates, random_degree=self.random_degree,
                    override_outsider=True)

            if new_attribute not in new_attributes:
                new_attributes.append(new_attribute)

        if not new_attributes:
            return

        use_battle = [a for a in new_attributes if a.get_bit('use_battle')]
        if len(use_battle) >= 8:
            use_battle = use_battle[:7]
        random.shuffle(use_battle)
        no_use = [a for a in new_attributes if not a.get_bit('use_battle')]
        no_use = sorted(no_use)

        candidates = [m for m in MoveSelectionObject.every
                      if m.num_moves == len(use_battle)]
        assert 1 <= len(use_battle) <= 7
        chosen = random.choice(candidates)
        MonsterLevelObject.get(self.index).set_move_selection_index(
            chosen.index)

        self.attribute_indexes = [a.index for a in use_battle + no_use]

    def cleanup(self):
        self.set_num_attributes()
        if self.index <= MonsterObject.MAX_EVOLVE_INDEX:
            self.hp = min(self.hp, 999)

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
        return self.decode(self.name_str)

    @classmethod
    def decode(cls, to_decode):
        s = ''
        for c in to_decode:
            if c in cls.codemap:
                s += cls.codemap[c]
            else:
                s += '<{0:0>2x}>'.format(c)
        return s

    @classmethod
    def encode(cls, to_encode):
        return bytes([NameMixin.codemap[s] for s in to_encode])

    @classproperty
    def codemap(cls):
        if hasattr(NameMixin, '_codemap'):
            return NameMixin._codemap

        codemap = {
            0xee: "'",
            0xf0: '.',
            0xf2: '-',
            0xff: ' ',
        }

        for c in range(0xd4, 0xd4 + 26):
            s = chr(ord('a') + c - 0xd4)
            codemap[c] = s

        for c in range(0xb0, 0xb0 + 10):
            s = '0123456789'[c - 0xb0]
            codemap[c] = s

        for c in range(0xba, 0xba + 26):
            s = chr(ord('A') + c - 0xba)
            codemap[c] = s

        for k, v in list(codemap.items()):
            assert v not in codemap
            codemap[v] = k

        NameMixin._codemap = codemap
        return cls.codemap


class AttributeNameObject(NameMixin): pass
class MonsterNameObject(NameMixin): pass


class ItemPriceObject(TableObject):
    flag = 's'
    custom_random_enable = 's'

    mutate_attributes = {'price': (0, 60000)}

    @classproperty
    def after_order(cls):
        return [ShopObject]

    @property
    def name(self):
        return '{0:<11}: {1:>5}'.format(
            AttributeNameObject.get(self.index).name, self.price)

    @cached_property
    def rank(self):
        if self.index in ChestObject.banned_item_indexes:
            return -1

        if 10 <= self.old_data['price'] <= 65535:
            return self.old_data['price']

        return 999999

    def cleanup(self):
        price = self.price * 2
        magnitude = 0
        while price >= 100:
            price /= 10
            magnitude += 1
        price = int(round(price))
        while magnitude > 0:
            price *= 10
            magnitude -= 1
        self.price = int(round(price)) // 2


class ShopObject(TableObject):
    flag = 's'
    flag_description = 'shops'
    custom_random_enable = 's'

    def __repr__(self):
        s = 'SHOP {0:0>2X}\n'.format(self.index)
        for i in self.item_indexes:
            if i < 0xFF:
                ipo = ItemPriceObject.get(i)
                s += '  {0}\n'.format(ipo.name)
            else:
                s += '  --\n'
        return s.strip()

    @property
    def items(self):
        return [AttributeObject.get(i) for i in self.item_indexes if i < 0xFF]

    def randomize(self):
        num_items = len(self.items)
        num_items = mutate_normal(num_items, minimum=1, maximum=8,
                                  random_degree=self.random_degree,
                                  wide=True)
        old_items = list(self.items)
        new_items = []
        for _ in range(500):
            if len(new_items) == num_items:
                break
            buyable_check = not (random.random() < self.random_degree)
            chosen_class = random.choice(old_items).shop_item_class
            chosen_price = random.choice(old_items)
            candidates = [a for a in AttributeObject.every
                          if a.index <= 0x7f and a.rank >= 0
                          and a.shop_item_class == chosen_class
                          and a.is_buyable >= buyable_check]
            candidates = [c for c in candidates if c not in new_items]
            if not candidates:
                continue
            chosen = chosen_price.get_similar(
                    candidates=candidates, random_degree=self.random_degree,
                    override_outsider=True)
            new_items.append(chosen)
        else:
            raise Exception('Unable to populate shop.')

        for i in new_items:
            if not i.is_buyable:
                ItemPriceObject.get(i.index).price = 60000

        self.item_indexes = [i.index for i in new_items]

    def cleanup(self):
        items = sorted(
            self.items, key=lambda i: (ItemPriceObject.get(i.index).price,
                                       i.index))
        self.item_indexes = [i.index for i in items]
        while len(self.item_indexes) < 8:
            self.item_indexes.append(0xFF)


def rewrite_title_screen():
    title_len_1, title_len_2 = 17, 20
    s1 = 'v{0} SN {1}'.format(VERSION, get_seed())

    if any(hasattr(o, 'custom_random_degree') for o in ALL_OBJECTS):
        random_degree = 'CUSTOM'
    else:
        random_degree = round(get_random_degree() ** 0.5, 2)
    s2 = '{0} {1}'.format(random_degree, get_flags())

    s1 = s1.strip()
    s2 = s2.strip()
    assert len(s1) <= title_len_1
    assert len(s2) <= title_len_2
    while len(s1) < title_len_1:
        s1 = ' {0} '.format(s1)
    s1 = s1[:title_len_1]
    while len(s2) < title_len_2:
        s2 = ' {0} '.format(s2)
    s2 = s2[:title_len_2]
    assert len(s1) == title_len_1
    assert len(s2) == title_len_2

    f = open(get_outfile(), 'r+b')
    f.seek(addresses.title_text_1)
    f.write(NameMixin.encode(s1))
    f.seek(addresses.title_text_2)
    f.write(NameMixin.encode(s2))
    f.close()


if __name__ == '__main__':
    try:
        print ('You are using the Final Fantasy Legend II '
               '"Mighty Power" randomizer version %s.' % VERSION)
        print

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]

        codes = {
                 }

        run_interface(ALL_OBJECTS, snes=False, codes=codes,
                      custom_degree=True)

        clean_and_write(ALL_OBJECTS)

        if get_global_label() == 'FFL2_NA':
            rewrite_title_screen()

        finish_interface()

    except Exception:
        print_exc()
        print('ERROR:', exc_info()[1])
        input('Press Enter to close this program. ')
