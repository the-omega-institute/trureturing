#!/usr/bin/env python3
"""Replay a finite contradiction for mixed-prime common-center relocations.

Only three explicit inputs and the explicit output are accessed. All parent,
child, CRT and rescue data are reconstructed with exact integer arithmetic.
No solver, stored case tree, floating arithmetic or runtime limit is used.
Successful output means the necessary-condition tree closed in every branch;
a surviving necessary-condition model or a node-limit hit raises an error.
"""

import argparse
from collections import Counter
import hashlib
import json
from math import gcd, isqrt, lcm
from pathlib import Path


ORIGINALS_SHA256 = '427138d17d61f284dff84c2143b90b3b5b3997af6c26e9a8c17f4ab790aa1e11'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def prime_factors(value):
    answer = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            answer.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        answer.append(value)
    return answer


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def evaluate(originals, blockers, joint_data, max_nodes):
    require(blockers['input_sha256'] == ORIGINALS_SHA256,
            'private witnesses refer to different originals')
    require(joint_data['input_sha256'] == ORIGINALS_SHA256,
            'joint points refer to different originals')
    rows = originals['originals']
    require(len(rows) == 463, 'expected 463 originals')
    require(all(type(row[key]) is int for row in rows
                for key in ('modulus', 'residue', 'private_point')),
            'noninteger original data')
    classes = {row['modulus']: row['residue'] for row in rows}
    require(len(classes) == len(rows), 'duplicate numerical modulus')
    require(all(m > 1 and m % 2 == 1 and 0 <= a < m
                for m, a in classes.items()), 'invalid original odd AP')
    period = lcm(*classes)
    primes = prime_factors(period)
    require(period == 481225870125, 'unexpected period')
    require(primes == [3, 5, 7, 11, 13, 17, 19], 'unexpected prime support')
    require(all(classes.get(p) == 0 for p in primes), 'prime normalization fails')
    divisor_checks = 0
    for m in classes:
        for divisor in range(2, isqrt(m) + 1):
            if m % divisor == 0:
                require(divisor in classes and m // divisor in classes,
                        'nonunit divisor missing')
                divisor_checks += 1
    require(all(originals['hole'] % m != a for m, a in classes.items()),
            'original hole is covered')

    witnesses = {row['modulus']: [row['private_point']] for row in rows}
    require(len(blockers['rows']) == 395, 'expected 395 extra private points')
    for row in blockers['rows']:
        require(set(row) == {'modulus', 'private_point'} and
                all(type(value) is int for value in row.values()),
                'invalid private-point row')
        m, point = row['modulus'], row['private_point']
        require(m in witnesses and point not in witnesses[m],
                'duplicate or unknown private-point row')
        witnesses[m].append(point)
    private_count = 0
    for m, points in witnesses.items():
        for point in points:
            require(0 <= point < period, 'private point outside period')
            require([d for d, a in classes.items() if point % d == a] == [m],
                    'claimed private point has different original owners')
            private_count += 1

    # Parent-first reconstruction: every original d = m*p^e with p not | m.
    # Equal (m,c) options merge across primes; all original child records remain.
    groups = {}
    maximum = max(classes)
    for m, a in sorted(classes.items()):
        for p in primes:
            if m % p == 0:
                continue
            e, child = 1, m * p
            while child <= maximum:
                if child in classes:
                    center = classes[child] % m
                    require(center != a, 'old parent contains original child')
                    groups.setdefault((m, center), []).append((p, child, e))
                e, child = e + 1, child * p
    options = [(m, c, tuple(sorted(children)))
               for (m, c), children in sorted(groups.items())]
    count = len(options)
    universe = (1 << count) - 1
    parents = sorted({m for m, _, _ in options})
    parent_masks = {m: sum(1 << i for i, (n, _, _) in enumerate(options) if n == m)
                    for m in parents}
    compatible = []
    for i, (m, c, _) in enumerate(options):
        compatible.append(sum(1 << j for j, (n, d, _) in enumerate(options)
                              if (m != n or i == j) and (c - d) % gcd(m, n) == 0))
    requirements = {}
    for m in parents:
        requirements[m] = [sum(1 << i for i, (n, c, _) in enumerate(options)
                               if point % n == c) for point in witnesses[m]]
    joint = []
    joint_rows = []
    require(len(joint_data['points']) == 10, 'expected 10 joint points')
    seen_points = set()
    for row in joint_data['points']:
        point = row['point']
        require(type(point) is int and 0 <= point < period and point not in seen_points,
                'invalid or duplicate joint point')
        seen_points.add(point)
        owners = tuple(m for m, a in sorted(classes.items()) if point % m == a)
        require(list(owners) == row['owners'] and owners, 'wrong complete owner set')
        rescuers = sum(1 << i for i, (m, c, _) in enumerate(options) if point % m == c)
        require(rescuers.bit_count() == row['rescuer_options'], 'wrong rescuer count')
        joint.append((owners, rescuers))
        joint_rows.append({'point': point, 'owners': list(owners),
                           'rescuer_options': rescuers.bit_count()})

    # Regression: finite private tests alone allow this batch, but its actual
    # changed union loses a jointly owned point. This does not claim that all
    # private integers, rather than the supplied private tests, are rescued.
    regression = joint_data['private_only_regression']
    changes = {row['parent']: row['center'] for row in regression['selected']}
    require(len(changes) == len(regression['selected']) == 5,
            'regression must have five distinct parents')
    for row in regression['selected']:
        key = (row['parent'], row['center'])
        require(key in groups, 'regression center is not child-induced')
        require([list(item) for item in sorted(groups[key])] == row['children'],
                'wrong regression child records')
        require(regression['center'] % row['parent'] == row['center'],
                'regression centers have no stated common CRT point')
    retained_checks = 0
    for m, points in witnesses.items():
        for point in points:
            require(any(point % d == changes.get(d, a) for d, a in classes.items()),
                    'regression loses a supplied private point')
            retained_checks += 1
    lost = regression['lost_point']
    old_owners = [m for m, a in sorted(classes.items()) if lost % m == a]
    require(old_owners == regression['old_owners'] and len(old_owners) > 1,
            'regression loss does not have stated joint ownership')
    require(not any(lost % m == changes.get(m, a) for m, a in classes.items()),
            'regression loss is covered after simultaneous parent replacements')

    stats = Counter()

    def close(live, selected, forced):
        """Preserve A with selected <= A <= live and parents(A) >= forced.

        A is a nonempty CRT clique. A moved parent needs every private rescue;
        if all old owners of a joint point move, at least one new option must
        rescue that point. All deductions below are necessary conditions only.
        """
        stats['propagation_calls'] += 1
        forced = set(forced)
        while True:
            stats['propagation_rounds'] += 1
            previous = (live, selected, len(forced))
            if not live or selected & ~live:
                return None, 'forced-option-lost'
            for m in sorted(forced):
                choices = live & parent_masks[m]
                if not choices:
                    return None, 'forced-parent-empty'
                if choices & (choices - 1) == 0:
                    selected |= choices
            for i in indices(selected):
                live &= compatible[i]
                forced.add(options[i][0])
            if selected & ~live:
                return None, 'forced-options-incompatible'
            remove = 0
            for i in indices(live):
                m = options[i][0]
                local = live & compatible[i]
                if any(not (rescuers & local) for rescuers in requirements[m]):
                    remove |= 1 << i
                    continue
                if any(not (local & parent_masks[n]) for n in forced):
                    remove |= 1 << i
                    continue
                assumed = forced | {m}
                if any(all(n in assumed for n in owners) and not (rescuers & local)
                       for owners, rescuers in joint):
                    remove |= 1 << i
            live &= ~remove
            if not live or selected & ~live:
                return None, 'conditional-option-demand'
            obligations = [r for m in sorted(forced) for r in requirements[m]]
            for owners, rescuers in joint:
                if any(m not in parent_masks or not (live & parent_masks[m])
                       for m in owners):
                    continue  # An old owner is necessarily retained.
                unforced = [m for m in owners if m not in forced]
                if not unforced:
                    obligations.append(rescuers)
                elif not (rescuers & live) and len(unforced) == 1:
                    live &= ~parent_masks[unforced[0]]
            for rescuers in obligations:
                choices = live & rescuers
                if not choices:
                    return None, 'forced-rescue-empty'
                if choices & (choices - 1) == 0:
                    selected |= choices
                else:
                    pool = {options[i][0] for i in indices(choices)}
                    if len(pool) == 1:
                        forced.update(pool)
            if not live or selected & ~live:
                return None, 'joint-owner-ban'
            # forced only grows, so its size detects all forced-set changes.
            if previous == (live, selected, len(forced)):
                return (live, selected, forced), 'stable'

    priority = [5, 11, 3, 9, 13, 17, 7, 19]

    def search(live, selected, forced, depth=0):
        stats['nodes'] += 1
        stats['maximum_depth'] = max(stats['maximum_depth'], depth)
        require(stats['nodes'] <= max_nodes, 'case budget reached; no closed result')
        state, reason = close(live, selected, forced)
        if state is None:
            stats['conflict_leaves'] += 1
            stats['conflict:' + reason] += 1
            return
        live, selected, forced = state
        domains = [((live & parent_masks[m]).bit_count(), m) for m in forced
                   if not (selected & parent_masks[m])]
        if domains:
            _, m = min(domains)
            stats['parent_center_choice_nodes'] += 1
            for i in indices(live & parent_masks[m]):
                search(live & compatible[i], selected | (1 << i), forced | {m}, depth + 1)
            return
        for m in priority:
            if m not in forced and live & parent_masks[m]:
                stats['moved_unmoved_split_nodes'] += 1
                search(live, selected, forced | {m}, depth + 1)
                search(live & ~parent_masks[m], selected, forced, depth + 1)
                return
        if selected:
            okay = all(all(selected & r for r in requirements[m]) for m in forced)
            okay = okay and all(not all(m in forced for m in owners) or selected & r
                                 for owners, r in joint)
            require(not okay, 'necessary conditions admit selected options ' +
                    repr(list(indices(selected))) + '; this does not certify an exchange')
        residuals = [r & live for m in sorted(forced) for r in requirements[m]
                     if not (selected & r)]
        residuals += [r & live for owners, r in joint
                      if all(m in forced for m in owners) and not (selected & r)]
        if not residuals:
            residuals = [live]  # The hypothesized selected set is nonempty.
        choices = min(residuals, key=int.bit_count)
        require(choices != 0, 'empty rescue should have closed the branch')
        stats['rescuer_choice_nodes'] += 1
        for i in indices(choices):
            search(live & compatible[i], selected | (1 << i),
                   forced | {options[i][0]}, depth + 1)

    search(universe, 0, set())
    require(stats['nodes'] == stats['conflict_leaves'] +
            stats['parent_center_choice_nodes'] + stats['moved_unmoved_split_nodes'] +
            stats['rescuer_choice_nodes'], 'node accounting mismatch')
    return {
        'result': 'CLOSED_CASE_TREE',
        'period': period,
        'original_count': len(classes),
        'original_hole': originals['hole'],
        'divisor_pair_checks': divisor_checks,
        'validated_private_points': private_count,
        'private_original_membership_checks': private_count * len(classes),
        'private_requirements_for_eligible_parents': sum(len(requirements[m]) for m in parents),
        'option_count': count,
        'eligible_parent_count': len(parents),
        'child_record_count': sum(len(children) for _, _, children in options),
        'joint_original_membership_checks': len(joint) * len(classes),
        'joint_rescuer_membership_checks': len(joint) * count,
        'joint_points': joint_rows,
        'private_only_regression': {
            'selected_parent_count': len(changes),
            'all_supplied_private_points_retained': retained_checks,
            'lost_point': lost,
            'old_owners': old_owners,
            'final_owner_count': 0,
        },
        'search': dict(stats),
        'all_mixed_prime_centered_batches_excluded': True,
        'scope': 'Every nonempty batch of distinct original cofactor parents, using '
                 'actual child-induced centers with one common CRT point, loses an '
                 'old covered integer after simultaneous parent replacements. All '
                 'other labels are retained; a child may itself be another selected '
                 'parent. No unrestricted relocation or whole-cover theorem is claimed.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--originals', required=True)
    parser.add_argument('--blockers', required=True)
    parser.add_argument('--joint-blockers', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--max-nodes', type=int, default=1000000)
    args = parser.parse_args()
    require(args.max_nodes > 0, 'node limit must be positive')
    original_raw = Path(args.originals).read_bytes()
    blocker_raw = Path(args.blockers).read_bytes()
    joint_raw = Path(args.joint_blockers).read_bytes()
    require(hashlib.sha256(original_raw).hexdigest() == ORIGINALS_SHA256,
            'wrong original input bytes')
    result = evaluate(json.loads(original_raw), json.loads(blocker_raw),
                      json.loads(joint_raw), args.max_nodes)
    result['originals_sha256'] = ORIGINALS_SHA256
    result['blockers_sha256'] = hashlib.sha256(blocker_raw).hexdigest()
    result['joint_points_sha256'] = hashlib.sha256(joint_raw).hexdigest()
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: result[key] for key in
                      ('result', 'option_count', 'eligible_parent_count', 'search')},
                     sort_keys=True))


if __name__ == '__main__':
    main()
