"""Finite TM62 original-source guards, online prefix image and memory bounds.

Python 3.9+, stdlib; source/target/Clifford helpers are reused from TM61.
This is mathematical experiment content, not a supplier or repository judge.
"""

import argparse
import importlib.util
from itertools import combinations
import json
from pathlib import Path


SPEC = importlib.util.spec_from_file_location(
    'tm61_source', Path(__file__).with_name('terminal_checkpoint.py'))
OLD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(OLD)
require = OLD.require


def size_path(cap, entry):
    """Each node is a REQUEST cut, including the final single-leaf request."""
    lo, hi = 0, cap
    path = []
    while True:
        length = 1 if hi - lo == 1 else hi - (lo + hi) // 2
        response = 'R' if hi - lo == 1 else ('A' if entry <= (lo + hi) // 2 else 'R')
        path.append((lo, hi, length, response))
        if hi - lo == 1:
            break
        cut = (lo + hi) // 2
        if response == 'A':
            hi = cut
        else:
            lo = cut
    require(hi == entry, 'Size leaf does not identify original entry')
    return path


def instruction(cap, state):
    stage, label, *data = state
    h, count = cap // 4, (cap // 4 + 3) // 4
    cutoff = 2 * count + 2 * label - 2
    if stage == 'initial':
        return ('right', cap - 4 * cutoff) if cutoff < h else ('rho',)
    if stage == 'context':
        return ('rho',)
    if stage == 'size':
        branch, lo, hi = data
        return ('right', 1 if hi - lo == 1 else hi - (lo + hi) // 2)
    branch, entry = data
    material = cap - 4 * cutoff if cutoff < h else 0
    return ('output', OLD.decode(h, label, branch, entry, material))


def update(cap, state, response):
    stage, label, *data = state
    require(response in ('A', 'R'), 'nonactual response alphabet')
    if stage == 'initial':
        h, count = cap // 4, (cap // 4 + 3) // 4
        if 2 * count + 2 * label - 2 < h:
            return ('context', label, response)
        return ('size', label, 'O' + response, 0, cap)
    if stage == 'context':
        return ('size', label, data[0] + response, 0, cap)
    require(stage == 'size', 'cannot update after output instruction')
    branch, lo, hi = data
    if hi - lo == 1:
        require(response == 'R', 'compulsory actual rejection was lost')
        return ('output', label, branch, hi)
    cut = (lo + hi) // 2
    return (('size', label, branch, lo, cut) if response == 'A'
            else ('size', label, branch, cut, hi))


def trace(cap, z, w):
    label, branch, entry, material = OLD.prefix(cap, z, w)
    states = [('initial', label)]
    responses = [] if branch[0] == 'O' else [branch[0]]
    responses.append(branch[1])
    responses.extend(node[3] for node in size_path(cap, entry))
    for response in responses:
        states.append(update(cap, states[-1], response))
    require(instruction(cap, states[-1]) == ('output', OLD.literal_target(cap // 4, z, w)),
            'online representation lost original literal output')
    return states, responses


def forest(cap, entries):
    """Prune the full midpoint tree by actual nonempty entry sets."""
    if not entries:
        return 0, 0
    def walk(lo, hi, active):
        if hi - lo == 1:
            require(active == {hi}, 'pruned leaf/entry mismatch')
            return 1, 0
        cut = (lo + hi) // 2
        children = [(lo, cut, {x for x in active if x <= cut}),
                    (cut, hi, {x for x in active if x > cut})]
        children = [x for x in children if x[2]]
        counts = [walk(*x) for x in children]
        return 1 + sum(x[0] for x in counts), (len(children) == 1) + sum(x[1] for x in counts)
    return walk(0, cap, set(entries))


def cap_image(cap):
    h, count = cap // 4, (cap // 4 + 3) // 4
    states, boundaries, entries, targets = set(), set(), {}, {}
    histories = {}
    for z in range(2, h + 1):
        for w in range(z + 1, 2 * z):
            label, branch, entry, material = OLD.prefix(cap, z, w)
            target = OLD.literal_target(h, z, w)
            key = (label, target)
            require(key not in targets or targets[key] == (branch, entry),
                    'a hidden composition changed its target trace')
            targets[key] = (branch, entry)
            entries.setdefault((label, branch), set()).add(entry)
            if branch[0] != 'O':
                boundaries.add((label, branch[0]))
            actual, responses = trace(cap, z, w)
            states.update(actual)
            history = ()
            for step, state in enumerate(actual):
                require(state not in histories or histories[state] == history,
                        'same prefix state has two different actual histories')
                histories[state] = history
                if step < len(responses):
                    history += ((instruction(cap, state), responses[step]),)
    q = len(targets)
    require(q == h * h // 4, 'full distinct original target count differs')
    require(sum(map(len, entries.values())) == q, 'branch entry inverse is not bijective')
    c, unary = map(sum, zip(*(forest(cap, x) for x in entries.values())))
    require(c == 2 * q - len(entries) + unary, 'unary/binary tree count fails')
    require(len(states) == count + len(boundaries) + c + q,
            'actual prefix image formula fails')
    bounds, loads = [0] * count, [0] * count
    for (label, target), (_, entry) in targets.items():
        loads[label - 1] += 1
        path = size_path(cap, entry)
        saturated = [x for x in path if x[1] == entry]
        width = saturated[0][1] - saturated[0][0]
        b = 1 + (width - 1).bit_length()
        require(len(saturated) == b and all(x[3] == 'R' for x in saturated),
                'saturated remaining-request count fails')
        bounds[label - 1] += b
    return {'H': cap, 'Q': q, 'L': count, 'e': len(boundaries),
            'nonempty_branches': len(entries), 'unary_nodes': unary,
            'size_nodes': c, 'prefix_image': len(states),
            'conditional_prefix_images': [sum(s[1] == i for s in states) for i in range(1, count + 1)],
            'target_loads': loads, 'saturated_request_lower_bounds': bounds}


def execute_tree(cap, word, actual):
    z, w = (word.count('a') + word.count('b')) // 4, (word.count('a') + 2 * word.count('b')) // 4
    require(OLD.leaves(actual) == word, 'literal bracketing changes source word')
    check = word
    for _ in range(3):
        require(OLD.ARITH.leaf_product(check) == OLD.ARITH.IDENTITY, 'source is not in complete U_H')
        check = ''.join('b' if x == 'a' else 'ba' for x in check)
    states, expected = trace(cap, z, w)
    current, accepted_rho, equality, inserted = actual, 0, 0, 0
    for index, response in enumerate(expected):
        state = states[index]
        action = instruction(cap, state)
        if state[0] == 'size':
            entry = OLD.prefix(cap, z, w)[2]
            lo, hi = state[-2:]
            require(lo < entry <= hi and len(OLD.leaves(current)) == entry + cap - hi,
                    'actual original Size invariant fails')
        candidate = (OLD.replace(current) if action == ('rho',)
                     else (current, OLD.tree('a' * action[1], 'left')))
        length = len(OLD.leaves(candidate))
        got = 'A' if length <= cap else 'R'
        require(got == response and update(cap, state, got) == states[index + 1],
                'actual guard or native response update differs')
        if got == 'A':
            equality += length == cap
            if action == ('rho',):
                accepted_rho += 1
            elif state[0] == 'size':
                inserted += action[1]
            current = candidate
    entry = OLD.prefix(cap, z, w)[2]
    require(len(OLD.leaves(current)) == cap and inserted == cap - entry,
            'actual terminal fill differs')
    branch = states[-1][2]
    require(OLD.ARITH.leaf_product(OLD.leaves(current)) ==
            (OLD.BPOW[cap % 4] if branch == 'AA' else OLD.APOW[cap % 4]),
            'all-residue terminal product differs')
    require(accepted_rho <= 1 and len(expected) <= (cap - 1).bit_length() + 3,
            'authentic simultaneous call/depth contract differs')
    require(expected[-1] == 'R' and instruction(cap, states[-2]) == ('right', 1),
            'final actual single-leaf rejection missing')
    return equality


def bracketings(word):
    if len(word) == 1:
        yield word
    else:
        for split in range(1, len(word)):
            for left in bracketings(word[:split]):
                for right in bracketings(word[split:]):
                    yield left, right


def recompute():
    rows = [cap_image(4 * h + delta) for h in range(2, 33) for delta in range(4)]
    dyadic = []
    for d in range(4, 11):
        row = cap_image(2 ** d)
        require(row['saturated_request_lower_bounds'][0] == 20 * (2 ** d // 16) - 2,
                'dyadic original-source lower bound fails')
        for m in range(1, 2 ** d + 1):
            require(sum(hi == m for _, hi, _, _ in size_path(2 ** d, m)) ==
                    (m & -m).bit_length(), 'dyadic valuation identity fails')
        dyadic.append({'H': row['H'], 'B1': row['saturated_request_lower_bounds'][0],
                       'TM61_K0': 5 * (row['H'] // 16) - 1})
    h60 = [r for r in rows if 60 <= r['H'] <= 63]
    require(all((r['prefix_image'], r['e'], r['nonempty_branches'], r['unary_nodes'], r['Q'])
                == (318, 7, 12, 151, 56) for r in h60), 'H60..63 image differs')
    executions, equality = 0, 0
    for h in range(2, 17):
        for z in range(2, h + 1):
            for w in range(z + 1, 2 * z):
                word = OLD.source_word(z, w)
                for delta in range(4):
                    for shape in ('left', 'balanced'):
                        equality += execute_tree(4 * h + delta, word, OLD.tree(word, shape))
                        executions += 1
    euler_words, all_bracket_executions = 0, 0
    for positions in combinations(range(8), 4):
        word = ''.join('a' if j in positions else 'b' for j in range(8))
        check, unit = word, True
        for _ in range(3):
            unit &= OLD.ARITH.leaf_product(check) == OLD.ARITH.IDENTITY
            check = ''.join('b' if x == 'a' else 'ba' for x in check)
        if not unit:
            continue
        euler_words += 1
        for actual in bracketings(word):
            for delta in range(4):
                equality += execute_tree(8 + delta, word, actual)
                all_bracket_executions += 1
    points = [(2, 3), (3, 4), (3, 5), (4, 5)]
    entries = [OLD.prefix(16, *p)[2] for p in points]
    saturated = [sum(hi == m for _, hi, _, _ in size_path(16, m)) for m in entries]
    require(entries == [16, 16, 12, 16] and saturated == [5, 5, 3, 5],
            'H16 original-target progress falsifier differs')
    require(OLD.prefix(21, 2, 3) == (2, 'OA', 12, 0), 'genuine positive-residue omission lost')
    # Actual target fields and both initial guards must remain available.
    falsifier_executions = 0
    for cap, points in ((80, [(6, 11), (16, 21)]), (72, [(6, 10), (10, 19)])):
        a, b = [OLD.prefix(cap, *p) for p in points]
        require(a[0] == b[0] and a[2] == b[2] and a[1] != b[1],
                'original response/branch falsifier differs')
        require(OLD.literal_target(cap // 4, *points[0]) != OLD.literal_target(cap // 4, *points[1]),
                'response-erasure falsifier no longer has different targets')
        for z, w in points:
            word = OLD.source_word(z, w)
            equality += execute_tree(cap, word, OLD.tree(word, 'balanced'))
            falsifier_executions += 1
    return {'schema': 'fib-tm62-online-prefix-v1', 'cap_rows': rows, 'dyadic_rows': dyadic,
            'actual_tree_domain': {'h': [2, 16], 'residues': [0, 1, 2, 3],
                                   'brackets': ['left', 'balanced']},
            'actual_tree_executions': executions, 'whole_candidate_equalities_accepted': equality,
            'actual_falsifier_executions': falsifier_executions,
            'complete_h2_domain': {'unit_leaf_words': euler_words, 'all_bracket_residue_executions': all_bracket_executions},
            'H16': {'points': [(2, 3), (3, 4), (3, 5), (4, 5)],
                    'entries': entries, 'saturated_requests': saturated, 'B1': sum(saturated),
                    'TM61_K0': 4, 'optional_Moore_lower_bound': sum(saturated) + 4},
            'H60_63': h60,
            'falsifiers': {'positive_residue_omission': [21, 2, 2, 3, 'OA', 12, 0],
                           'context_response_erasure': [80, [6, 11], [16, 21]],
                           'rho_response_erasure': [72, [6, 10], [10, 19]]}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = recompute()
    canonical = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.write:
        args.certificate.write_text(canonical)
    else:
        require(args.certificate.read_text() == canonical, 'retained finite evidence differs')
    print(json.dumps({k: result[k] for k in ['H16', 'dyadic_rows', 'actual_tree_executions',
                     'complete_h2_domain', 'whole_candidate_equalities_accepted']}, sort_keys=True))


if __name__ == '__main__':
    main()
