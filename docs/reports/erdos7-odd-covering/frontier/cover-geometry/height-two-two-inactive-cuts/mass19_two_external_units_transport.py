from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from collections import deque
import random
import json
import argparse
from hashlib import sha256


def need(test, message):
    if not test:
        raise ValueError(message)


def flow_matrix(support, row_caps, col_caps, edge_caps=2):
    n, source, sink = 14, 12, 13
    capacity = [[0]*n for _ in range(n)]
    for i in range(5):
        capacity[source][i] = row_caps[i]
    for j in range(7):
        capacity[5+j][sink] = col_caps[j]
    for i, j in support:
        capacity[i][5+j] = edge_caps[i, j] if isinstance(edge_caps, dict) else edge_caps
    residual = [row[:] for row in capacity]
    value = 0
    while True:
        parent = [-1]*n
        parent[source] = source
        queue = deque([source])
        while queue and parent[sink] < 0:
            v = queue.popleft()
            for u in range(n):
                if parent[u] < 0 and residual[v][u] > 0:
                    parent[u] = v
                    queue.append(u)
        if parent[sink] < 0:
            reached = {i for i, p in enumerate(parent) if p >= 0}
            break
        path = []
        u = sink
        while u != source:
            v = parent[u]
            path.append((v, u))
            u = v
        amount = min(residual[v][u] for v, u in path)
        for v, u in path:
            residual[v][u] -= amount
            residual[u][v] += amount
        value += amount
    matrix = [[F(capacity[i][5+j]-residual[i][5+j]) for j in range(7)] for i in range(5)]
    return value, matrix, ({i for i in range(5) if i in reached},
                           {j for j in range(7) if 5+j in reached})


def truncate(matrix, target):
    out = [row[:] for row in matrix]
    remove = sum(map(sum, out))-target
    need(remove >= 0, 'truncation direction')
    for i in range(5):
        for j in range(7):
            step = min(remove, out[i][j])
            out[i][j] -= step
            remove -= step
    need(remove == 0, 'truncation total')
    return out


def check(matrix, support, z, y):
    rows = list(map(sum, matrix))
    cols = [sum(matrix[i][j] for i in range(5)) for j in range(7)]
    need(sum(rows) == 19, 'mass19')
    need(all(rows[i] <= min(6, 7-z[i]) for i in range(5)), 'row caps')
    need(all(cols[j] <= 7-y[j] for j in range(7)), 'column caps')
    need(all(0 <= matrix[i][j] <= 2 and ((i, j) in support or matrix[i][j] == 0)
             for i in range(5) for j in range(7)), 'entry caps and actual support')
    maximum = max(20*rows[i]+20*cols[j]+25*matrix[i][j]+5*z[i]+5*y[j]
                  for i in range(5) for j in range(7))
    need(maximum <= 310, 'augmented score')
    return maximum


def construct(support, z, y, declared_cut=None):
    need(len(z) == 5 and len(y) == 7 and sum(z) == sum(y) == 2,
         'external mass')
    need(all(isinstance(t, int) and t >= 0 for t in z+y), 'integral external mass')
    maximum, matrix, mincut = flow_matrix(support, [min(6, 7-t) for t in z],
                                         [7-t for t in y])
    need(maximum >= 19, 'initial feasibility')
    if max(z) == 2:
        result, branch = truncate(matrix, 19), 'concentrated_z'
    elif maximum >= 20:
        result = [[F(19, 20)*value for value in row] for row in truncate(matrix, 20)]
        branch = 'maximum_at_least20'
    else:
        I, J = declared_cut if declared_cut is not None else mincut
        I, J = set(I), set(J)
        outside = set(range(5))-I
        ordinary = {j for j in range(7) if y[j] == 0}
        flags = set(range(7))-ordinary
        a, b, f = len(outside), len(J & ordinary), len(J & flags)
        cross = {(i, j) for i, j in support if i in I and j not in J}
        c = len(cross)
        need(6*a+sum(7-y[j] for j in J)+2*c == 19, 'declared minimum cut')
        need(all(matrix[i][j] == 2 for i, j in cross), 'forced crossing entries')
        need(all(matrix[i][j] == 0 for i in outside for j in J), 'no backward cut flow')
        result = [row[:] for row in matrix]
        branch = ('y2' if max(y) == 2 else 'y11') + f':a{a}b{b}f{f}c{c}'
        if a == 0 and b == 1 and (max(y) == 1 or f == 0):
            ordinary_column = next(iter(J & ordinary))
            row_residual = [6-sum(matrix[i][j] for j in range(7) if j not in J)
                            for i in range(5)]
            local_support = {(i, j) for i, j in support if j in J}
            need(all(r.denominator == 1 and int(r) % 2 == 0 for r in row_residual),
                 'even residual row capacities')
            edge_caps = {(i, j): 9 if j == ordinary_column else 10 for i, j in local_support}
            value, repair, _ = flow_matrix(local_support, [5*int(r) for r in row_residual],
                                           [5*(7-y[j]) if j in J else 0 for j in range(7)],
                                           edge_caps)
            need(value == 5*sum(7-y[j] for j in J), 'parity-shaved feasibility')
            for i in range(5):
                for j in J:
                    result[i][j] = repair[i][j]/5
        elif a == 0 and max(y) == 2 and b == 0 and f == 1:
            pass
        elif a == 0 and max(y) == 2 and b == 2 and f == 1:
            for j in J:
                neighbors = [i for i in I if (i, j) in support]
                for i in I:
                    result[i][j] = F(7-y[j], len(neighbors)) if i in neighbors else F(0)
        elif a == 1 and b == 1 and f == 0:
            j = next(iter(J))
            need(len(I) == 4 and all((i, j) in support for i in I), 'four ordinary neighbors')
            for i in I:
                result[i][j] = F(7, 4)
        elif a == 1 and max(y) == 2 and b == 0 and f == 1:
            row = next(iter(outside))
            degrees = {j: sum((i, j) in cross for i in I) for j in ordinary}
            threes = [j for j, degree in degrees.items() if degree == 3]
            need(len(threes) <= 1 and max(degrees.values()) <= 3, 'degree3 uniqueness')
            if threes:
                excluded = threes[0]
                choices = sorted(j for j in ordinary if j != excluded and (row, j) in support)
                need(len(choices) >= 3, 'three ordinary alternative columns')
                for j in range(7):
                    result[row][j] = F(2) if j in choices[:3] else F(0)
        elif a == 2 and max(y) == 2 and b == 0 and f == 1 and c == 1:
            pass
        elif a == 1 and max(y) == 1 and b == 1 and f == 1 and c == 0:
            for j in J:
                neighbors = [i for i in I if (i, j) in support]
                for i in I:
                    result[i][j] = F(7-y[j], len(neighbors)) if i in neighbors else F(0)
        else:
            raise ValueError(f'unclassified feasible minimum cut {branch}')
    score = check(result, support, z, y)
    return result, {'branch': branch, 'maximum_flow': maximum, 'max_augmented_score': str(score)}


def main():
    parser=argparse.ArgumentParser(description="Exact rational controls for mass19 transport with two external units")
    parser.add_argument("--output", type=Path, required=True, help="Result JSON path")
    args=parser.parse_args()
    generator = random.Random(190310)
    all_edges = {(i, j) for i in range(5) for j in range(7)}
    types = {
        'y2': [(0,1,0,6),(1,1,0,3),(0,0,1,7),(1,0,1,4),(2,0,1,1),(0,2,1,0)],
        'y11': [(0,1,0,6),(1,1,0,3),(0,1,1,3),(1,1,1,0),(0,1,2,0)],
    }
    excluded = (2,1,0,0)
    for name, flag_count, ordinary_count, flag_cap in [('y2',1,6,5),('y11',2,5,6)]:
        derived = {(a,b,f,c) for a in range(6) for b in range(ordinary_count+1)
                   for f in range(flag_count+1) for c in range(36)
                   if 6*a+7*b+flag_cap*f+2*c == 19
                   and c <= (5-a)*(7-b-f)}
        need(derived == set(types[name]) | {excluded}, 'complete cut-type enumeration')
    fixture_rows = []
    verified = 0
    for name, profiles in types.items():
        y = [2,0,0,0,0,0,0] if name == 'y2' else [1,1,0,0,0,0,0]
        flags = [j for j in range(7) if y[j]]
        ordinary = [j for j in range(7) if not y[j]]
        for a,b,f,c in profiles:
            I = set(range(a,5))
            J = set(flags[:f]+ordinary[:b])
            possible = sorted((i,j) for i in I for j in range(7) if j not in J)
            kept = None
            for attempt in range(2000):
                cross = set(generator.sample(possible, c))
                support = (all_edges-set(possible)) | cross
                maximum, _, _ = flow_matrix(support, [6]*5, [7-t for t in y])
                if maximum == 19:
                    kept = support
                    break
            need(kept is not None, 'named cut fixture found')
            for marked in combinations(range(5),2):
                z = [int(i in marked) for i in range(5)]
                matrix, metadata = construct(kept,z,y,(I,J))
                verified += 1
                fixture_rows.append({'type': name, 'profile': [a,b,f,c], 'marked_rows': list(marked),
                                     'support': sorted(map(list,kept)), 'certificate': metadata,
                                     'matrix': [[str(t) for t in row] for row in matrix]})
    # Explicit exercise of the unique degree3-column repair.
    y, z = [2,0,0,0,0,0,0], [1,1,0,0,0]
    I, J = {1,2,3,4}, {0}
    cross = {(1,1),(2,1),(3,1),(4,2)}
    possible = {(i,j) for i in I for j in range(1,7)}
    support = (all_edges-possible)|cross
    matrix, metadata = construct(support,z,y,(I,J))
    verified += 1
    fixture_rows.append({'type': 'explicit_degree3_repair', 'support': sorted(map(list,support)),
                         'certificate': metadata, 'matrix': [[str(t) for t in row] for row in matrix]})
    random_branches = {}
    infeasible = 0
    for trial in range(3000):
        density = generator.choice([.25,.35,.45,.55,.7,1.0])
        support = {edge for edge in all_edges if generator.random()<density}
        z = [0]*5
        y = [0]*7
        for _ in range(2):
            z[generator.randrange(5)] += 1
            y[generator.randrange(7)] += 1
        maximum, _, _ = flow_matrix(support,[min(6,7-t) for t in z],[7-t for t in y])
        if maximum < 19:
            infeasible += 1
            continue
        _, metadata = construct(support,z,y)
        verified += 1
        random_branches[metadata['branch']] = random_branches.get(metadata['branch'],0)+1
    result = {'scope': 'Exact constructor controls for the ordinary universal mass19 proof; no Lean claim.',
              'verified_feasible_instances': verified, 'random_infeasible_instances': infeasible,
              'named_minimum_cut_types': 11, 'named_fixtures': fixture_rows,
              'excluded_minimum_cut_type_for_each_y_pattern': list(excluded),
              'random_branch_counts': random_branches,
              'score_ceiling':310, 'coherent_charge_ceiling_at_a_b_21_d_19':607,
              'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: {verified} feasible exact constructions, all11 minimum-cut types, 310 augmented ceiling')


if __name__ == '__main__':
    main()
