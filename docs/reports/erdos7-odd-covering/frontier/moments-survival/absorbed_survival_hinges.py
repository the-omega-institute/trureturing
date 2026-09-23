"""Exact lower bounds for two whole-hinge source/deletion margins.

The ordinary cell-cost absorption proof supplies separately concave true
m_abs for h4 and h5 with signed barrier1. Their certified vertex lower bounds
are D-raw357(t)+epsilon_t. The epsilon table itself is not asserted concave.
All original labels and the predecessor's complete exponent tails remain.
"""
from fractions import Fraction as F
from hashlib import sha256

THRESHOLDS = (4, 5)
BARRIER = F(1)
SOURCE_HINGE_WEIGHT = F(29, 35)
Q_PREVIOUS = F(193, 231)
Q = F(23, 42)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reconstruct(source, rows):
    parameters = list(source.vertices())
    bases = source.BASES
    require(len(rows) == len(parameters) == 1296 and len(bases) == 10
            and [row['index'] for row in rows] == list(range(1296)),
            'Complete ordered source-parameter and independent shallow-layout inventories')
    require(Q == Q_PREVIOUS-F(1, 6)-F(4, 33)
            and SOURCE_HINGE_WEIGHT-F(2, 5) == F(3, 7) > 0,
            'All signed survival constants charged and cell-cost convexity budget positive')
    kappas = {}
    for threshold in THRESHOLDS:
        chi = lambda value: F(min(1, max(value-threshold, 0)))
        kappas[threshold] = tuple(sum(F(4, n*5**n)*(chi(n*b)-chi(n))
                                         for n in range(2, threshold+1)) for b in (1, 2, 3))
        require(all(chi(n*b) == chi(n) == 1 for n in (threshold+1, threshold+2)
                    for b in (1, 2, 3)),
                'Clipped-cost difference vanishes identically after the finite hinge range')
    require(kappas == {4: (F(0), F(23, 1875), F(173, 1875)),
                       5: (F(0), F(587, 46875), F(4337, 46875))},
            'Exact finite positive5 centered-cost gains')

    digest = sha256()
    count = 0
    output, changes = [], []
    zero_counts = {threshold: 0 for threshold in THRESHOLDS}
    for index, (parameter, row) in enumerate(zip(parameters, rows)):
        dat = source.data(parameter)
        d, n, eta, s, D = dat
        require((F(row['s']), F(row['D'])) == (s, D) and min(d) >= F(1, 4)
                and min(n) >= 0 and min(eta) > 0 and 0 < D <= s,
                'Same actual source mass and cell-cost density premises')
        require(isinstance(row['survival_hinge_margin'], F), 'Inherited exact h(5/2) margin')
        roots = (sum(n[:2]), sum(n[2:]))
        root_max, cell_max = max(roots), max(n)
        incident = any(roots[r] == root_max and n[j] == cell_max and source.ROOT[j] == r
                       for r in (0, 1) for j in range(5))
        updated, record = dict(row), {'index': index}
        for threshold in THRESHOLDS:
            values, labels = [], []
            for root in (0, 1):
                for cell in range(5):
                    penalty = (root_max+cell_max-roots[root]-n[cell])/5
                    omega = tuple(F(int(source.ROOT[l] == root)+int(l == cell), 5) for l in range(5))
                    require(penalty >= 0 and min(omega) >= 0 and max(omega) <= F(2, 5),
                            'Original shallow-carrier mass penalty and absorption weights')
                    for bi, b in enumerate(bases):
                        saving = sum(eta[l]*omega[l]*kappas[threshold][b[l]-1] for l in range(5))
                        value = penalty+saving
                        require(isinstance(value, F) and value >= 0, 'Nonnegative exact absorbed source saving')
                        values.append(value)
                        labels.append([root, cell, bi])
                        digest.update(f'{index},{threshold},{root},{cell},{bi}:{value}\n'.encode())
                        count += 1
            epsilon = min(values)
            require((epsilon == 0) == incident, 'Sharp maximum-root/maximum-cell zero-gain criterion')
            zero_counts[threshold] += int(epsilon == 0)
            raw = source.raw357(F(threshold), dat)
            margin = D-raw+epsilon
            updated['absorbed_hinge_'+str(threshold)+'_margin'] = margin
            updated['absorbed_hinge_'+str(threshold)+'_epsilon'] = epsilon
            record[str(threshold)] = {'epsilon': epsilon, 'raw_predecessor': raw,
                                      'margin_lower': margin,
                                      'minimizers': [label for label, v in zip(labels, values) if v == epsilon]}
        output.append(updated)
        changes.append(record)
    require(count == 259200, 'Complete two-hinge 1296 by 10 by 10 comparison')
    for index in (398, 410, 422, 616, 628, 640):
        e4, e5 = (output[index]['absorbed_hinge_'+str(t)+'_epsilon'] for t in THRESHOLDS)
        require((e4, e5, e4/6+F(4, 33)*e5) == (F(23, 84375), F(587, 2109375), F(11021, 139218750)),
                'Exact common control-point improvement')
    return output, {'thresholds': list(THRESHOLDS), 'barriers': [BARRIER, BARRIER],
                    'q_previous': Q_PREVIOUS, 'q_effective': Q,
                    'source_hinge_weight': SOURCE_HINGE_WEIGHT,
                    'minimum_absorbed_hinge_coefficient': F(3, 7),
                    'kappa': kappas, 'layout_checks': count,
                    'zero_epsilon_vertices': zero_counts, 'rows': changes,
                    'epsilon_margin_sha256': digest.hexdigest(),
                    'vertex_table_semantics': 'D-raw357(t)+epsilon_t is a lower bound at each vertex for the true globally defined separately concave absorbed whole-hinge margin m_abs. Epsilon itself is not asserted concave.',
                    'consumer_obligation': 'Use signed barriers1 for h4,h5 with the unchanged h(5/2) barrier7/2 on one actual S in [D,s]. Charge q_effective=23/42, retain all three margins, and select D or s according to each fixed-target coefficient sign.'}
