"""Raise the signed square-cost barrier while retaining its actual raw deficit.

The proved uniform source norm remains SOURCE_NORM. BARRIER is an independent
constant used in the signed inequality. Its increase is charged to H16 and A81
by the consumer. The true margin dominates the old margin plus (BARRIER -
SOURCE_NORM) * D globally; the patched vertex table is a certified lower bound,
not itself a function claimed to be separately concave.
"""
from fractions import Fraction as F
from hashlib import sha256

SOURCE_NORM = F(102715, 2916)
BARRIER = F(45)
SELECTED = (398, 410, 422, 616, 628, 640)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def _distance(eta, b, c):
    delta = tuple(x-y for x, y in zip(b, c))
    return sum(w*v*v for w, v in zip(eta, delta)) - (
        max((0,)+delta)**2+max((0,)+tuple(-v for v in delta))**2)/F(18)


def refine(source, fixed, rows, outside):
    """Return new margin lower bounds without changing any input row.

    `rows` is the output of shared_source_deficits.aggregate, optionally after
    the independent linear refinement. `outside` is its quadratic_tail_weight
    (the complete quadratic complement from the same AP inventory).
    """
    outside = F(outside)
    require(outside > 0 and BARRIER > SOURCE_NORM,
            'Positive complete quadratic complement and fixed barrier increase')
    bases = source.BASES
    parameters = list(source.vertices())
    require(len(bases) == 10 and len(rows) == len(parameters) == 1296
            and [row['index'] for row in rows] == list(range(1296)),
            'Complete independent layouts and ordered source-parameter vertices')
    increase = BARRIER-SOURCE_NORM
    result = [dict(row) for row in rows]
    for row, updated in zip(rows, result):
        mg, Mquad, D = (F(row[key]) for key in ('source_margin', 'Mquad', 'D'))
        margins = tuple(F(value) for value in row['quadratic_margins'])
        require(len(margins) == 5 and min((mg, Mquad, D)+margins) >= 0
                and 0 < D <= F(row['s']) and Mquad == sum(margins)+outside*mg,
                'Unchanged five quadratic margins and complete source contribution')
        updated['source_margin'] = mg+increase*D
        updated['Mquad'] = Mquad+outside*increase*D

    previous_digest, refined_digest = sha256(), sha256()
    previous_checks = refined_checks = 0
    changes = []
    for index in SELECTED:
        dat = source.data(parameters[index])
        d, n, eta, s, D = dat
        row = rows[index]
        require((s, D) == (F(row['s']), F(row['D']))
                and min(d) >= F(1, 4) and min(n) >= 0 and 0 < D <= s,
                'Same actual source mass and density parameter')
        cap0 = fixed._cofactor_cap(dat, (F(1),)*5, (F(0),)*5, 6)
        require(cap0 == 5*(s-D) and cap0 >= 0,
                'Complete unweighted cofactor cap is exactly the raw mass loss')
        pure = tuple(sum(w*x*x for w, x in zip(eta, b))
                     +max(F(x+1, 9) for x in b) for b in bases)
        maximum_pure = max(pure)
        base = tuple(sum((mass+w/4)*x*x for mass, w, x in zip(n, eta, b))
                     +max((a+F(1, 4))*F(x+1, 9) for a, x in zip(d, b))
                     for b in bases)
        global35 = max(base)+F(5, 8)*maximum_pure
        previous_values, refined_values, labels = [], [], []
        for bi, b in enumerate(bases):
            old_k = tuple(SOURCE_NORM-x*x for x in b)
            new_k = tuple(BARRIER-x*x for x in b)
            for ci, c in enumerate(bases):
                correction = tuple(F((2*x+1)*y) for x, y in zip(b, c))
                require(all(0 <= corr <= old <= new
                            for corr, old, new in zip(correction, old_k, new_k)),
                        'Original 5,15,45 square floors remain admissible')
                selected = base[bi]+F(9, 20)*pure[ci]+F(7, 40)*maximum_pure
                selected -= F(4, 25)*_distance(eta, b, c)
                raw_source = F(6, 5)*selected+F(7, 15)*global35
                old_cap = fixed._cofactor_cap(dat, old_k, correction, 6)
                new_cap = fixed._cofactor_cap(dat, new_k, correction, 6)
                require(new_cap <= old_cap+increase*cap0,
                        'Raised square barrier is paid by the exact raw mass-loss cap')
                old_margin = SOURCE_NORM*s-raw_source-old_cap/5
                new_margin = BARRIER*s-raw_source-new_cap/5
                require(old_margin >= 0 and new_margin >= old_margin+increase*D,
                        'Exact square margins dominate the fully charged inherited bound')
                previous_values.append(old_margin)
                refined_values.append(new_margin)
                labels.append([bi, ci])
                previous_digest.update(f'{index},{bi},{ci}:{old_margin}\n'.encode())
                refined_digest.update(f'{index},{bi},{ci}:{new_margin}\n'.encode())
                previous_checks += 1
                refined_checks += 1
        old_mg, new_mg = min(previous_values), min(refined_values)
        inherited_mg = old_mg+increase*D
        require(old_mg == F(row['source_margin']) and new_mg > inherited_mg,
                'Published source margin reconstructed and strict selected-vertex gain')
        result[index]['source_margin'] = new_mg
        result[index]['Mquad'] = F(row['Mquad'])+outside*(new_mg-old_mg)
        changes.append({'index': index, 'previous_source_margin': old_mg,
                        'inherited_source_margin': inherited_mg,
                        'refined_source_margin': new_mg,
                        'net_gain': new_mg-inherited_mg,
                        'previous_Mquad': F(row['Mquad']),
                        'refined_Mquad': result[index]['Mquad'],
                        'minimizers': [label for label, value in zip(labels, refined_values)
                                       if value == new_mg]})
    require(previous_checks == refined_checks == 600,
            'Six complete 10 by 10 original-label comparisons')
    return result, {'source_norm': SOURCE_NORM, 'source_barrier': BARRIER,
                    'source_barrier_increase': increase,
                    'H16_increase': outside*increase,
                    'quadratic_tail_weight': outside,
                    'updated_vertices': list(SELECTED), 'inherited_vertices': 1290,
                    'predecessor_layout_checks': previous_checks,
                    'refined_layout_checks': refined_checks,
                    'predecessor_margin_sha256': previous_digest.hexdigest(),
                    'margin_sha256': refined_digest.hexdigest(), 'changes': changes,
                    'vertex_table_semantics': 'Source margins are vertex lower bounds for one globally defined separately concave square refinement at barrier45. Inherited rows add source_barrier_increase times D. Five independent quadratic margins are unchanged; their complete complement uses the new source margin. No concavity claim is made for the patched table itself.',
                    'consumer_obligation': 'Keep source_norm as the proved uniform norm. Add H16_increase to H16 and cG times source_barrier_increase to A81, retain the updated raw deficits in all consumers, check all 1296 target vertices and the four positive D coefficients. Eight missing-class branches remain separate.'}
