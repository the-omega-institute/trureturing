"""Exact original-label controls for fibrewise early-survivor conditioning.

Import-safe; standard library only. Checks remain active with python -O.
No fixture below is asserted to satisfy the asymptotic prime cutoff.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations
import json
import sys
from pathlib import Path


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def subsets(items, nonempty=False):
    for count in range(int(nonempty), len(items) + 1):
        yield from combinations(items, count)


def crt(congruences):
    modulus = 1
    for m, _ in congruences:
        modulus *= m
    residue = sum(value * (modulus // m) * pow(modulus // m, -1, m)
                  for m, value in congruences) % modulus
    return modulus, residue


def original(e, a, phases, head_phase=0, ternary_phase=0):
    congruences = list(phases.items())
    if a > 1:
        congruences.append((a, head_phase))
    if e > 0:
        congruences.append((3**e, ternary_phase))
    modulus, residue = crt(congruences)
    return dict(modulus=modulus, residue=residue, e=e, a=a,
                outside=tuple(sorted(phases)))


def matches(label, x, word, primes):
    return (x % label['a'] == label['residue'] % label['a']
            and all(word[primes.index(p)] == label['residue'] % p
                    for p in label['outside']))


def make_sources(points, primes, cuts, labels, head_inventory):
    require(len({v['modulus'] for v in labels}) == len(labels),
            'original numerical moduli must be pairwise distinct')
    for v in labels:
        require(v['modulus'] == 3**v['e']*v['a']*prod_tuple(v['outside']),
                'complete original numerical labels retained')
        require(0 <= v['residue'] < v['modulus'], 'actual original residue representative')
    early = [v for v in labels if v['e'] <= cuts[max(v['outside'])]]
    sigma, rho, survival, moments, branch_counts = {}, {}, {}, {}, {}
    for x in points:
        law = {(): F(1)}
        x_moments = {}
        branches = Counter()
        for stage, p in enumerate(primes):
            assigned = [v for v in early if max(v['outside']) == p]
            next_law = {}
            alpha_square, violation = F(0), F(0)
            for prefix, prefix_mass in law.items():
                forbidden = set()
                for v in assigned:
                    if x % v['a'] != v['residue'] % v['a']:
                        continue
                    if all(prefix[primes.index(q)] == v['residue'] % q
                           for q in v['outside'] if q < p):
                        forbidden.add(v['residue'] % p)
                alpha = F(len(forbidden), p)
                if alpha == 0:
                    branch = 'alpha_zero'
                elif alpha <= F(1, 2):
                    branch = 'low_positive'
                elif alpha == 1:
                    branch = 'completely_forbidden'
                else:
                    branch = 'high_partial'
                if prefix_mass:
                    branches[branch] += 1
                row = {}
                for leaf in range(p):
                    if alpha <= F(1, 2):
                        density = F(0) if leaf in forbidden else 1 / (1-alpha)
                    else:
                        density = ((alpha-F(1, 2))/(alpha*F(1, 2))
                                   if leaf in forbidden else F(2))
                    require(0 <= density <= 2, 'full-history density cap')
                    row[leaf] = density / p
                    next_law[prefix+(leaf,)] = prefix_mass * row[leaf]
                require(sum(row.values()) == 1, 'normalized full-history row')
                row_violation = sum(row[y] for y in forbidden)
                expected_violation = max(alpha-F(1, 2), F(0))*2
                require(row_violation == expected_violation, 'exact capped-kernel bad mass')
                alpha_square += prefix_mass*alpha**2
                violation += prefix_mass*row_violation
                require(sum(next_law[prefix+(y,)] for y in range(p)) == prefix_mass,
                        'complete prefix marginal preservation')
            require(sum(next_law.values()) == 1, 'normalized prefix law')
            law = next_law
            require(violation <= alpha_square, 'delta=1/2 second-moment bound')
            moment_bound = F((head_inventory*(cuts[p]+1))**2,p*p)
            # Both fixtures have J=1: (0,0),(1,0),(0,1),(1,1) give 1+6/q.
            for q in primes[:stage]:
                moment_bound *= 1+F(6,q)
            require(alpha_square <= moment_bound,
                    'full-predecessor finite-height original-tuple second moment')
            x_moments[p] = dict(second_moment=alpha_square, assigned_bad_mass=violation,
                               full_predecessor_second_moment_bound=moment_bound)
        sigma[x] = law
        require(sum(law.values()) == 1, 'normalized complete unconditioned law')
        good = {word: not any(matches(v, x, word, primes) for v in early)
                for word in law}
        survival[x] = sum(w for word, w in law.items() if good[word])
        require(survival[x] > 0, 'positive measured fibre survival')
        rho[x] = {word: w/survival[x] if good[word] else F(0)
                  for word, w in law.items()}
        require(sum(rho[x].values()) == 1, 'normalized conditioned fibre law')
        for stage, p in enumerate(primes):
            assigned = [v for v in early if max(v['outside']) == p]
            actual_bad = sum(w for word, w in law.items()
                             if any(matches(v, x, word, primes) for v in assigned))
            require(actual_bad == x_moments[p]['assigned_bad_mass'],
                    'later kernels preserve assigned violation probability')
        require(1-survival[x] <= sum(v['assigned_bad_mass'] for v in x_moments.values()),
                'common survivor union bound')
        moments[x] = x_moments
        branch_counts[x] = dict(sorted(branches.items()))
    return sigma, rho, survival, moments, branch_counts


def verify_joint_caps(sigma, rho, survival, points, primes):
    query_count = 0
    for x in points:
        for selected in subsets(tuple(range(len(primes))), nonempty=True):
            sigma_marginal, rho_marginal = defaultdict(F), defaultdict(F)
            denominator = 1
            for index in selected:
                denominator *= primes[index]
            cap = F(2**len(selected), denominator)
            for word in sigma[x]:
                key = tuple(word[index] for index in selected)
                sigma_marginal[key] += sigma[x][word]
                rho_marginal[key] += rho[x][word]
            for key in sigma_marginal:
                query_count += 1
                require(sigma_marginal[key] <= cap, 'unconditioned selected-cylinder cap')
                require(rho_marginal[key] <= cap/survival[x],
                        'conditioned joint-cylinder cap with one survivor denominator')
    return query_count


def original_masses(labels, points, primes, rho, mu):
    return {v['modulus']: sum(mu[x]*w for x in points for word, w in rho[x].items()
                             if matches(v, x, word, primes)) for v in labels}


def two_prime_countercontrols():
    primes, points = (43,47), (0,1)
    divisors = (1,5,7,25,35,49,175,245)
    labels = [original(e, a, {43:0, 47:8*e+i+1})
              for e in range(3) for i,a in enumerate(divisors)]
    cuts = {43:3, 47:3}
    sigma,rho,survival,moments,branches = make_sources(points,primes,cuts,labels,9)
    query_count = verify_joint_caps(sigma,rho,survival,points,primes)
    require(survival == {0:F(2020,2021),1:F(1)}, 'countercontrol survival values')
    row_mass = sum(rho[0][0,y] for y in range(47))
    conditional_leaf = rho[0][0,0]/row_mass
    require(conditional_leaf == F(1,23) > F(2,47),
            'countercontrol must disprove unchanged full-prefix cap')
    mu = {0:F(1,2),1:F(1,2)}
    global_good = sum(mu[x]*survival[x] for x in points)
    global_conditioned_zero = mu[0]*survival[0]/global_good
    require(global_conditioned_zero == F(2020,4041) != mu[0],
            'global conditioning must change the supplied core marginal')
    recovered_mu = {x:sum(mu[x]*w for w in rho[x].values()) for x in points}
    require(recovered_mu == mu, 'fibrewise conditioning must preserve the supplied marginal')
    masses = original_masses(labels,points,primes,rho,mu)
    require(all(m == 0 for m in masses.values()), 'every original early cofactor is killed')
    return dict(original_labels=labels, core_modulus=1225, core_law=mu,
                original_ternary_height=3, outside_primes=primes, outside_heights={43:1,47:1},
                number_of_originals=len(labels), early_cuts=cuts,
                measured_survival=survival, selected_cylinder_queries=query_count,
                conditioned_prefix_leaf=conditional_leaf, original_prefix_cap=F(2,47),
                global_conditioned_core_zero=global_conditioned_zero,
                fibrewise_conditioned_core_law=recovered_mu,
                positive_prefix_branch_counts=branches, stages=moments)


def three_prime_fixture():
    primes, points = (5,7,11), (0,1,2)
    cuts, mu = {5:0,7:1,11:1}, {0:F(1,2),1:F(1,3),2:F(1,6)}
    labels = []
    for support in subsets(primes,nonempty=True):
        last = max(support)
        for e in range(3):
            for a in (1,13):
                h = int(a == 13)
                if last == 5:
                    phase5 = ((h if e == 0 else (4-h if e == 1 else 2+2*h)))
                    phases = {5:phase5}
                elif last == 7:
                    if e <= 1:
                        qphase = (2*e+h if support == (7,) else (4+2*e+h)%7)
                        phases = {7:qphase}
                        if 5 in support:
                            phases[5] = 2
                    else:
                        phases = {q:4 for q in support if q != 7}
                        phases[7] = 5+h
                else:
                    if e <= 1:
                        rphase = 2*e+h if support == (11,) else 4+2*e+h
                        phases = {11:rphase}
                        if 5 in support:
                            phases[5] = 4 if 7 in support else 3
                        if 7 in support:
                            phases[7] = 5 if 5 in support else 4
                    else:
                        phases = {q:(4 if q == 5 else 5) for q in support if q != 11}
                        phases[11] = 8+h
                head_phase = 2 if e == 2 else 0
                ternary_phase = (2+h+sum(support)+e) % 3**e
                labels.append(original(e,a,phases,head_phase,ternary_phase))
    require(len(labels) == 42, 'complete 3-prime fixture original count')
    sigma,rho,survival,moments,branches = make_sources(points,primes,cuts,labels,2)
    query_count = verify_joint_caps(sigma,rho,survival,points,primes)
    recovered_mu = {x:sum(mu[x]*w for w in rho[x].values()) for x in points}
    require(recovered_mu == mu, 'nonuniform three-point core marginal preservation')
    masses = original_masses(labels,points,primes,rho,mu)
    weighted_load, measured_bound, uniform_bound = F(0),F(0),F(0)
    gamma = min(survival.values())
    event_records = []
    for v in labels:
        is_early = v['e'] <= cuts[max(v['outside'])]
        if is_early:
            require(masses[v['modulus']] == 0, 'all actual early originals vanish')
        if v['e'] == 0:
            require(masses[v['modulus']] == 0, 'actual original three-free support')
        if v['e'] == 0:
            continue
        weight = F(1,3**(v['e']-1))
        cap = F(2**len(v['outside']),prod_tuple(v['outside']))
        conditional_cap = sum(mu[x]*cap/survival[x] for x in points
                              if x % v['a'] == v['residue'] % v['a'])
        require(masses[v['modulus']] <= conditional_cap, 'one-law original cylinder bound')
        weighted_load += weight*masses[v['modulus']]
        if not is_early:
            measured_bound += weight*conditional_cap
            uniform_bound += weight*cap/gamma
        event_records.append(dict(modulus=v['modulus'],early=is_early,
                                  weight=weight,common_law_mass=masses[v['modulus']],
                                  measured_fibre_cap=conditional_cap))
    require(weighted_load > 0, 'late completion fixture must be nonzero')
    require(weighted_load <= measured_bound <= uniform_bound, 'same-law weighted late bound')
    triple_early = [v for v in labels if len(v['outside']) == 3 and v['e'] <= 1]
    triple_late = [v for v in labels if len(v['outside']) == 3 and v['e'] == 2]
    require(all(masses[v['modulus']] > 0 for v in triple_late), 'both original late triples have positive mass')
    # These early triples remove points that every nontriple early class leaves untouched.
    exclusive_triple_mass = sum(sigma[0][word] for word in sigma[0]
        if any(matches(v,0,word,primes) for v in triple_early)
        and not any(matches(v,0,word,primes) for v in labels
                    if len(v['outside']) < 3 and v['e'] <= cuts[max(v['outside'])]))
    require(exclusive_triple_mass > 0, 'early triples must impose a substantive additional constraint')
    merged_branches = Counter()
    for value in branches.values():
        merged_branches.update(value)
    require(merged_branches['low_positive'] > 0 and merged_branches['high_partial'] > 0,
            'both nontrivial capped-kernel branches must occur')
    require(merged_branches['completely_forbidden'] > 0,
            'normalization of a completely forbidden intermediate fibre is exercised')
    common_law = [dict(core=x,outside=word,mass=mu[x]*w)
                  for x in points for word,w in rho[x].items() if w]
    require(sum(v['mass'] for v in common_law) == 1, 'one final actual common law')
    return dict(boundary='Uses measured fibre survival; does not claim the large-cutoff theorem at primes 5,7,11.',
                core_modulus=13, core_law=mu, original_ternary_height=2,
                outside_primes=primes,outside_heights={p:1 for p in primes},
                early_cuts=cuts,original_labels=labels,number_of_originals=len(labels),
                measured_survival=survival,minimum_fibre_survival=gamma,
                selected_cylinder_queries=query_count,positive_prefix_branch_counts=branches,
                stages=moments,recovered_core_law=recovered_mu,
                number_of_early_three_free_originals=sum(v['e']==0 for v in labels),
                early_triple_exclusive_unconditioned_mass_at_core_zero=exclusive_triple_mass,
                late_triple_common_law_masses={v['modulus']:masses[v['modulus']] for v in triple_late},
                common_law_atom_count=len(common_law),common_law=common_law,
                weighted_late_load=weighted_load,measured_fibre_weighted_bound=measured_bound,
                minimum_fibre_weighted_bound=uniform_bound,completion_events=event_records)


def prod_tuple(values):
    result = 1
    for value in values:
        result *= value
    return result


def exact_constants():
    # Exact endpoints and ratio constants for the separate analytic proof.
    # No finite D/support scan is presented as its universal quantification.
    require(108*513**2 == 28422252 < 3**16, 'early-load power-of-three constant')
    require(324 < 3**6, 'late-load power-of-three constant')
    require(112 < 256 and 28 < 256, 'exponential product prefactors below e')
    require(2*114 <= 256 and 2*28 <= 256, 'integral degree thresholds')
    require(F(1,3**240)<F(1,2) and F(1,3**250)<F(1,4),
            'strict survival and quarter endpoints')
    return dict(cutoff_formula='3^256 D^4',early_polynomial_constant=108*513**2,
                early_power_bound=3**16,late_constant=324,late_power_bound=3**6,
                general_epsilon_bound=F(1,3**240),general_late_bound=F(1,3**250),
                boundary='All-D and unrestricted-support conclusions are proved analytically; these finite rational comparisons do not replace that proof.')


def serializable(value):
    if isinstance(value,F):
        return f'{value.numerator}/{value.denominator}'
    if isinstance(value,dict):
        return {str(k):serializable(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [serializable(v) for v in value]
    return value


def build_controls():
    return dict(schema='erdos7-unrestricted-tail-completion-controls-v1',
                status='all explicit exact checks passed',
                scope='Actual original-label finite controls with two or three outside primes. Unrestricted outside support is established by the separate analytic proof, not by these finite controls. No Lean certification or unrestricted Erdős #7 claim.',
                two_prime_countercontrols=two_prime_countercontrols(),
                three_prime_fixture=three_prime_fixture(),exact_constants=exact_constants())


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='Write exact JSON result data to this path.')
    args = parser.parse_args()
    result = build_controls()
    payload = json.dumps(serializable(result),ensure_ascii=False,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(payload,encoding='utf-8')
    else:
        print(payload,end='')
    fixture = result['three_prime_fixture']
    print('PASS: original labels, full-history kernels, all selected joint caps, fibrewise support and core marginal, same-law late load.',file=sys.stderr)
    print('Three-prime measured survival:',fixture['measured_survival'],file=sys.stderr)
    print('Three-prime late load and bound:',fixture['weighted_late_load'],fixture['measured_fibre_weighted_bound'],file=sys.stderr)


if __name__ == '__main__':
    main()
