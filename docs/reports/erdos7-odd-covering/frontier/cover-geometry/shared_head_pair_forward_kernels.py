#!/usr/bin/env python3
"""Exact joint budgets for increasing networks over a shared head pair.

All Report601 finite root choices remain unchanged. Nonroot moments reuse
Report610's exact table routine with reference (3,37), cap 37/4. The proof
supplies the common-source construction and the full infinite-tail argument.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import isqrt
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, default=Path(__file__).parent)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks, sources = {}, {}

    def require(name, value):
        if not value:
            raise ArithmeticError(name)
        checks[name] = True

    def load(name):
        path = args.source_dir/name
        raw = path.read_bytes()
        value = json.loads(raw)
        require(name+'_checks_true', bool(value['checks'])
                and all(v is True for v in value['checks'].values()))
        fingerprint = sha256(path.with_suffix('.py').read_bytes()).hexdigest()
        require(name+'_producer_fingerprint', fingerprint == value['producer_sha256'])
        sources[name] = dict(sha256=sha256(raw).hexdigest(), producer_sha256=fingerprint)
        return value

    old = load('staged_two_parent_attachment.json')
    load('recursive_pair_forward_kernels.json')
    method_path = args.source_dir/'recursive_pair_forward_kernels.py'
    spec = importlib.util.spec_from_file_location('prior_forward_kernels', method_path)
    method = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(method)

    boundary, n0, cap = 971, 22, F(37, 4)
    primes = [v for v in range(37, boundary)
              if all(v % p for p in range(2, isqrt(v)+1))]
    sieve = bytearray(b'\1')*boundary
    sieve[:2] = b'\0\0'
    for p in range(2, isqrt(boundary-1)+1):
        if sieve[p]:
            sieve[p*p:boundary:p] = b'\0'*((boundary-1-p*p)//p+1)
    require('prime_enumerations_agree', len(primes) == 152
            and primes == [v for v in range(37, boundary) if sieve[v]])
    require('same_root_budget', F(old['fee_tables']['3_5']['total_fee']) < F(1,2600)
            and F(old['fee_tables']['3_23']['total_fee']) < F(1,125000))
    root_rows = {}
    for tag in ('3_5', '3_23'):
        rows = old['fee_tables'][tag]['finite_rows']
        require(tag+'_all_root_rows', [row['entry_prime'] for row in rows] == primes)
        saved = []
        for row in rows:
            q, n = row['entry_prime'], row['selected_label_count']
            d = q-3-n
            amplitude = F(q-1, d)
            require(f'{tag}_root_{q}_minimum_complement', d >= 4
                    and F(row['reciprocal_tail'])/d == F(row['blocker_fee_upper']))
            # For j>=1: A(q)/q^j <= (1/4)q^(1-j)
            # <=(37/4)37^-j and <=3^-j; proof handles all j.
            require(f'{tag}_root_{q}_first_prefix', amplitude/q < F(1,4))
            saved.append(dict(entry_prime=q, selected_label_count=n, complement_denominator=d,
                              conditional_haar_density=amplitude,
                              original_root_fee=F(row['blocker_fee_upper'])))
        root_rows[tag] = saved
    require('finite_minimum_D_is_four',
            min(r['complement_denominator'] for rows in root_rows.values() for r in rows) == 4)
    require('unique_D_four_row',
            [(tag,r['entry_prime']) for tag,rows in root_rows.items() for r in rows
             if r['complement_denominator'] == 4] == [('3_23',41)])
    require('root_rectangle_tail_minimum_D', n0*n0+1 == 485 and n0*n0+1 >= 4)
    require('outside_prefix_comparisons', F(1,4) < F(1,3)
            and F(6,41) < F(1,3) and 6 < cap and 41 > 37)

    labels, moments, all_moment = method.moment_table(37, cap, boundary, require)
    rows = []
    for v in primes[1:]:
        fee, n, delta = method.optimum(v, moments)
        d = v-3-n
        haar_cap = F(v-1,d)/(1-delta)
        require(f'node_{v}_normalized_kernel', 0 <= n < v-3
                and 0 < delta <= F(1,2) and haar_cap <= 6
                and fee == moments[n]/(4*delta*(1-delta)*d*d))
        require(f'node_{v}_finite_optimum',
                all(fee <= moments[nn]
                    /(4*min(F(1,2),1-F(v-1,6*(v-3-nn)))
                      *(1-min(F(1,2),1-F(v-1,6*(v-3-nn))))*(v-3-nn)**2)
                    for nn in range(v-3) if 6*(v-3-nn)>v-1))
        rows.append(dict(node_prime=v, selected_label_count=n, complement_denominator=d,
                         threshold=delta, conditional_haar_density=haar_cap,
                         unselected_pair_moment=moments[n], node_violation_fee=fee))
    require('all_151_nonroot_rows', len(rows) == 151 and rows[0]['node_prime'] == 41
            and rows[-1]['node_prime'] == 967)
    finite = sum((row['node_violation_fee'] for row in rows), F())

    first_rectangle = F(3,2)*(1+cap*(F(3,36)+F(2,36**2)))
    second_rectangle = 3*cap*F(37,36)
    slope = first_rectangle+second_rectangle
    intercept = 2*first_rectangle+second_rectangle*F(19,18)
    require('exact_rectangle_coefficients', first_rectangle == F(4627,1728)
            and second_rectangle == F(1369,48)
            and slope == F(53911,1728) < 32 and intercept == F(15319,432) < 37)
    require('whole_tail_interval_boundary', 2*n0*n0+3 == boundary)
    require('whole_tail_uniform_factor', 32+F(37,n0) < 34)
    # The proof bounds each weighted interval by 170*3^-n, all n>=22.
    weighted_tail = F(510,2*3**n0)
    tail = weighted_tail/boundary
    total = finite+tail
    require('all_prime_nonroot_fee', total < F(1,250000))

    old_simple = F(old['consequence']['simple_extendible_head_lower'])
    old_exact = F(old['consequence']['extendible_head_lower'])
    beta = F(old['constants']['alpha'])*(1-F(old['constants']['c']))*F(old['constants']['early_pair_density'])
    require('unchanged_early_late_conversion', beta == F(46191477,720966400) and 0 < beta < 1)
    require('unchanged_inherited_reserve', old_exact > old_simple == F(31991,2048000000))
    simple = old_simple-F(1,250000)
    exact = old_exact-total
    require('early_source_positive', F(1,32000)-beta*total > 0)
    require('complete_shared_pair_network_reserve',
            exact > old_simple-total > simple > F(1,90000))
    result = dict(schema='shared-head-pair-forward-kernels-v1', sources=sources,
                  scope=dict(head='Report598 restrictions', roots='Any number of distinct outside nodes with the same two head parents; unchanged Report601 finite choices and rectangle tail',
                             nonroots='Increasing distinct outside primes, each with two fixed earlier parents and at least one outside parent; parents may come from different roots of this same head pair',
                             sharing='All nodes of one network share one head pair; different networks have disjoint outside nodes and no cross-network originals',
                             originals='Distinct full numerical labels, one globally fixed residue each, arbitrary finite heights; unique largest-prime owner',
                             ordinary='Report599 private trees with disjoint interiors; Type I and separate components unchanged',
                             source='One normalized forward law from product Haar on the head pair; root rows use selected-complement Haar, nonroot rows capped at six; no primary amplification',
                             excluded='Unrestricted head labels; multiple parent inventories at one node; different-head-pair network crossings; non-increasing network order', lean_verified=False),
                  constants=dict(root_minimum_D=4, reference_pair=(3,37), second_coordinate_cap=cap,
                                 nonroot_conditional_haar_density=6,beta=beta,
                                 inherited_simple_reserve=old_simple,inherited_exact_reserve=old_exact),
                  root_rows=root_rows,
                  moment_table=dict(all_label_pair_moment=all_moment,literal_prefix=labels,tail_moments=moments),
                  finite_rows=rows,finite_nonroot_fee=finite,
                  analytic_tail=dict(first_odd_node=boundary,rectangle_start=n0,
                                     selected_rectangle='0<=i,j<n, excluding unit',selected_count='n^2-1',
                                     threshold='1/2',conditional_haar_cap='at most4',
                                     first_rectangle_coefficient=first_rectangle,second_rectangle_coefficient=second_rectangle,
                                     moment_bound='(32n+37)3^-n',weighted_interval_bound='170*3^-n',
                                     weighted_bound=weighted_tail,unweighted_bound=tail),
                  consequence=dict(total_nonroot_fee=total,strictly_below=F(1,250000),
                                   exact_extendible_head_lower=exact,simple_extendible_head_lower=simple,
                                   strictly_greater_than=F(1,90000),full_density_lower='1/(90000 Q_off)'),
                  checks=checks,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(method.encode(result),indent=2)+'\n')
    print(json.dumps(method.encode(dict(checks=len(checks),root_rows=sum(map(len,root_rows.values())),
                                       nonroot_rows=len(rows),total_nonroot_fee=total,
                                       simple_final=simple,strictly_greater_than=F(1,90000)))))


if __name__ == '__main__':
    main()
