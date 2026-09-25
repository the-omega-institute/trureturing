#!/usr/bin/env python3
"""Exact reserve for one global increasing two-parent outside network.

Early roots are sampled before the existing head-only physical continuation.
All remaining entries then share one normalized forward law. This certificate
checks the retained root/nonroot budgets and the small cost of not restricting
early blockers; the accompanying proof supplies the lifting and gluing steps.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


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
        data = json.loads(raw)
        require(name+'_checks_true', bool(data['checks'])
                and all(v is True for v in data['checks'].values()))
        fingerprint = sha256(path.with_suffix('.py').read_bytes()).hexdigest()
        require(name+'_producer_fingerprint', fingerprint == data['producer_sha256'])
        sources[name] = dict(sha256=sha256(raw).hexdigest(),producer_sha256=fingerprint)
        return data

    staged = load('staged_two_parent_attachment.json')
    network = load('shared_head_pair_forward_kernels.json')
    alpha = F(staged['constants']['alpha'])
    density = 1/alpha
    c = F(staged['constants']['c'])
    gate = F(staged['constants']['inherited_gate'])
    early = F(staged['fee_tables']['3_5']['total_fee'])
    late = F(staged['fee_tables']['3_23']['total_fee'])
    ordinary = F(staged['consequence']['ordinary_attachment_fee'])
    fee = F(network['consequence']['total_nonroot_fee'])
    pair_cap = F(staged['constants']['early_pair_density'])
    require('actual_head_density', alpha == F(2673,138320) and density == F(138320,2673)
            and density == F(staged['constants']['density_D'])*F(staged['constants']['continuation_multiplier'])
            and density > 1)
    require('homogeneous_head_controls', c == F(1084133,201247200)
            and gate == F(26345885990886052732242307711,9055182074115772514304000000000))
    require('root_budget_bounds', pair_cap == F(10,3)
            and early < F(1,2600) and late < F(1,125000))
    require('ordinary_budget', ordinary == F(1,131072))
    require('outside_prefix_constants', network['constants']['root_minimum_D'] == 4
            and F(network['constants']['second_coordinate_cap']) == F(37,4)
            and network['constants']['nonroot_conditional_haar_density'] == 6
            and F(1,4) < F(1,3) and F(6,41) < F(1,3))
    finite = sum((F(r['node_violation_fee']) for r in network['finite_rows']),F())
    tail = F(network['analytic_tail']['unweighted_bound'])
    require('entire_nonroot_budget', len(network['finite_rows']) == 151
            and finite == F(network['finite_nonroot_fee'])
            and tail == F(510,2*3**22*971) and finite+tail == fee < F(1,250000))
    for row in network['finite_rows']:
        v = row['node_prime']
        local = F(row['node_violation_fee'])
        require(f'node_{v}_single_head_density_payment', alpha*density*local == local)
    require('tail_single_head_density_payment', alpha*density*tail == tail)

    raw = gate-pair_cap*early-density*(late+ordinary+fee)
    exact = alpha*raw
    lost_unit_gain = alpha*c*pair_cap*early
    simple_lost_unit_gain = alpha*c/F(780)
    inherited_exact = F(staged['consequence']['extendible_head_lower'])
    inherited_simple = F(staged['consequence']['simple_extendible_head_lower'])
    require('same_source_budget_identity', exact == inherited_exact-lost_unit_gain-fee)
    require('early_unit_gain_bound', 0 < lost_unit_gain < simple_lost_unit_gain
            == F(3252399,24368664320000))
    simple = inherited_simple-simple_lost_unit_gain-F(1,250000)
    require('inherited_reserve', inherited_exact > inherited_simple == F(31991,2048000000))
    require('global_network_positive_mass', raw > 0 and exact > simple)
    require('global_network_simple_reserve', simple == F(447881975781,38989862912000000)
            and simple > F(1,90000))

    result = dict(schema='global-two-parent-forward-kernels-v1',sources=sources,
                  scope=dict(head='Report598 ten-prime head restriction',
                             outside='One arbitrary finite increasing network; each distinct v>=37 has two fixed distinct parents among all ten head coordinates and smaller outside entries',
                             roots='All two-head-parent entries allowed, across all head pairs; early roots are exactly those with both parents in P0',
                             nonroots='At least one outside parent, hence v>=41; all cross-root, cross-head-pair and early-late connections allowed',
                             sampling='First all early roots, then the head-only 23/29/31 physical continuation, then remaining outside entries in numerical order',
                             source='One unnormalized joint law from actual eta on P0; no early exterior blocker restriction and no intermediate survival conditioning',
                             ordinary='Report599 disjoint private block trees at entries; Type I head attachments and separate components unchanged',
                             originals='Distinct full numerical labels, one arbitrary globally fixed residue each, arbitrary finite heights, unique largest-prime owner',
                             excluded='Unrestricted head labels; multiple parent inventories at one owner; non-increasing parent assignments; additional crossings through ordinary private interiors',lean_verified=False),
                  constants=dict(alpha=alpha,full_head_density=density,continuation_c=c,
                                 inherited_gate=gate,early_root_pair_density=pair_cap,
                                 root_minimum_D=4,outside_reference=(3,37),second_coordinate_cap=F(37,4),
                                 nonroot_conditional_haar_density=6),
                  fees=dict(early_root=early,late_root=late,ordinary=ordinary,
                            finite_nonroot=finite,analytic_nonroot_tail=tail,total_nonroot=fee,
                            lost_early_unit_gain=lost_unit_gain,simple_lost_early_unit_gain=simple_lost_unit_gain),
                  consequence=dict(raw_good_mass_lower=raw,exact_extendible_head_lower=exact,
                                   simple_extendible_head_lower=simple,strictly_greater_than=F(1,90000),
                                   full_density_lower='1/(90000 Q_off)'),
                  checks=checks,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks),raw_good_mass=raw,
                                lost_early_unit_gain_upper=simple_lost_unit_gain,
                                simple_final=simple,strictly_greater_than=F(1,90000)))))


if __name__ == '__main__':
    main()
