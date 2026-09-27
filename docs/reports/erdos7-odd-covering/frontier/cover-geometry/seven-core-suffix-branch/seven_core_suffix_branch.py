#!/usr/bin/env python3
"""Regenerate one pinned source branch and its variable-threshold certificate.

Input: an extraction of Schroeder's nine-prime-support edition 1.0.1.
The unchanged source verifier and C++ geometry enumerator run in temporary
storage. This is a counterexample to a fixed comparison certificate, not
an actual-query lower bound or an odd covering. No Lean is invoked.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import prod
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory


PINS = {
    'paper/main.tex': '73f78621a297650176cb796f763b9279eae9533efedbbb58405efc885ef41bb9',
    'checks/verify.py': 'e3296d181686c0f1925e755583fdc4df2ffeb2bacbc36a77a2396bbe3b4a9135',
    'checks/geometry.cpp': '8d7ecf1981a413daf2d3835ebe2c046b20f03010f7ce24f247bd357136e24f04',
    'certificate/integer_certificate.json': 'a1720cea93f30e04f31db6b49700a7d5c2d0fcfe9dff2f63ea2e3130b08629ac',
    'certificate/closing.json': '2fc48ecf06bc7ca256f7107648158fe92bff2052368b438267e6541e3eb07b1b',
}
CAPS = {11:F(5,3),13:F(3,2),17:F(2),19:F(9,5)}
NODE = (2,4,1,8,1,2,1,0,13)
PROJECTION = (1,4,7,14)
ETA165 = 14


def suffix_hinge(primes,threshold=12):
    low = {1:F(1)}
    for p in primes:
        cap = CAPS[p]
        updated = {}
        for m,w in low.items():
            for n in range(1,threshold):
                if m*n >= threshold:
                    break
                probability = 1-cap/p if n == 1 else cap*F(p-1,p**n)
                updated[m*n] = updated.get(m*n,F())+w*probability
        low = updated
    mean = prod((1+CAPS[p]/(p-1) for p in primes),start=F(1))
    return mean-threshold+sum(((threshold-m)*w for m,w in low.items()),F())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root',type=Path,required=True)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--cxx',default='c++')
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('The pinned external verifier uses assertions; run without -O.')
    checks = {}

    def need(name,predicate):
        if name in checks or not predicate:
            raise ValueError(name)
        checks[name] = True

    source = args.source_root.resolve()
    for name,digest in PINS.items():
        need('source_identity_'+name,sha256((source/name).read_bytes()).hexdigest() == digest)
    rows = json.loads((source/'certificate/closing.json').read_text())
    matched = [row for row in rows if row['state'] == 'A1' and row['eta'] == ETA165]
    need('unique_original_closing_row',len(matched) == 1)
    original = matched[0]
    with TemporaryDirectory(prefix='e7-seven-suffix-') as directory:
        work = Path(directory)
        (work/'checks').mkdir()
        (work/'cache').mkdir()
        for name in ('checks/verify.py','checks/geometry.cpp'):
            shutil.copy2(source/name,work/name)
        shutil.copy2(source/'LICENSES/MIT.txt',work/'MIT.txt')
        subprocess.run([args.cxx,'-std=c++17','-O3',str(work/'checks/geometry.cpp'),
                        '-o',str(work/'checks/geometry')],check=True)
        spec = importlib.util.spec_from_file_location('pinned_seven_suffix_source',work/'checks/verify.py')
        verifier = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(verifier)
        original_ratios = verifier.RATIOS
        verifier.RATIOS = tuple(sorted({F(t,m) for t in range(1,13) for m in range(1,t)}))
        need('extended_geometry_ratios',len(verifier.RATIOS) == 45
             and set(original_ratios) <= set(verifier.RATIOS))
        reserve = verifier.reserve(NODE)
        spatial = verifier.spatial(NODE,PROJECTION)
        fixed11 = verifier.fixed165(NODE,PROJECTION,ETA165)
        stages = (spatial[0],fixed11)+spatial[2:]
        need('source_fixed165_cost',fixed11 == F(original['cost']))
        need('source_available_mass',reserve-sum((x for i,x in enumerate(stages) if i != 1),F())
             == F(original['available']))
        env = verifier.envelope(NODE)
        killed = verifier.envelope(NODE,'ordinary',PROJECTION,True)
        full_dist,full_mean = verifier.distributions()[5]
        skip_dist,skip_mean = verifier.distributions(True)[5]
        threshold_numerators = []
        for t in range(1,13):
            ordinary = verifier.expectation(env,full_dist,full_mean,t)
            old_zero = verifier.expectation(env,skip_dist,skip_mean,t)
            new_zero = verifier.expectation(killed,skip_dist,skip_mean,t)
            saved = (11*old_zero-new_zero)/14
            need('nonnegative_spatial_saving_'+str(t),saved >= 0)
            numerator = ordinary-saved
            source_style = verifier.up(ordinary/(22-t))-saved/(22-t)
            need('rounding_direction_'+str(t),
                 numerator/(22-t) <= source_style < numerator/(22-t)+F(1,10**10))
            if t == 12:
                need('original_final_stage_recovered',source_style == stages[5])
            threshold_numerators.append((numerator,source_style))
        need('fresh_geometry_batches',verifier.GENERATED == 24)
        need('geometry_integer_queries',verifier.INTEGER_QUERIES == 10152)
    primes = tuple(CAPS)
    zeta = {boundary:suffix_hinge(primes[i:])
            for i,boundary in enumerate((7,)+primes)}
    eta = {q:(zeta[before]-zeta[q])/CAPS[q]
           for before,q in zip((7,11,13,17),primes)}
    for q in primes:
        need('positive_cap_slope_'+str(q),eta[q] > 0)
    need('terminal_suffix_zero',zeta[19] == 0)
    need('terminal_cap_slope',eta[19] == F(1,2096824660167942))
    need('penultimate_suffix',zeta[17] == F(1,1164902588982190))
    target = F(27,49)
    need('target_lambda',11+target == F(566,49) and target >= zeta[7])
    denominator = reserve-sum(stages[:5],F())
    need('positive_old_certificate',denominator > stages[5] > 0)
    base = target*denominator-10*stages[5]
    suffix_credit = sum((zeta[q]*stages[i] for i,q in enumerate((7,)+primes)),F())
    cap_credit = 135*sum((eta[q]*CAPS[q] for q in primes),F())
    need('cap_credit_telescopes',cap_credit == 135*zeta[7])
    optimistic = base+suffix_credit+cap_credit
    need('fixed_ledger_certificate_fails',optimistic < -33)
    threshold_rows = []
    for t,(numerator,source_style) in enumerate(threshold_numerators,1):
        zt = {boundary:suffix_hinge(primes[i:],t)
              for i,boundary in enumerate((7,)+primes)}
        slopes = {q:(zt[before]-zt[q])/CAPS[q]
                  for before,q in zip((7,11,13,17),primes)}
        lam = F(615,49)-t
        need('threshold_coefficient_condition_'+str(t),lam >= zt[7])
        need('threshold_suffix_order_'+str(t),zt[19] == 0
             and all(x >= 0 for x in slopes.values()))
        deletion = sum((zt[q]*stages[i] for i,q in enumerate((7,)+primes)),F())
        cap = 135*sum((slopes[q]*CAPS[q] for q in primes),F())
        need('threshold_slack_telescopes_'+str(t),cap == 135*zt[7])
        margin = lam*denominator-numerator+deletion+cap
        need('integer_threshold_fails_'+str(t),margin < F(-7,4))
        threshold_rows.append(dict(t=t,beta=22-t,dummy_cap=F(22,22-t),
            lambda_target=lam,H_upper_exact=numerator,L23_unrounded=numerator/(22-t),
            L23_source_style=source_style,zeta=zt,cap_slopes=slopes,
            deletion_credit_B7_zero=deletion,generous_cap_credit=cap,optimistic_margin=margin))
    intervals = []
    for left,right in zip(threshold_rows,threshold_rows[1:]):
        upper = (left['lambda_target']*denominator-right['H_upper_exact']
                 +left['deletion_credit_B7_zero']+left['generous_cap_credit'])
        need('real_threshold_interval_fails_'+str(left['t']),upper < F(-7,4))
        intervals.append(dict(left_open=left['t'],right_closed=right['t'],optimistic_upper=upper))
    need('largest_interval_upper',max(row['optimistic_upper'] for row in intervals)
         == intervals[0]['optimistic_upper'])
    result = dict(
        scope='Pinned finest A1/eta14 early stage envelopes and the retained complete comparison fail the 566/49 query certificate at every real final threshold in [1,12], even with B7=0 and all four ordinary cap-slack terms at generous upper bounds. The report supplies the half-open interval argument. No actual query lower bound or unrestricted-cover conclusion.',
        source_doi='10.5281/zenodo.22759614',source_edition='1.0.1',
        source_artifact_sha256=PINS,node=NODE,projection=PROJECTION,eta165=ETA165,
        reserve=reserve,stage_upper=dict(zip((7,11,13,17,19,23),stages)),
        original_closing_cost=F(original['cost']),original_closing_available=F(original['available']),
        D7=denominator,old_closing_surplus=denominator-stages[5],zeta=zeta,cap_slopes=eta,
        target_lambda=target,base=base,optimistic_suffix_credit_B7_zero=suffix_credit,
        all_cap_slacks_generous_maximum=cap_credit,optimistic_total=optimistic,
        physical_schedule=verifier.T[:5],physical_caps=verifier.CAP[:5],
        extended_geometry_ratios=verifier.RATIOS,threshold_rows=threshold_rows,
        real_threshold_intervals=intervals,
        fresh_geometry_batches=24,geometry_integer_queries=10152,
        checks=checks,check_count=len(checks),lean_certification=False)
    args.output.write_text(json.dumps(result,default=str,indent=2)+'\n')
    print('PASS',len(checks),'checks;24 fresh geometry batches;10152 integer queries')
    print('optimistic_certificate',optimistic,float(optimistic))
    print('all_real_threshold_interval_upper',float(intervals[0]['optimistic_upper']))


if __name__ == '__main__':
    main()
