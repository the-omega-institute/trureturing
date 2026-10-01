#!/usr/bin/env python3
"""Exact consumer of the uniform shared-deficit depth-two source certificate.

The full comparison is the paired C++ producer. This consumer independently
checks its minimizing endpoint by the direct cancelled pair-energy formula,
then computes the complete 1300 tail. No Lean verification is claimed.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial, prod
from pathlib import Path
import argparse
import importlib.util
import json


def need(ok,message):
    if not ok:raise ValueError(message)


def library():
    path=Path(__file__).with_name('uniform_depth2_source.py')
    spec=importlib.util.spec_from_file_location('depth_two_baseline',path)
    need(spec is not None and spec.loader is not None,'baseline source module')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def direct_response(base,layout):
    primes=base.P
    weights=tuple(F(x,sum(base.WEIGHTS))for x in base.WEIGHTS)
    caps=tuple(F(1,p-2)for p in primes)
    star=tuple(tuple(1-caps[i]*(int((l>=2)==bool(r))+int(l==t))for l in range(5))for i,(r,t)in enumerate(layout))
    roles=tuple(tuple(1+int((l>=2)==bool(r))+int(l==t)for l in range(5))for r in range(2)for t in range(5))
    supports=tuple(s for s in range(128)if s.bit_count()>=2)
    pairs=tuple((s,t)for s,t in combinations(supports,2)if not s&t)
    degree={s:sum(s in pair for pair in pairs)for s in supports}
    rows={s:tuple(weights[l]*prod(caps[i]if s>>i&1 else star[i][l]for i in range(7))for l in range(5))for s in range(128)}
    first={s:tuple(sum(rows[s][l]*c[l]for l in range(5))for c in roles)for s in supports}
    maximum={s:max(first[s])for s in supports}
    mass=sum(rows[0]);zero=sum(maximum[s]for s in supports if not degree[s])
    pair_energy=F(0);credit=F(0);positive=0
    for s,t in pairs:
        pair=tuple(tuple(sum(rows[s|t][l]*cs[l]*ct[l]for l in range(5))for ct in roles)for cs in roles)
        low=min(min(x)for x in pair)
        energy=min(pair[i][j]-first[s][i]/degree[s]-first[t][j]/degree[t]for i in range(10)for j in range(10))
        gain=energy+maximum[s]/degree[s]+maximum[t]/degree[t]-low
        need(gain>=0,'nonnegative shared-deficit credit')
        pair_energy+=energy;credit+=gain;positive+=gain>0
    triple=F(0)
    triple_coeff=tuple(tuple(prod(c[l]for c in cs)for l in range(5))for cs in product(roles,repeat=3))
    for s in supports:
        count=base.block_partitions(s.bit_count(),3)
        if count:triple+=count*max(sum(rows[s][l]*c[l]for l in range(5))for c in triple_coeff)
    result=mass-zero+pair_energy-triple
    baseline,_=base.response(layout)
    need(result==baseline+credit,'direct affine-pair cancellation')
    need(len(pairs)==546 and tuple(sorted(set(degree.values())))==(0,1,4,11,26),'support degree inventory')
    return dict(mass=result,baseline=baseline,credit=credit,positive_pairs=positive,
                pair_count=len(pairs),zero_degree_supports=sum(d==0 for d in degree.values()))


def calculate(enumeration):
    need(enumeration['complete'] is True and enumeration['raw_vertices']==10000000 and
         enumeration['visits']==929408,'complete star-vertex comparison')
    need(enumeration['refined']==683 and enumeration['cutoff_denominator']==100,
         'all omitted vertices retain baseline at least one hundredth')
    need(enumeration['old_min_numerator']==2263036 and
         enumeration['refined_min_numerator']==4431234914 and
         enumeration['refined_denominator']==682296615000,'certified refined minimum')
    base=library();layout=tuple(map(tuple,enumeration['layout']))
    need(layout==base.MINIMIZER,'same canonical minimizing star profile')
    direct=direct_response(base,layout)
    mass=F(2215617457,341148307500)
    need(direct['mass']==mass and mass<F(1,100),'global minimum lies in explicitly refined domain')
    need(direct['baseline']==F(1131518,596413125),'retained baseline minimum')
    fourth=F(1423,25)*prod(1+F(p-1,p-2)*base.a4(p)for p in base.P)
    need(fourth==F(83957323825075240180209923,277054053281280000000),'same raw fourth envelope')
    B,ell,r=1300,6,21
    need(B>=286 and ell>=4 and 3**ell<=B and 4*ell>=r,'analytic tail range')
    tau=F(21609,10240)*F(73,71)**r*F(B,(B-1)**4)*sum(
        F(factorial(r),factorial(r-j)*(3*ell)**j)for j in range(r+1))
    final=mass-fourth*tau
    need(final>F(1,3000),'uniform source survives complete 1300 tail')
    no3=base.P+(29,);b=tuple(F(1,p-2)for p in no3)
    no3mass=2+sum(b)-prod(1+x for x in b)
    no3fourth=prod(1+F(p-1,p-2)*base.a4(p)for p in no3)
    no3final=no3mass-no3fourth*tau
    need(no3final>F(1,3000),'missing-three branch at the same cutoff')
    return dict(status='exact_arithmetic_passed_not_Lean',
                source_mass_lower=mass,source_mass_decimal=float(mass),
                minimizer=layout,direct=direct,
                raw_fourth_upper=fourth,tail=dict(cutoff=B,ell=ell,delta=F(2,7),growth=r,factor=tau),
                final_mass_lower=final,final_mass_decimal=float(final),simple_lower=F(1,3000),
                missing_three=dict(mass=no3mass,fourth=no3fourth,final=no3final,final_decimal=float(no3final)),
                enumeration=dict(raw_vertices=10000000,canonical_profiles=929408,refined_profiles=683,
                                 skipped_baseline_lower=F(1,100)),
                scope='At most eight actual support primes at most1300; only originals wholly supported there need v3<=2. All tail-bearing originals retain unrestricted finite heights, mixed supports and globally fixed phases.',
                proof_boundary='Uses Report789 actual source, one-clique Shearer premise and prefix transport, the shared-deficit cancellation and separate concavity proved in Report791, and Report734 analytic prime-tail input. The finite comparison does not establish those ordinary mathematical premises by itself.')


def encode(x):
    if isinstance(x,F):return str(x)
    raise TypeError(type(x).__name__)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--enumeration',type=Path,default=Path(__file__).with_name('uniform_depth2_pair_source_enumeration.json'))
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    enumeration=json.loads(args.enumeration.read_text(encoding='utf-8'))
    result=json.loads(json.dumps(calculate(enumeration),default=encode))
    if args.write_result:
        args.write_result.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    else:
        recorded=json.loads(Path(__file__).with_name('uniform_depth2_pair_source.json').read_text(encoding='utf-8'))
        need(result==recorded,'retained exact result matches fresh calculation')
        print('uniform depth-two pair source: exact arithmetic passed')


if __name__=='__main__':main()
