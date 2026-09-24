#!/usr/bin/env python3
"""Exact actual survival for the actual profile-threshold counterexample.
Enumerates finite Q-channel atoms, never the original CRT period.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import json,hashlib,argparse
Q=(5,7,11,13,17,19);H=8;K=4
rows={q:{'denominator':(q-2)*q**H+1,'channel_numerator':q**H-q**(H-K),'digits':tuple(range(2,min(q-1,10)+1))} for q in Q}
# 5 and7 truncate their displayed digits at4/6; all four late primes use2,...,10.
for q,row in rows.items():row['remainder_numerator']=row['denominator']-len(row['digits'])*row['channel_numerator']
D=prod(rows[q]['denominator'] for q in Q)
counts={'zero':0,'base':0,'extra5':0,'missing5':0,'missing5_extra7':0,'missing7':0}
root_counts={'zero':2,'base':1458,'extra5':729,'missing5':366,'missing5_extra7':363,'missing7':363}
all_weight=0;n_atoms=0
for code in product(*((0,)+rows[q]['digits'] for q in Q)):
    n_atoms+=1
    mass=prod(rows[q]['channel_numerator'] if d else rows[q]['remainder_numerator'] for q,d in zip(Q,code))
    all_weight+=mass
    late=code[2:]
    old_bad=late.count(8)>=2 or late.count(9)>=3 or late==(10,10,10,10)
    if old_bad:continue
    counts['zero']+=mass
    mixed_bad=any(sum(d==min(size+1,q-1) for q,d in zip(Q,code))>=size for size in range(2,7))
    if mixed_bad:continue
    rest=all(d!=2 for d in code[2:])
    if not rest:continue
    if code[1]!=2:
        counts['missing5']+=mass
        if code[1]!=3:counts['missing5_extra7']+=mass
    if code[0]!=2:counts['missing7']+=mass
    if code[0]!=2 and code[1]!=2:
        counts['base']+=mass
        if code[0]!=3:counts['extra5']+=mass
checks={}
def check(k,x):
    if k in checks or not x:raise RuntimeError(k)
    checks[k]=True
check('channel_atom_count',n_atoms==240000)
check('all_channel_weights_normalize',all_weight==D)
check('all_remainders_nonnegative',all(rows[q]['remainder_numerator']>=0 for q in Q))
profiles={name:F(n,D) for name,n in counts.items()}
actual=sum((F(root_counts[name],3281)*v for name,v in profiles.items()),F())
B5=F(19132074022251234990036997833948759259,18473247078046657922374787501704265625)
target=51*B5/310
G=F(11896353657900110917305940184050970099978148851942853,69878103243070953218900866574163339591956220339720217)
check('actual_survival_exceeds_failed_certificate',actual>G)
check('actual_survival_exceeds_target',actual>target)
query=5+B5/actual
check('same_uniform_law_query_crosses',query<F(565,51))
result={'scope':__doc__,'channel_atom_count':n_atoms,'coordinate_atoms':rows,'root_region_counts':root_counts,
        'exact_conditional_survival':profiles,'actual_pure_source_survival':actual,'actual_decimal':float(actual),
        'profile_G':G,'actual_minus_G':actual-G,'actual_minus_G_decimal':float(actual-G),'target':target,
        'uniform_survivor_query_bound':query,'query_bound_decimal':float(query),'passed_checks':len(checks),'checks':checks}
def enc(v):
    if isinstance(v,F):return str(v)
    raise TypeError(type(v).__name__)
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=parser.parse_args()
output=args.output;output.write_text(json.dumps(result,default=enc,indent=2)+'\n')
for name,v in profiles.items():print(name,str(v),float(v))
print(json.dumps({k:result[k] for k in ('channel_atom_count','passed_checks','actual_decimal','actual_minus_G_decimal','query_bound_decimal')},indent=2))
print('actual='+str(actual));print('json_sha256='+hashlib.sha256(output.read_bytes()).hexdigest())
