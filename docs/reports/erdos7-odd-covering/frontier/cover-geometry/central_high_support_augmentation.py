#!/usr/bin/env python3
"""Exact Report597 + all 800 high-support central-square labels.

Consumes the completed Report597 JSON; does not import or run its producer.
The inherited full certificate is identified and checked for consistency,
not rerun here. All new arithmetic and inventories use stdlib Fractions.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from math import comb, prod
from pathlib import Path

P=(3,5,7,11,13,17,19)
TAIL=(23,29,31)
CONTROLS=(F(2,5),F(9,20),F(1,2))
CHECKS={}


def check(name, condition):
    CHECKS[name]=bool(condition)
    if not condition:
        raise ValueError(name)


def sha(data):
    return sha256(data).hexdigest()


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [encode(v) for v in value]
    return value


def support(exps):
    return sum(e>0 for e in exps)


def old_allowed(exps):
    return support(exps)<=1 or max(exps)>=3 or (exps[0]<=1 and exps[1]<=1)


def new_label(exps):
    return max(exps)==2 and (exps[0]==2 or exps[1]==2) and support(exps)>=5


def numerical(exps):
    return prod(p**e for p,e in zip(P,exps))


def raw_cap(exps):
    return prod(F(2,3**e) if p==3 else F(1,p-1) if e==1 else F(1,(p-2)*p**(e-1)) for p,e in zip(P,exps) if e)


def factor_back(n):
    out=[]
    for p in P:
        e=0
        while n%p==0:
            n//=p
            e+=1
        out.append(e)
    check('all_numerical_labels_P_smooth',n==1)
    return tuple(out)


def polynomial_mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j]+=x*y
    return c


def independent_cap_polynomial():
    # Count support by x; central square must occur at 3 or 5.
    c31,c32,c51,c52=F(2,3),F(2,9),F(1,4),F(1,15)
    full=polynomial_mul([1,c31+c32],[1,c51+c52])
    no_square=polynomial_mul([1,c31],[1,c51])
    poly=[x-y for x,y in zip(full,no_square)]
    for p in P[2:]:
        poly=polynomial_mul(poly,[1,F(1,p-1)+F(1,p*(p-2))])
    return poly


def inherited(source):
    raw=source.read_bytes()
    obj=json.loads(raw)
    check('inherited_all_recorded_checks_true',bool(obj['checks']) and all(v is True for v in obj['checks'].values()))
    check('inherited_complete_case_count',obj['cases']==358963200)
    check('inherited_complete_coverage_check',obj['checks'].get('complete_coverage') is True)
    check('inherited_source_hashes_present',len(obj['source_sha256'])==5)
    for name,expected in obj['source_sha256'].items():
        check('inherited_source_sha256_'+name,sha((source.parent/name).read_bytes())==expected)
    K=F(obj['raw_tail_lower'])
    old_haar=F(obj['haar_lower'])
    check('inherited_positive_gate_and_density',K>0 and old_haar>0)
    # c and D are encoded by the coefficient identities and density relation;
    # the current source JSON does not have dedicated c/D fields.
    check('inherited_192_coefficients',len(obj['coefficients'])==192)
    candidates=set()
    for row in obj['coefficients']:
        loss,weighted,combined=map(F,(row['remaining_loss'],row['weighted_query'],row['combined']))
        if weighted!=loss:
            candidates.add((combined-loss)/(weighted-loss))
        else:
            check('inherited_equal_loss_query_row',combined==loss)
    check('unique_continuation_c',len(candidates)==1)
    c=candidates.pop()
    check('continuation_c_in_unit_interval',0<c<1)
    check('all_coefficient_identities',all(F(r['combined'])==(1-c)*F(r['remaining_loss'])+c*F(r['weighted_query']) for r in obj['coefficients']))
    g=v=F(1)
    for q,delta in zip(TAIL,CONTROLS):
        v-=g/(4*delta*(1-delta)*(q-1)**2)
        g*=1+F(3*q-1,(q-1)**2)/(1-delta)
    check('independent_continuation_recurrence',c==1-v)
    multiplier=prod(1/(1-d) for d in CONTROLS)
    check('continuation_density_multiplier',multiplier==F(200,33))
    D=K/(multiplier*old_haar)
    check('independent_product_source_density',D==2*prod(F(p,p-2) for p in P[1:]))
    check('inherited_constants_match_current597',K==F(548601319573,131072000000000) and c==F(1084133,201247200) and D==F(3458,405))
    return K,c,D,multiplier,dict(file=source.name,sha256=sha(raw),source_hashes=obj['source_sha256'],inherited_checks=len(obj['checks']),inherited_cases=obj['cases'],full_scan_rerun=False,constant_recovery='K from raw_tail_lower; c from all combined coefficient identities; D from the recorded Haar consequence. Both c and D are independently recomputed.')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,default=Path(__file__).with_name('outside_pair_shearer_profile.json'))
    ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=ap.parse_args()
    K,c,D,multiplier,source=inherited(args.source)
    added=[];remaining=[];all_missing=[];all_numbers=set()
    for exps in product(range(3),repeat=7):
        n=numerical(exps)
        check('numerical_labels_distinct',n not in all_numbers)
        all_numbers.add(n)
        check('numerical_factorization_roundtrip',factor_back(n)==exps)
        if not old_allowed(exps):
            record=dict(modulus=n,exponents=exps,support=support(exps),source_cap=raw_cap(exps))
            all_missing.append(record)
            if new_label(exps):
                added.append(record)
            else:
                remaining.append(record)
    for rows in (added,remaining,all_missing):
        rows.sort(key=lambda row:row['modulus'])
    check('full_depth_two_inventory',len(all_numbers)==3**7)
    check('all_added_are_new_to597',all(not old_allowed(r['exponents']) for r in added))
    check('all_added_match_natural_subclass',all(new_label(r['exponents']) for r in added))
    check('800_new_labels',len(added)==800)
    check('1213_original_missing_central_labels',len(all_missing)==1213)
    check('413_remaining_central_labels',len(remaining)==413)
    check('disjoint_complete_central_partition',{r['modulus'] for r in added}.isdisjoint(r['modulus'] for r in remaining) and {r['modulus'] for r in added+remaining}=={r['modulus'] for r in all_missing})
    check('remaining_exact_low_support_class',all(max(r['exponents'])==2 and (r['exponents'][0]==2 or r['exponents'][1]==2) and 2<=r['support']<=4 for r in remaining))
    counts={k:sum(r['support']==k for r in added) for k in (5,6,7)}
    formula={k:sum(comb(2,j)*comb(5,k-j)*(2**j-1)*2**(k-j) for j in (1,2) if 0<=k-j<=5) for k in (5,6,7)}
    check('independent_combinatorial_support_counts',counts==formula=={5:400,6:304,7:96})
    B=sum((r['source_cap'] for r in added),F(0))
    poly=independent_cap_polynomial()
    check('independent_generating_polynomial_cap',B==sum(poly[5:]))
    check('supportwise_cap_polynomial',all(sum((r['source_cap'] for r in added if r['support']==k),F(0))==poly[k] for k in (5,6,7)))
    check('exact_800_cap',B==F(2931380251141127,2284918571295360000))
    new_K=K-(1-c)*B
    new_haar=new_K/(multiplier*D)
    check('simultaneous_800_gate_positive',new_K>0)
    check('simultaneous_800_density_gt_1_18000',new_haar>F(1,18000))
    check('density_strictly_less_than_old_consequence',new_haar<K/(multiplier*D))
    old_remaining_cap=sum((r['source_cap'] for r in remaining),F(0))
    result=dict(schema='central-high-support-augmentation-v1',source=source,scope=dict(head_primes=P,unrestricted_continuation_primes=TAIL,new_class='max exponent = 2; v3 = 2 or v5 = 2; at least five prime divisors',resulting_mixed_head_condition='max exponent >= 3 OR (v3 <= 1 AND v5 <= 1) OR support cardinality >= 5',all_residues='arbitrary and globally fixed',all_original_and_query_heights='unbounded',transport='Any ten ordered odd primes, preserving exponent vectors and coordinate roles',excluded_claims=['The 413 remaining max-exponent-two central labels','Arbitrary additional support primes','Lean verification','Unrestricted Erdos7']),constants=dict(inherited_gate=K,continuation_c=c,source_density_D=D,continuation_density_multiplier=multiplier,available_raw_cap_budget=K/(1-c)),deletion_lemma=dict(common_submeasure='eta_new = eta_597 restricted outside the union of all present additional original classes',raw_mass_removed_upper=B,unit_included=True,gate_cost=(1-c)*B,query_maxima_monotone=True,homogeneous_moment_drop_at_least_removed_mass=True,same_actual_product_source=True),inventory=dict(added_count=len(added),added_counts_by_support=counts,added=added,remaining_count=len(remaining),remaining_counts_by_support={k:sum(r['support']==k for r in remaining) for k in (2,3,4)},remaining=remaining,remaining_source_cap=old_remaining_cap),cap_polynomial=poly,consequence=dict(raw_cap_sum=B,new_gate=new_K,haar_lower=new_haar,strictly_greater_than=F(1,18000),new_gate_decimal=float(new_K),haar_decimal=float(new_haar)),checks=CHECKS,producer_sha256=sha(Path(__file__).read_bytes()))
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(output=str(args.output),new_labels=len(added),remaining=len(remaining),cap=B,gate=new_K,haar=new_haar,strictly_gt='1/18000',checks=len(CHECKS)))))


if __name__=='__main__':
    main()
