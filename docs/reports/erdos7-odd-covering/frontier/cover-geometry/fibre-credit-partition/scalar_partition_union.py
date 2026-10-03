"""Exact set-partition optimization of raw-budget scalar row unions.

Only consumes the stored four-flip budgets; no old checker is rerun.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import prod
from pathlib import Path

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',required=True)
ap.add_argument('--endpoint',required=True)
ap.add_argument('--output',required=True)
args=ap.parse_args()
raw=Path(args.input).read_bytes()
endpoint_raw=Path(args.endpoint).read_bytes()
data=json.loads(raw)
ep=json.loads(endpoint_raw)
checks=0
def need(ok,message):
    global checks
    checks+=1
    if not ok:
        raise ValueError(message)
need(ep['input_sha256']==sha256(raw).hexdigest(),'Endpoint binds the exact original inventory')
need(ep['flipped_cofactors']==[77,91,119,133],'Declared four-flip endpoint')
need(data['primes']==[5,7,11,13,17,19,23,29,31,37,41],'Reference prime profile')

def optimize(group):
    qs=sorted(map(int,group['T']))
    a=[1-F(group['T'][str(q)]) for q in qs]
    k=group['k']
    rho=F(group['rho'])
    P=prod(a,start=F(1))
    need(all(0<z<=1 for z in a),'Strictly subunit raw budgets')
    need(P==F(group['P']) and P>=rho**k and 0<=rho<1 and k>=1,'Fractional-row transfer threshold')
    residual=[F(1)]*(1<<len(qs))
    for mask in range(1,1<<len(qs)):
        lowbit=mask & -mask
        residual[mask]=residual[mask^lowbit]*a[lowbit.bit_length()-1]
    count=0
    by_size={}
    optimum=None
    optimal_masks=None
    ties=0
    def visit(index,blocks):
        nonlocal count,optimum,optimal_masks,ties
        if index==len(qs):
            count+=1
            by_size[len(blocks)]=by_size.get(len(blocks),0)+1
            cost=sum((residual[m] for m in blocks),F(k-len(blocks)))
            if optimum is None or cost<optimum:
                optimum=cost
                optimal_masks=tuple(blocks)
                ties=1
            elif cost==optimum:
                ties+=1
            return
        bit=1<<index
        for j in range(len(blocks)):
            blocks[j]|=bit
            visit(index+1,blocks)
            blocks[j]^=bit
        if len(blocks)<k:
            blocks.append(bit)
            visit(index+1,blocks)
            blocks.pop()
    visit(0,[])
    # A separate Stirling-number recurrence checks exhaustive symmetry
    # reduction: each unlabeled partition into at most k nonempty blocks.
    stirling=[0]*(k+1)
    stirling[0]=1
    for _ in qs:
        stirling=[0]+[j*stirling[j]+stirling[j-1] for j in range(1,k+1)]
    need(by_size=={j:stirling[j] for j in range(1,k+1) if stirling[j]},'Every restricted-growth partition counted once')
    need(count==sum(stirling),'Total exhaustive partition count')
    blocks=[[q for i,q in enumerate(qs) if mask>>i & 1] for mask in optimal_masks]
    need(sorted(q for block in blocks for q in block)==qs,'Optimal partition uses every coordinate once')
    scalar=F(k)-optimum
    pref=F(group['prefactor'])
    union=pref*scalar
    radical_lo=F(group['union_formula_lower'])
    radical_hi=F(group['union_formula_upper'])
    need(union<=radical_hi,'Exact scalar optimum respects old radical upper bound')
    return {'prime':group['prime'],'k':k,'rho':str(rho),'P':str(P),
            'raw_T':group['T'],'partition_count':count,'counts_by_nonempty_blocks':by_size,
            'optimal_partition':blocks,'optimal_partition_ties_mod_row_permutation':ties,
            'block_residuals':[str(residual[m]) for m in optimal_masks],
            'empty_blocks':k-len(optimal_masks),'minimum_residual_sum':str(optimum),
            'scalar_maximum':str(scalar),'prefactor':str(pref),
            'actual_group_upper':str(union),'actual_group_upper_decimal':float(union),
            'gain_over_radical_lower':str(radical_lo-union),
            'gain_over_radical_upper':str(radical_hi-union),
            'gain_over_radical_interval_decimal':[float(radical_lo-union),float(radical_hi-union)]}

g5=optimize(ep['group5'])
g7=optimize(ep['additional_disjoint_group7'])
old=F(ep['old_endpoints_by_root']['1'])
new5=old+F(ep['group5']['old_charge'])-F(g5['actual_group_upper'])
new_both=new5+F(ep['additional_disjoint_group7']['old_charge'])-F(g7['actual_group_upper'])
need(new_both>=F(ep['both_group_root1_lower']),'New same-source comparison improves old endpoint')
need(new_both<F(-7,8000) and F(ep['old_endpoints_by_root']['2'])<F(-7,8000),
     'Both endpoints remain strictly below minus7over8000 after exact scalar optimization')
result={
 'contract':'Exact optimum only of the independent raw-budget scalar row relaxation with each sum_i x_qi<=Tq<1. No joint realization of the two maximizing sources or actual original phases is asserted. Existing numerical/root constraints remain unchanged.',
 'input_sha256':sha256(raw).hexdigest(),'endpoint_sha256':sha256(endpoint_raw).hexdigest(),
 'checks':checks,'group5':g5,'group7':g7,
 'root1_after_exact5':str(new5),'root1_after_exact5_decimal':float(new5),
 'root1_after_both_exact_groups':str(new_both),'root1_after_both_exact_groups_decimal':float(new_both),
 'root2_unchanged':ep['old_endpoints_by_root']['2'],
 'closes_four_flip_root1':new_both>0,
 'both_endpoints_strict_upper':'-7/8000',
 'joint_gain_lower':str(F(g5['gain_over_radical_lower'])+F(g7['gain_over_radical_lower'])),
 'joint_gain_upper':str(F(g5['gain_over_radical_upper'])+F(g7['gain_over_radical_upper'])),
 'limits':['The clipped FC53 budget min(1,Vq) cannot replace the raw sum constraint.',
           'Exact scalar optima do not certify simultaneous AP-phase realizability.',
           'The original unrestricted Erdos7 target is unchanged.']}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'partitions':[g5['partition_count'],g7['partition_count']],
                  'best_blocks5':g5['optimal_partition'],'best_blocks7':g7['optimal_partition'],
                  'new_root1':float(new_both),'closes':new_both>0,
                  'gain5':g5['gain_over_radical_interval_decimal'],
                  'gain7':g7['gain_over_radical_interval_decimal']},sort_keys=True))
