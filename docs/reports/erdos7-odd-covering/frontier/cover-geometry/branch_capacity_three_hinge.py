#!/usr/bin/env python3
"""Exact arithmetic for Report589's branch-capacity/first-hinge extension.

Consumes the existing normalized-joint-hinge data without rerunning its624
checks. Uses one selected Q law, its first three hinge contracts, and
complete original/query heights. This is not Lean or unrestricted Erdos7.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [encode(v) for v in value]
    return value


def main():
    parser=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--source-data',type=Path,default=Path(__file__).with_name('normalized_joint_hinge_transfer.json'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    source_bytes=args.source_data.read_bytes();source=json.loads(source_bytes)
    G,B,K2,K3=(F(source[key]) for key in ('G','B','K2','K3'))
    alpha=F(source['raw_Q_mass_lower'])
    theta1=F(source['stages'][-1]['Theta'][1])
    C=G-1-2*B
    N=B+2*K2-5+(G-3)*K3
    old=F(source['source_only_gate'])
    checks={}
    def require(name,predicate):
        if name in checks or not predicate:raise ArithmeticError(name)
        checks[name]=True
    require('same_source_constants',(G,B,K2,K3,alpha)==(
        F(566,49),F(2907477445994511750779,600105680174967275330),
        F(4201907333478675099087,1457399508996349097230),
        F(50846040079973272728927,24775791652937934652910),
        F(504290487541989307,4852222295880960000)))
    require('same_source_first_hinge',theta1==B-1)
    require('same_source_density',F(source['raw_Q_density_cap'])==9 and F(source['normalized_Q_density_cap'])==9/alpha)
    def delta(pA,pB):
        return C-(N+(1+B)*pA)/(27-pA-pB)
    def haar(pA,pB):
        return 49*(27-pA-pB)*alpha*delta(pA,pB)/299376
    require('base_formula_agrees',old==C-(3*K2-3+(G-3)*K3)/27)
    require('first_hinge_gain',delta(0,0)-old==(K2-B+2)/27>0)
    require('positive_base',delta(0,0)>0)
    require('positive_e8_tail',delta(F(1,81),0)>0)
    require('tail_budget',54*F(1,3**8)/(1-F(1,3))==F(1,81))
    thresholdA=(27*C-N)/(C+1+B)
    thresholdB=(27*C-N)/C
    require('threshold_A',delta(thresholdA,0)==0)
    require('threshold_B',delta(0,thresholdB)==0)
    require('positive_B_single_e6',delta(0,F(2,27))>0)
    require('positive_B_tail_e7',delta(0,F(1,27))>0)
    require('negative_e7_single_A_for_this_specialization',delta(F(2,81),0)<0)
    require('negative_B_tail_e6_for_this_specialization',delta(0,F(1,9))<0)
    haar8=haar(F(1,81),0)
    require('positive_density',haar8>F(1,8000000))
    require('fixed_total_worst_A',C>0 and N>0 and 1+B>0)
    # For0<=p<=3, A0<=12 and D>=24. The coefficient of R in
    # the pre-substitution gate is-2+(A0-11)/D <=-2+1/24.
    require('replacement_R_by_B_direction',-2+F(1,24)<0)
    values={'G':G,'B':B,'Theta1':theta1,'K2':K2,'K3':K3,'alpha':alpha,
            'old_base_margin':old,'base_three_hinge_margin':delta(0,0),
            'base_haar_density_lower':haar(0,0),'first_hinge_gain':(K2-B+2)/27,
            'e8_uniform_pure_budget':F(1,81),'e8_margin':delta(F(1,81),0),
            'e8_haar_density_lower':haar8,'A_branch_threshold':thresholdA,
            'B_branch_threshold':thresholdB,
            'e7_single_A_margin_fixed_z3_k1_t2':delta(F(2,81),0),
            'e4_single_A_margin_fixed_z3_k1_t2':delta(F(2,3),0),
            'e4_single_B_margin_fixed_z3_k1_t2':delta(0,F(2,3))}
    output={'scope':'Same Report589 selected Q law and shallow two-phase condition; fixed base1 mod3,3 mod9; additional pure branch budgets or arbitrary pure tail e>=8; all allowed nonpure heights and arbitrary23/29 originals. No global clipping optimality or unrestricted Erdos7 claim.',
            'input_data_sha256':sha256(source_bytes).hexdigest(),
            'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'constants':values,'displays':{k:float(v) for k,v in values.items()},
            'checks':checks,'check_count':len(checks)}
    args.output.write_text(json.dumps(encode(output),indent=2)+'\n',encoding='utf-8')
    print(json.dumps(encode({'output':str(args.output),'base_margin':delta(0,0),'e8_margin':delta(F(1,81),0),'e8_haar':haar8,'check_count':len(checks)}),indent=2))

if __name__=='__main__':main()
