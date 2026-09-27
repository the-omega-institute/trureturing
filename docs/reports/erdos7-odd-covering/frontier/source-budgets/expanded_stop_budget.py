"""Exact upward continuation at three cutoffs under the same fixed seven-phase head law."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,isqrt,lcm,prod
from pathlib import Path
import importlib.util
import json
import sys
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('expanded_stop_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require,load_module=_io.require,_io.load_module

CERTIFICATE='certificates/source_norms/source-budgets/expanded_stop_budget.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md', 'problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md', 'certificates/source_norms/source-budgets/expanded_stop_head.json', 'frontier/source-budgets/expanded_stop_head.py', 'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json', 'frontier/source-budgets/balanced_profile_tail_budget.py', 'certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json', 'frontier/source-budgets/balanced_profile_exponent_frontier.py', 'star_block/stoploss.py', 'star_block/base.py', 'verify_finite_continuation.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','same complete actual seven-phase input')
    head=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_head.json','frontier/source-budgets/expanded_stop_head.py')
    old=ctx.fresh('certificates/source_norms/source-budgets/balanced_profile_tail_budget.json','frontier/source-budgets/balanced_profile_tail_budget.py')
    frontier=ctx.fresh('certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json','frontier/source-budgets/balanced_profile_exponent_frontier.py')
    api=load_module('expanded_stoploss_library',Path(base)/'star_block/stoploss.py')
    continuation=load_module('expanded_stopping_library',Path(base)/'verify_finite_continuation.py')
    for key in ('prime_order','heights','profiles','labels'):
        require(data[key]==head[key],'same actual head '+key)
    require(len(data['labels'])==len({m for m,a in data['labels']})==154,'154 distinct actual labels')
    require(all(34%m!=a for m,a in data['labels']),'actual uncovered witness')
    P,H=data['prime_order'],data['heights'];R=[[F(x) for x in row] for row in data['profiles']]
    epsilon=F(head['epsilon_exact'])
    require(all(F(row['epsilon_exact'])==epsilon for row in head['records']),'full20 and collapsed7 exact agreement')
    require(frontier['profiles']==data['profiles']==old['profiles'],'same balanced comparison profiles')
    BMAX=65536;CHECKPOINTS=(16384,32768,65536);SCALE=10**18;CAP=(2*BMAX+1)//5
    low_tables={}
    # Recompute all 101 exact bounded-coordinate coefficients and infinite total.
    coefficients=[F(1)];total=F(1)
    for p,h,r in zip(P,H,R):
        require(len(r)==h+1 and r[0]==1 and all(F(1,p**e)<=r[e]<=r[e-1] for e in range(1,h+1)),'feasible complete depth caps')
        factors=[r[e] if e<=h else r[h]/p**(e-h) for e in range(6)]
        updated=[F(0)]*(len(coefficients)+5)
        for i,a in enumerate(coefficients):
            for j,b in enumerate(factors):updated[i+j]+=a*b
        coefficients=updated;total*=sum(r)+r[-1]/(p-1)
    E7=total-sum(coefficients[:8])
    require(len(coefficients)==101 and E7==F(frontier['records'][1]['outside_weight']),'exact unchanged D7 complement allowance')
    allprimes=api.primes_to(BMAX)
    require(P==[p for p in allprimes if 3<=p<=73],'complete twenty actual head primes')
    require(len(allprimes)==6542 and allprimes[-1]==65521,'complete large global prime inventory')
    cutoffs={max(p for p in allprimes if p<=B):B for B in CHECKPOINTS}
    ceil=api.stoploss_ceiling
    weights=[0]*(CAP+1);weights[1]=SCALE;mean=second=SCALE
    exact_mean=exact_second=F(1)
    for p,h,r in zip(P,H,R):
        rounded=[0]+[ceil(SCALE*(r[f-1]-r[f]).numerator,(r[f-1]-r[f]).denominator) for f in range(1,h+1)]
        numerator=SCALE*r[h].numerator*(p-1);denominator=r[h].denominator*p
        for f in range(h+1,CAP+1):
            if denominator>=numerator:
                rounded.extend([1]*(CAP+1-f));break
            rounded.append(ceil(numerator,denominator));denominator*=p
        require(len(rounded)==CAP+1,'every retained lifted atom rounded upward')
        first=1+sum(r[1:],F(0))+r[h]/(p-1)
        square=1+sum(((2*e+1)*r[e] for e in range(1,h+1)),F(0))+r[h]*(F(2*h+1,p-1)+F(2*p,(p-1)**2))
        exact_mean*=first;exact_second*=square
        weights=api.stoploss_product_update(weights,rounded,SCALE)
        mean=ceil(mean*first.numerator,first.denominator);second=ceil(second*square.numerator,square.denominator)
    charge=0;steps=[];snapshots=[]
    for k,q in enumerate(allprimes,1):
        if q<=73:continue
        cutoff=(2*q+1)//5
        numerator=5*mean-(2*q+1)*SCALE+sum((2*q+1-5*d)*weights[d] for d in range(1,cutoff+1))
        require(numerator>=0,'nonnegative directed positive-part upper numerator')
        step=ceil(numerator,3*(q-2));charge+=step;steps.append([q,step,charge])
        c=F(5*(q-1),3*(q-2))
        weights=api.stoploss_product_update(weights,api.stoploss_atom_bounds(q,c,CAP,SCALE),SCALE)
        first=1+c/(q-1);square=1+c*F(3*q-1,(q-1)**2)
        mean=ceil(mean*first.numerator,first.denominator);second=ceil(second*square.numerator,square.denominator)
        if q in cutoffs:
            B=cutoffs[q];T=continuation.stopping_threshold(k);C,J=F(charge,SCALE),F(second,SCALE)
            require(T>1 and k>=10,'positive BBMST stopping threshold')
            score=epsilon+C+(J-1)/(T-1);survival=1-epsilon-C;d7=score+E7;d7survival=survival-E7
            snapshot={'B':B,'global_prime_index':k,'last_prime':q,'next_prime':next((p for p in allprimes if p>B),65537),'tail_stages':len(steps),'C_upper':str(C),'J_upper':str(J),'full_mean_upper':str(F(mean,SCALE)),'T_lower':str(T),'epsilon_exact':str(epsilon),'consumer_score_upper':str(score),'consumer_score_decimal':float(score),'margin_lower':str(1-score),'margin_decimal':float(1-score),'survival_lower':str(survival),'Gamma_upper':str(1+(J-1)/survival) if survival>0 else None,'E7_upper':str(E7),'D7_score_upper':str(d7),'D7_score_decimal':float(d7),'D7_margin_lower':str(1-d7),'D7_margin_decimal':float(1-d7),'D7_survival_lower':str(d7survival),'D7_Gamma_upper':str(1+(J-1)/d7survival) if d7survival>0 else None,'retained_states':CAP,'maximum_queried_state':cutoff,'step_digest':sha256(json.dumps(steps,separators=(',',':')).encode()).hexdigest(),'final_low_state_digest':sha256(json.dumps(weights,separators=(',',':')).encode()).hexdigest()}
            if B==16384:
                require(C==F(old['C_upper']) and J==F(old['J_upper']) and steps==old['stages'],'all original1879 directed stages exactly preserved')
            snapshots.append(snapshot)
            low_tables[str(B)]=list(weights)
    require(len(steps)==6521 and [s['B'] for s in snapshots]==list(CHECKPOINTS),'complete requested one-pass sweep')
    require(F(snapshots[1]['consumer_score_upper'])<1 and F(snapshots[2]['D7_score_upper'])<1,'strict baseline and degree7 passes at the specified cutoffs')
    result={'schema':'expanded-stopping-cutoff-exact-upper-v1','scope':'Actual seven-phase154 head, unchanged complete balanced depth caps, numerical head order and uniform complete higher digits. Delta2/5 through B, one common avoiding-event conditioning, then BBMST uniform-base delta1/2. Extra distinct smooth moduli are licensed only outside D7. Ordinary comparison and continuation remain explicit inputs.','scale':SCALE,'maximum_B':BMAX,'prime_order':P,'heights':H,'profiles':data['profiles'],'labels':data['labels'],'exact_initial_head_mean':str(exact_mean),'exact_initial_head_second':str(exact_second),'E7_upper':str(E7),'D7_coefficients':list(map(str,coefficients)),'total_infinite_head_weight':str(total),'snapshots':snapshots,'stages':steps,'low_product_tables':low_tables}
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
