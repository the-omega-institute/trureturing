"""Independent exact verification of all prefix tables, endpoint charges and feasible relaxed controls."""
from collections import Counter, deque
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import gcd, lcm, prod
from pathlib import Path
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
_spec=importlib.util.spec_from_file_location('shared_root_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/shared_first9_prefix_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/67-shared-root-prefix-bounds-for-the-actual-survivor-law.md', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'frontier/source-budgets/first9_prefix_edge_charges_input.json', 'certificates/source_norms/source-budgets/shared_first9_prefix_queries.json', 'frontier/source-budgets/shared_first9_prefix_queries.py', 'certificates/source_norms/source-budgets/shared_first3_root_queries.json', 'frontier/source-budgets/shared_first3_root_queries.py', 'certificates/source_norms/source-budgets/shared_first3_root_cut.json', 'frontier/source-budgets/shared_first3_root_cut.py', 'certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json', 'frontier/source-budgets/survivor_cylinder_ceiling.py', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py', 'certificates/source_norms/source-budgets/adaptive_core7_policy.json', 'frontier/source-budgets/adaptive_core7.py', 'certificates/source_norms/source-budgets/shared_first9_prefix_bound.json', 'frontier/source-budgets/shared_first9_prefix_bound.py', 'certificates/source_norms/source-budgets/survivor_cylinder_literals.json', 'frontier/source-budgets/verify_survivor_cylinder_literals.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    input_data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    witness=ctx.read('frontier/source-budgets/first9_prefix_edge_charges_input.json')
    policy=ctx.fresh('certificates/source_norms/source-budgets/adaptive_core7_policy.json','frontier/source-budgets/adaptive_core7.py')
    prefix_query=ctx.fresh('certificates/source_norms/source-budgets/shared_first9_prefix_queries.json','frontier/source-budgets/shared_first9_prefix_queries.py')
    root_query=ctx.fresh('certificates/source_norms/source-budgets/shared_first3_root_queries.json','frontier/source-budgets/shared_first3_root_queries.py')
    root_result=ctx.fresh('certificates/source_norms/source-budgets/shared_first3_root_cut.json','frontier/source-budgets/shared_first3_root_cut.py')
    bound=ctx.fresh('certificates/source_norms/source-budgets/shared_first9_prefix_bound.json','frontier/source-budgets/shared_first9_prefix_bound.py')
    literal=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_literals.json','frontier/source-budgets/verify_survivor_cylinder_literals.py')
    ceiling=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json','frontier/source-budgets/survivor_cylinder_ceiling.py')
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    candidate={**bound,'edge_charges':witness['edge_charges'],'numerical_dimensions':bound['model_dimensions']}
    def audit_prefix_certificate(input_data,policy,prefix_query,root_query,root_result,candidate,literal,hybrid,threshold,curve,budget):
        labels=input_data['labels'];moduli=sorted(m for m,a in labels)
        require(len(moduli)==len(set(moduli))==154,'same154 distinct original numerical labels')
        root_B={r['modulus']:list(map(F,r['restricted_upper'])) for r in root_query['records']}
        deeper={r['modulus']:list(map(F,r['restricted_upper'])) for r in prefix_query['records']}
        require(len(deeper)==len(prefix_query['records'])==prefix_query['queries']==1337 and set(deeper)=={m for m in root_B if m%9==0},'all1337 refined moduli are retained exactly once')
        require(prefix_query['states']<=2_000_000,'complete first9 query within the retained state limit')
        h=1-F(policy['epsilon_exact'])
        require(F(prefix_query['head_survival'])==F(root_query['head_survival'])==F(literal['head_survival'])==h,'unchanged actual full-H submeasure throughout')
        exact={r['modulus']:list(map(F,r['all_residue_masses'])) for r in literal['records']}
        require([a for m,a in labels if m==3]==[0] and [a for m,a in labels if m==9]==[4],'original classes exclude roots0mod3 and4mod9')
        require([r for r,v in enumerate(exact[9]) if v>0]==[1,2,5,7,8],'exact literal9 gives the five surviving prefixes')
        D=int(root_query['common_denominator'])
        require(all(len(row)==9 and min(row)>=0 and all(row[r]==0 for r in (0,3,4,6)) and all(row[r]<=exact[9][r] and (row[r]*D).denominator==1 for r in range(9)) for row in deeper.values()),'all refined prefix bounds are nonnegative, zero on forbidden prefixes, bounded by their actual prefix mass and in the same denominator')
        require(all([max(row[r::3]) for r in range(3)]==root_B[m] for m,row in deeper.items()),'all1337 refined tables aggregate exactly to their retained first3 tables')
        require({r['modulus'] for r in prefix_query['records'] if r['uses_exact_literal']}=={9} and deeper[9]==exact[9],'only the exact literal9 override is used and every residue agrees')

        # Check pure3 prefix bins directly from the single actual initial row.
        P=input_data['prime_order'];H=input_data['heights']
        profiles=[list(map(F,row)) for row in input_data['profiles']]
        units=[row[-1].denominator for row in profiles]
        require(prod(units)==D and P[0]==3,'same full actual denominator for independent prefix reconstruction')
        cap=profiles[0][-1].numerator;size=3**H[0]
        rows={(r['remaining'],int(r['live'])):r for r in policy['policy']}
        first=rows[127,(1<<154)-1]
        require(first['prime']==3,'retained initial coordinate remains prime3')
        remaining={int(child):mass for child,count,mass in first['branches']}
        covered_mask=sum(1<<j for j,(m,a) in enumerate(labels) if size%m==0)
        child_den=D//units[0];leaves=[]
        for x in range(size):
            child=sum(1<<j for j,(m,a) in enumerate(labels) if x%gcd(m,size)==a%gcd(m,size))
            allocated=min(cap,remaining.get(child,0))
            if allocated:remaining[child]-=allocated
            survival=0 if allocated==0 or child&covered_mask else child_den-int(rows[126,child]['numerator'])
            leaves.append(allocated*survival)
        require(not any(remaining.values()) and F(sum(leaves),D)==h,'single-row prefix reconstruction retains all survivor mass')
        pure3=[];m=9
        while m<=size:
            if m in deeper:
                masses=[F(sum(leaves[a::m]),D) for a in range(m)]
                require(deeper[m]==[max(masses[r::9]) for r in range(9)],'allnine prefixes independently reconstructed for pure3 query: '+str(m))
                pure3.append(m)
            m*=3

        B={**root_B,**deeper}
        selected=[m for m in moduli if m%3==0];other=[m for m in moduli if m%3]
        state={m:tuple(r for r,v in enumerate(exact[9] if m%9==0 else exact[3]) if v>0) for m in selected}
        depth={m:9 if m%9==0 else 3 for m in selected}
        require(len(selected)==66 and len(other)==88 and sum(depth[m]==9 for m in selected)==28 and sum(depth[m]==3 for m in selected)==38,'correct28 five-state and38 two-state labels with unchanged88-label remainder')
        require(candidate['labels']==selected and candidate['states']==[list(state[m]) for m in selected],'all advertised variables and legal states agree with the original-label model')
        unary={m:{a:3*B[m][a] for a in state[m]} for m in selected}
        for m in selected:
            for e in other:
                for a in state[m]:unary[m][a]+=2*B[lcm(m,e)][a]
        edges=list(combinations(selected,2))
        require(len(edges)==2145,'same2145 internal original pairs, counted once')
        charges={(r['i'],r['j']):r for r in candidate['edge_charges']}
        require(len(charges)==len(candidate['edge_charges'])==2145 and set(charges)==set(combinations(range(66),2)),'all2145 edge-charge certificates present exactly once')
        charged={m:dict(values) for m,values in unary.items()}
        pair_payoff={};compatible_count=0;all_pair_count=0;charge_entries=0
        for i,j in combinations(range(66),2):
            d,e=selected[i],selected[j];record=charges[i,j]
            left=list(map(F,record['left']));right=list(map(F,record['right']))
            require(len(left)==len(state[d]) and len(right)==len(state[e]) and min(left+right)>=0,'complete nonnegative rational charge vectors: '+str((i,j)))
            left=dict(zip(state[d],left));right=dict(zip(state[e],right))
            table={}
            for a,b in product(state[d],state[e]):
                compatible=a%gcd(depth[d],depth[e])==b%gcd(depth[d],depth[e])
                refined=a if depth[d]>=depth[e] else b
                value=2*B[lcm(d,e)][refined] if compatible else F(0)
                require(left[a]+right[b]>=value,'exact edge domination: '+str((i,j,a,b)))
                table[a,b]=value;all_pair_count+=1;compatible_count+=int(compatible)
            pair_payoff[d,e]=table
            for a in state[d]:charged[d][a]+=left[a]
            for b in state[e]:charged[e][b]+=right[b]
            charge_entries+=len(left)+len(right)
        prices=[max(charged[m].values()) for m in selected]
        require(list(map(F,candidate['site_prices']))==prices,'all66 site prices equal exact unary-plus-incident-charge maxima')
        upper=sum(prices,F(0))
        require(upper==F(candidate['certified_selected_upper']),'exact sum of derived site prices gives the retained dual upper')
        dimensions={'variables':66+charge_entries,'constraints':compatible_count+sum(len(v) for v in state.values()),'nonzeros':2*compatible_count+66*sum(len(v) for v in state.values())}
        require(dimensions==candidate['numerical_dimensions']=={'variables':14106,'constraints':8832,'nonzeros':31488},'proposal dimensions match the independently rebuilt finite model')
        require(compatible_count==8616 and all_pair_count==22902,'all compatible and incompatible pair-state cases checked')
        controls=[]
        for prefix in (1,2,5,7,8):
            assignment={m:prefix%depth[m] for m in selected}
            require(all(assignment[m] in state[m] for m in selected),'one legal globally fixed relaxation assignment: '+str(prefix))
            value=sum((unary[m][assignment[m]] for m in selected),F(0))+sum((table[assignment[d],assignment[e]] for (d,e),table in pair_payoff.items()),F(0))
            controls.append({'deep_prefix':prefix,'relaxation_score':str(value)})
        require(controls==candidate['centered_prefix_controls'],'allfive retained feasible relaxation values independently recomputed')
        best_control=max(controls,key=lambda r:F(r['relaxation_score']))
        lower=F(best_control['relaxation_score']);root_upper=F(root_result['new_selected_upper'])
        require(best_control['deep_prefix']==7 and lower<=upper<root_upper,'prefix7 lower control and rational dual bracket the improved relaxation')
        require(upper-lower<F(1276,10**9) and root_upper-lower<F(947127,10**9),'both strict near-tightness and remaining-improvement bounds')
        old=F(root_result['old_selected_upper'])
        gain=old-upper;increment=root_upper-upper
        total=F(hybrid['hybrid_Delta_lower'])+gain
        require(old==F(candidate['old_selected_upper']) and gain==F(candidate['additional_credit']) and increment==F(candidate['improvement_over_first3_cut']) and total==F(candidate['new_total_credit_lower']),'single replacement credit and increment over first3 agree exactly')
        Jh=F(budget['exact_initial_head_second']);tail=F(threshold['tail_moment_upper_exact'])
        current=next(r for r in curve['records'] if r['B']==16384)
        T,C,E=map(F,(current['T_lower'],current['C_upper'],current['E7_upper']))
        require(Jh==F(threshold['head_moment_exact']) and Jh*tail==F(current['J_upper']) and T>1 and tail>=1 and Jh-(1-h)-total>=h,'same anchored positive-product head-to-tail transport')
        scores=[]
        for extra,is_D7,key in ((F(0),False,'baseline_score'),(E,True,'E7_score')):
            needed=Jh-(1-h)-((T-1)*(h-C-extra)+h)/tail
            expected=next(r for r in threshold['records'] if r['B']==16384 and r['D7']==is_D7)
            score=(1-h)+C+extra+(tail*(Jh-(1-h)-total)-h)/(T-1)
            require(h-C-extra>0 and needed==F(expected['Delta_strict_threshold_exact']) and score==F(candidate[key]) and score>1 and total<needed,'exact refined score remains above one: '+key)
            scores.append({'D7':is_D7,'score_exact':str(score),'score_decimal':float(score),'required_Delta':str(needed),'remaining_gap':str(needed-total)})
        return {'query_count':1337,'pure3_prefix_moduli':pure3,'labels':selected,'depth3_labels':38,'depth9_labels':28,'charge_edges':2145,'charge_entries':charge_entries,'compatible_pair_cases':compatible_count,'all_pair_cases':all_pair_count,'site_prices':[str(x) for x in prices],'certified_selected_upper':str(upper),'feasible_relaxation_lower':str(lower),'feasible_deep_prefix':7,'dual_primal_gap':str(upper-lower),'maximum_increment_over_first3_upper':str(root_upper-lower),'near_tight_gap_strict_upper':'319/250000000','increment_capacity_strict_upper':'947127/1000000000','additional_credit':str(gain),'improvement_over_first3_cut':str(increment),'new_total_credit_lower':str(total),'controls':controls,'scores':scores,'scope':'Exact feasible rational charges bound the same prefix relaxation; prefix7 is feasible only for the relaxed table objective and need not be attained by any actual full layout. First3/triangle credits overlap and are not added again.'}
    result=audit_prefix_certificate(input_data,policy,prefix_query,root_query,root_result,candidate,literal,ceiling['hybrid'],ceiling['thresholds'],curve,budget)
    result.update(schema='shared-first9-prefix-independent-verification-v1',status='PASS',production_query_recomputations=0,solver_calls=0,head_optimizations=0,tail_recomputations=0)
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
