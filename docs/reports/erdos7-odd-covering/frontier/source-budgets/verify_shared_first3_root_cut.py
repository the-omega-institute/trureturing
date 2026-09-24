"""Independent reconstruction of every shared-root coefficient, integer arc and feasible-flow/cut equality."""
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

CERTIFICATE='certificates/source_norms/source-budgets/shared_first3_root_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/67-shared-root-prefix-bounds-for-the-actual-survivor-law.md', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'certificates/source_norms/source-budgets/adaptive_core7_policy.json', 'frontier/source-budgets/adaptive_core7.py', 'certificates/source_norms/source-budgets/shared_first3_root_queries.json', 'frontier/source-budgets/shared_first3_root_queries.py', 'certificates/source_norms/source-budgets/shared_first3_root_cut.json', 'frontier/source-budgets/shared_first3_root_cut.py', 'certificates/source_norms/source-budgets/survivor_cylinder_queries.json', 'frontier/source-budgets/survivor_cylinder_queries.py', 'certificates/source_norms/source-budgets/survivor_cylinder_literals.json', 'frontier/source-budgets/verify_survivor_cylinder_literals.py', 'certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json', 'frontier/source-budgets/survivor_cylinder_ceiling.py', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    input_data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    policy=ctx.fresh('certificates/source_norms/source-budgets/adaptive_core7_policy.json','frontier/source-budgets/adaptive_core7.py')
    restricted=ctx.fresh('certificates/source_norms/source-budgets/shared_first3_root_queries.json','frontier/source-budgets/shared_first3_root_queries.py')
    candidate=ctx.fresh('certificates/source_norms/source-budgets/shared_first3_root_cut.json','frontier/source-budgets/shared_first3_root_cut.py')
    oldquery=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_queries.json','frontier/source-budgets/survivor_cylinder_queries.py')
    literal=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_literals.json','frontier/source-budgets/verify_survivor_cylinder_literals.py')
    ceiling=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json','frontier/source-budgets/survivor_cylinder_ceiling.py')
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    def audit_certificate(input_data,policy,restricted,candidate,oldquery,literal,hybrid,threshold,curve,budget):
        labels=input_data['labels'];moduli=[m for m,a in labels]
        require(len(moduli)==len(set(moduli))==154,'154 distinct original numerical labels')
        primes=input_data['prime_order'];heights=input_data['heights']
        profiles=[list(map(F,r)) for r in input_data['profiles']]
        units=[r[-1].denominator for r in profiles]
        caps=[r[-1].numerator for r in profiles]
        D=prod(units)
        h=1-F(policy['epsilon_exact'])
        require(primes[0]==3 and int(restricted['common_denominator'])==int(candidate['common_denominator'])==D,'same actual full denominator and first prime3')
        require(F(restricted['head_survival'])==F(oldquery['head_survival'])==F(literal['head_survival'])==h,'all prices and scores use the same unchanged full-H submeasure')
        require([a for m,a in labels if m==3]==[0],'original class3 excludes the entire root0 cylinder from H')
        by_literal={r['modulus']:list(map(F,r['all_residue_masses'])) for r in literal['records']}
        require(by_literal[3][0]==0 and sum(by_literal[3])==h,'literal survivor mass has exactly the two allowed first3 roots')
        require(len(restricted['records'])==restricted['queries']==2662 and restricted['states']<=2_000_000,'complete restricted query output within retained state bound')
        restricted_by={r['modulus']:r for r in restricted['records']}
        old_by={r['modulus']:r for r in oldquery['records']}
        require(len(restricted_by)==2662 and set(restricted_by)=={m for m in old_by if m%3==0},'every affected original query occurs exactly once')
        mixed={m:F(r['survivor_max_upper']) for m,r in old_by.items()}
        for row in hybrid['updates']:
            require(F(row['exact_maximum'])==max(by_literal[row['modulus']]),'old exact override retained: '+str(row['modulus']))
            mixed[row['modulus']]=F(row['exact_maximum'])
        B={m:list(map(F,r['restricted_upper'])) for m,r in restricted_by.items()}
        require(all(len(v)==3 and v[0]==0 and min(v)>=0 and all(v[r]<=by_literal[3][r] for r in (1,2)) and all((z*D).denominator==1 for z in v) for v in B.values()),'all2662 root prices are nonnegative, zero at root0, bounded by the corresponding actual root mass and integral in the common denominator')
        require(all(max(B[m])==mixed[m]==F(restricted_by[m]['old_scalar_upper']) for m in B),'all2662 root maxima recover the old hybrid scalar map exactly')
        overridden={m for m,r in restricted_by.items() if r['uses_exact_literal']}
        require(overridden=={3,9,15,21},'exactly four full literal replacements')
        require(all(B[m][r]==max(by_literal[m][r::3]) for m in overridden for r in range(3)),'all12 root values independently match the retained full literal residue tables')

        # Recover the first row directly; all continuation survival values were
        # already certified with the locked policy. No DAG query is executed.
        row_map={(r['remaining'],int(r['live'])):r for r in policy['policy']}
        root=(127,(1<<154)-1);first=row_map[root]
        require(first['prime']==3,'the actual retained policy reads prime3 at its initial node')
        remaining={int(child):mass for child,count,mass in first['branches']}
        size=3**heights[0]
        groups=[sum(1<<j for j,(m,a) in enumerate(labels) if x%gcd(m,size)==a%gcd(m,size)) for x in range(size)]
        multiplicities=Counter(groups)
        require(all(multiplicities[int(child)]==count for child,count,mass in first['branches']),'independent first-row leaf groups have every retained cardinality')
        covered_mask=sum(1<<j for j,(m,a) in enumerate(labels) if size%m==0)
        child_den=D//units[0]
        leaves=[]
        for child in groups:
            allocated=min(caps[0],remaining.get(child,0))
            if allocated:remaining[child]-=allocated
            if allocated==0 or child&covered_mask:survival=0
            else:
                require((126,child) in row_map,'every surviving initial child is retained')
                survival=child_den-int(row_map[126,child]['numerator'])
            leaves.append(allocated*survival)
        require(not any(remaining.values()) and F(sum(leaves),D)==h,'first-row reconstruction preserves the full-H mass')
        require([F(sum(leaves[r::3]),D) for r in range(3)]==by_literal[3],'independent first-row root masses match the exact literal law')
        pure3=[]
        power=3
        while power<=size:
            if power in B:pure3.append(power)
            power*=3
        for m in pure3:
            masses=[F(sum(leaves[a::m]),D) for a in range(m)]
            require(B[m]==[max(masses[r::3]) for r in range(3)],'independent first-row bins validate all roots of pure3 query: '+str(m))

        selected=sorted(m for m in moduli if m%3==0)
        other=sorted(set(moduli)-set(selected))
        require(len(selected)==66 and len(other)==88 and candidate['labels']==selected,'all66 selected labels remain distinct from the88 unselected labels')
        all_pairs=list(combinations(sorted(moduli),2))
        affected=[(d,e) for d,e in all_pairs if d%3==0 or e%3==0]
        crossing=[(d,e) for d,e in affected if (d%3==0)!=(e%3==0)]
        internal=[(d,e) for d,e in affected if d%3==e%3==0]
        unaffected=[(d,e) for d,e in all_pairs if d%3 and e%3]
        require(len(affected)==7953 and len(crossing)==5808 and len(internal)==2145 and len(unaffected)==3828 and len(all_pairs)==11781,'complete154-label pair partition with no omissions or duplicates')
        coeff=Counter({m:3 for m in selected})
        for d,e in affected:coeff[lcm(d,e)]+=2
        require(set(coeff)==set(B) and all(coeff[m]==old_by[m]['coefficient'] for m in B),'all and only2662 affected marginal coefficients equal the old full expansion')
        old_selected=sum((coeff[m]*mixed[m] for m in B),F(0))
        unary={d:[3*B[d][r] for r in (1,2)] for d in selected}
        for d,e in crossing:
            endpoint=d if d%3==0 else e
            for bit in (0,1):unary[endpoint][bit]+=2*B[lcm(d,e)][bit+1]
        weights={(d,e):[2*B[lcm(d,e)][r] for r in (1,2)] for d,e in internal}
        require(old_selected==F(candidate['old_selected_upper']),'old selected upper reconstructed from all original coefficients')
        # Clear the full actual denominator after independent rational assembly.
        unary={d:[int(v*D) for v in row] for d,row in unary.items()}
        weights={edge:[int(v*D) for v in row] for edge,row in weights.items()}
        constant_zero=sum(row[0] for row in unary.values())+sum(row[0] for row in weights.values())
        linear={d:row[1]-row[0] for d,row in unary.items()}
        disagreements={}
        for (d,e),(w0,w1) in weights.items():
            require((w1-w0)%2==0 and (w0+w1)%2==0,'integer binary pair decomposition: '+str((d,e)))
            shift=(w1-w0)//2;penalty=(w0+w1)//2
            require(all((w0 if x==y==0 else w1 if x==y==1 else 0)==w0+shift*(x+y)-penalty*abs(x-y) for x,y in product((0,1),repeat=2)),'allfour local binary identities: '+str((d,e)))
            linear[d]+=shift;linear[e]+=shift;disagreements[d,e]=penalty
        constant=constant_zero+sum(max(v,0) for v in linear.values())
        N=len(selected);source=N;sink=N+1;index={d:i for i,d in enumerate(selected)}
        expected={}
        for d,a in linear.items():
            if a<0:expected[source,index[d]]=-a
            if a>0:expected[index[d],sink]=a
        for (d,e),penalty in disagreements.items():
            if penalty:
                expected[index[d],index[e]]=penalty
                expected[index[e],index[d]]=penalty
        require((candidate['source_vertex'],candidate['sink_vertex'])==(source,sink) and int(candidate['constant_numerator'])==constant,'exact objective-to-cut constant and vertex convention')
        submitted={(r['from'],r['to']):(int(r['capacity']),int(r['flow'])) for r in candidate['flow_edges']}
        require(len(submitted)==len(candidate['flow_edges'])==len(expected)==4356 and set(submitted)==set(expected),'every4356 original directed arc is present exactly once')
        require(all(cap==expected[e] and 0<=flow<=cap for e,(cap,flow) in submitted.items()),'every submitted capacity and feasible integer arc flow matches the independently reconstructed model')
        net=[0]*(N+2)
        for (u,v),(cap,flow) in submitted.items():net[u]-=flow;net[v]+=flow
        value=int(candidate['flow_value_numerator'])
        require(all(net[i]==0 for i in range(N)) and net[source]==-value and net[sink]==value,'flow conservation at all66 vertices and equal source/sink flow value')
        side=set(candidate['source_side'])
        require(len(side)==len(candidate['source_side']) and side<=set(range(N+2)) and source in side and sink not in side,'valid source/sink cut')
        cut=sum(cap for (u,v),(cap,flow) in submitted.items() if u in side and v not in side)
        require(cut==value,'independent feasible flow equals the displayed cut capacity')
        bits={d:int(index[d] not in side) for d in selected}
        direct=sum(unary[d][bits[d]] for d in selected)+sum(row[bits[d]] for (d,e),row in weights.items() if bits[d]==bits[e])
        require(direct==constant-cut and {str(d):bits[d]+1 for d in selected}==candidate['maximizing_roots'],'the cut attains the advertised binary objective and every named first3 root')
        require(set(bits.values())=={0},'all66 labels on root1 is an output of the certified binary optimum')
        best=F(direct,D)
        require(best==sum((coeff[m]*B[m][1] for m in B),F(0))==F(candidate['new_selected_upper']),'optimal root1 value also matches the complete2662-coefficient direct sum')
        gain=old_selected-best
        old_credit=F(hybrid['hybrid_Delta_lower']);new_credit=old_credit+gain
        require(gain>=0 and gain==F(candidate['additional_credit']) and new_credit==F(candidate['new_total_credit_lower']),'selected replacement gain is added exactly once to old Chapter65 credit')
        Jh=F(budget['exact_initial_head_second'])
        require(Jh==F(threshold['head_moment_exact']),'independent head-moment anchoring to the original budget')
        tail=F(threshold['tail_moment_upper_exact'])
        current=next(r for r in curve['records'] if r['B']==16384)
        T,C,E=map(F,(current['T_lower'],current['C_upper'],current['E7_upper']))
        require(Jh*tail==F(current['J_upper']) and T>1 and tail>=1 and Jh-(1-h)-new_credit>=h,'unchanged directed tail factor multiplies a positive residual head bound')
        scores=[]
        for extra,is_D7,key in ((F(0),False,'baseline_score'),(E,True,'E7_score')):
            matching=[r for r in threshold['records'] if r['B']==16384 and r['D7']==is_D7]
            require(len(matching)==1 and h-C-extra>0,'the requested same-law final-event lower mass stays positive: '+key)
            needed=Jh-(1-h)-((T-1)*(h-C-extra)+h)/tail
            score=(1-h)+C+extra+(tail*(Jh-(1-h)-new_credit)-h)/(T-1)
            require(needed==F(matching[0]['Delta_strict_threshold_exact']) and score==F(candidate[key]) and score>1 and new_credit<needed,'exact score remains above one and actual achieved credit below threshold: '+key)
            scores.append({'D7':is_D7,'score_exact':str(score),'score_decimal':float(score),'required_Delta':str(needed),'remaining_gap':str(needed-new_credit)})
        return {'selected_labels':selected,'other_count':len(other),'query_count':len(B),'literal_root_values_checked':12,'pure3_bin_moduli':pure3,'selected_unaries':66,'mixed_pairs':5808,'internal_pairs':2145,'unselected_pairs':3828,'flow_arcs':len(submitted),'flow_value':str(value),'cut_capacity':str(cut),'old_selected_upper':str(old_selected),'new_selected_upper':str(best),'additional_credit':str(gain),'new_total_credit_lower':str(new_credit),'scores':scores,'all_maximizing_roots':candidate['maximizing_roots'],'scope':'Exact optimum of the first3-root upper relaxation only, with remaining residues relaxed; prior triangle credit overlaps and is not added.'}
    result=audit_certificate(input_data,policy,restricted,candidate,oldquery,literal,ceiling['hybrid'],ceiling['thresholds'],curve,budget)
    result.update(schema='shared-first3-root-independent-verification-v1',status='PASS',production_query_recomputations=0,solver_calls=0,head_optimizations=0,tail_recomputations=0)
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
