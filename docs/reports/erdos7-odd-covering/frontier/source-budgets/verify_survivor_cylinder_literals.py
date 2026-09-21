"""Independent actual policy recursion for eight moduli and every one of their96 residues."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,lcm,prod
from pathlib import Path
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
_spec=importlib.util.spec_from_file_location('survivor_cylinder_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/survivor_cylinder_literals.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md', 'problem-details/63-squared-load-stoploss-continuation.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'certificates/source_norms/source-budgets/adaptive_core7_policy.json', 'frontier/source-budgets/adaptive_core7.py', 'certificates/source_norms/source-budgets/survivor_cylinder_queries.json', 'frontier/source-budgets/survivor_cylinder_queries.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    policy=ctx.fresh('certificates/source_norms/source-budgets/adaptive_core7_policy.json','frontier/source-budgets/adaptive_core7.py')
    bound=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_queries.json','frontier/source-budgets/survivor_cylinder_queries.py')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','locked complete literal input')
    START=time.monotonic();SECONDS=60
    MODULI=(1,3,5,7,9,15,21,35)
    class ResourceStop(Exception):pass
    def budget():
        if time.monotonic()-START>=SECONDS:raise ResourceStop('literal8query60secondcap')
    P,H,labels=data['prime_order'],data['heights'],data['labels'];R=[list(map(F,x)) for x in data['profiles']]
    U=[x[-1].denominator for x in R];A=[x[-1].numerator for x in R];sizes=[p**h for p,h in zip(P,H)]
    support=[sum(1<<i for i,p in enumerate(P) if m%p==0) for m,a in labels]
    complete=[sum(1<<j for j,s in enumerate(support) if s<128 and not s&u) for u in range(128)]
    den=[prod(U[7:])*prod(U[i] for i in range(7) if u>>i&1) for u in range(128)]
    root=(127,(1<<154)-1);h=1-F(policy['epsilon_exact'])
    require(F(bound['head_survival'])==h,'same head survivor event')
    # Every requested modulus only constrains original core coordinates.
    require(all(m>0 and all(m%p for p in P[7:]) for m in MODULI),'queries concern core primes only')
    terminals={};counts={'terminal_coordinate_rows':0,'terminal_actual_leaves':0,'reconstructed_core_rows':0,'core_actual_leaves':0,'state_row_updates':0,'fixed_residue_queries':0};rows=[];records=[]
    result={'schema':'literal-actual-survivor-cylinder8-v1','status':'partial','scope':'Exact all-residue queries for the locked actual positive64 policy, then actual allowed-first terminal rows. No optimization, relaxed history query or Bellman values are used.','query_moduli':list(MODULI),'head_survival':str(h),'records':records,'counts':counts}
    # Independently construct the terminal rows, counting assigned surviving mass.
    ids=[[j for j,s in enumerate(support) if s>>i&1] for i in range(7,20)]
    for live,ignored_claim in policy['terminals']:
     budget();active=int(live);survival=1
     for axis,indices in enumerate(ids,7):
      forbidden={labels[j][1]%P[axis] for j in indices if active>>j&1}
      actual_order=[x for x in range(P[axis]) if x not in forbidden]+[x for x in range(P[axis]) if x in forbidden]
      left=U[axis];allowed=0
      for x in actual_order:
       mass=min(left,A[axis]);left-=mass
       if x not in forbidden:allowed+=mass
      require(left==0,'actual terminal row normalizes')
      survival*=allowed;counts['terminal_coordinate_rows']+=1;counts['terminal_actual_leaves']+=len(actual_order)
     terminals[(0,active)]=survival
    # Independently recover each queried coordinate's original leaf groups.
    leaf_masks={}
    for axis in range(3):
     factors=[gcd(m,sizes[axis]) for m,a in labels]
     leaf_masks[axis]=[sum(1<<j for j,((m,a),f) in enumerate(zip(labels,factors)) if x%f==a%f) for x in range(sizes[axis])]
    for rec in policy['policy']:
     budget();u,active=rec['remaining'],int(rec['live']);axis=P.index(rec['prime']);child_u=u^(1<<axis)
     constraints=sorted({gcd(m,sizes[axis]) for m in MODULI});actual_groups=defaultdict(list)
     if len(constraints)>1:
      for x,mask in enumerate(leaf_masks[axis]):actual_groups[active&mask].append(x)
      counts['reconstructed_core_rows']+=1;counts['core_actual_leaves']+=sizes[axis]
     branches=[]
     for live,multiplicity,allocated in rec['branches']:
      child=int(live);hist={1:[allocated]}
      if len(constraints)>1:
       require(len(actual_groups[child])==multiplicity,'actual queried-axis group cardinality')
       for q in constraints[1:]:hist[q]=[0]*q
       left=allocated
       for x in actual_groups[child]:
        mass=min(left,A[axis]);left-=mass
        for q in constraints[1:]:hist[q][x%q]+=mass
       require(left==0 and all(sum(v)==allocated for v in hist.values()),'actual group mass and residue partition')
      branches.append((child,bool(child&complete[child_u]),hist))
     require(sum(x[2][1][0] for x in branches)==U[axis],'retained complete row total')
     rows.append((u,active,axis,child_u,branches))
    require(len(rows)==6511 and len(terminals)==2542,'complete retained positive law')
    by_mod={int(x['modulus']):x for x in bound['records']}
    for m in MODULI:
     masses=[]
     for residue in range(m):
      budget();values=dict(terminals)
      for n,(u,active,axis,child_u,branches) in enumerate(rows):
       if n%256==0:budget()
       q=gcd(m,sizes[axis]);answer=0
       for child,bad,hist in branches:
        if not bad:
         require(child>0 and (child_u,child) in values,'positive actual child retained and evaluated')
         answer+=hist[q][residue%q]*values[child_u,child]
       values[u,active]=answer;counts['state_row_updates']+=1
      masses.append(F(values[root],den[127]));counts['fixed_residue_queries']+=1
     require(sum(masses,F(0))==h,'all literal residues partition the same head survivor')
     exact=max(masses);upper=h if m==1 else F(by_mod[m]['survivor_max_upper'])
     require(h/m<=exact<=upper,'literal maximum lies between averaging lower and independent relaxation upper')
     row={'modulus':m,'all_residue_masses':[str(x) for x in masses],'max_exact':str(exact),'max_decimal':float(exact),'maximizing_residues':[a for a,x in enumerate(masses) if x==exact],'relaxed_upper':str(upper),'relaxed_gap_exact':str(upper-exact),'relaxed_gap_decimal':float(upper-exact),'upper_valid':True}
     records.append(row)
    result['status']='PASS'
    require(result['status']=='PASS' and len(records)==8 and counts['fixed_residue_queries']==96,'all requested exact residues complete')
    result.update(DP_recomputations=0,tail_recomputations=0,completed_moduli=len(records))
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
