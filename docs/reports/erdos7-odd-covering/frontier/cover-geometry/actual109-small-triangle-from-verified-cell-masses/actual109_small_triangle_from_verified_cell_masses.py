#!/usr/bin/env python3
"""Exact small shared-label clusters from the verified 692 cell masses.

Reuse the old independently verified source record; reconstruct its whole
mod225 marginal in root-major coordinates. Query intersections use CRT marginal
lookups. A producer comparison is performed only after the independent result.
No optimizer, full central cluster, or new source-construction claim.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, combinations
from math import gcd, lcm
from hashlib import sha256
import argparse, json
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source-record',type=Path,default=(Path(__file__).parent / '../clustered_full5_allfield_verify.json'))
ap.add_argument('--compare',type=Path)
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=ap.parse_args()
v=json.loads(a.source_record.read_text())
checks=0
def ck(ok,label):
 global checks
 checks+=1
 if not ok: raise ValueError(label)
ck(v['complete'] and v['actual_states']==2125830,'complete692 source record')
mass=[F(0)]*225
for row in v['per_cell']:
 l,m=row['cell'];x3=3*(l%3)+l//3;x5=5*(m%5)+m//5
 crt=next(x for x in range(225) if x%9==x3 and x%25==x5)
 ck(mass[crt]==0,'unique positive coarse atom')
 mass[crt]=F(row['source_num'],v['source_denominator'])
ck(sum(mass)==F(305684996597,646498195200),'actual109 unnormalized source mass')
mods=(3,5,9,15,45)
readings={d:[sum((w for x,w in enumerate(mass) if x%d==b),F(0)) for b in range(d)] for d in mods}
maxima={d:max(readings[d]) for d in mods}

def pair_mass(d,b,e,c):
 if (b-c)%gcd(d,e):return F(0)
 n=lcm(d,e)
 r=next(x for x in range(n) if x%d==b and x%e==c)
 return readings[n][r]

fee_path=a.source_record.with_name('actual_pair_activation_certificate.json')
W=list(map(F,json.loads(fee_path.read_text())['complete_coefficients']['weighted_nonunit_query']))
def fee_at(d):
 ex=ey=0
 while d%3==0:ex+=1;d//=3
 while d%5==0:ey+=1;d//=5
 ck(d==1 and max(ex,ey)<=2,'literal shallow central mode')
 return W[32*(4*ex+ey)]

triangles=[]
for labels in ((3,5,15),(3,5,9)):
 pairs=list(combinations(labels,2))
 envelope=3*sum(maxima[d] for d in labels)+2*sum(maxima[lcm(d,e)] for d,e in pairs)
 spent={}
 for d in labels:spent[d]=spent.get(d,0)+3
 for d,e in pairs:
  m=lcm(d,e);spent[m]=spent.get(m,0)+2
 for d,w in spent.items():ck(F(w)<=fee_at(d),'selected literal factors fit W budget')
 rows=[]
 for phases in product(*(range(d) for d in labels)):
  choice=dict(zip(labels,phases))
  unary=[3*readings[d][choice[d]] for d in labels]
  cross=[2*pair_mass(d,choice[d],e,choice[e]) for d,e in pairs]
  value=sum(unary+cross,F(0))
  ck(value<=envelope,'true factorwise envelope for every layout')
  rows.append({'residues':list(phases),'value':str(value)})
 maximum=max(F(row['value']) for row in rows)
 winners=[row['residues'] for row in rows if F(row['value'])==maximum]
 ck(len(rows)==225 if labels==(3,5,15) else len(rows)==135,'complete independent layout domain')
 common_values=[F(row['value']) for row in rows if any(all(x%d==b for d,b in zip(labels,row['residues'])) for x in range(lcm(*labels)))]
 common=max(common_values)
 ck(maximum>=common,'common centers form a restricted domain')
 gap=envelope-maximum
 ck(gap>0,'strict sharing loss relative to actual maxima')
 c0=F(1084133,201247200)
 triangles.append({'labels':list(labels),'layout_count':len(rows),
  'true_independent_six_factor_envelope':str(envelope),'shared_triangle_maximum':str(maximum),
  'sharing_gap':str(gap),'sharing_gap_decimal':float(gap),
  'common_center_maximum':str(common),'maximizing_layouts':winners,
  'marginal_maxima':{str(d):str(maxima[d]) for d in sorted(set(labels)|{lcm(d,e) for d,e in pairs})},
  'maximizer_residues':{str(d):[b for b,x in enumerate(readings[d]) if x==maxima[d]] for d in labels},
  'spent_lcm_coefficients':{str(d):n for d,n in sorted(spent.items())},
  'continuation_gate_credit':str(c0*gap),'continuation_gate_credit_decimal':float(c0*gap),
  'layouts':rows})

result={'status':'PASS','scope':'Literal {3,5,15} and {3,5,9} triangles on one fixed unnormalized actual109 source. Reuses verified692 source cells and uses independent CRT marginal intersections; not an independent source reconstruction or a new general cluster lemma. Credits overlap and cannot be summed. No full9x25 cluster, optimizer or Lean.',
 'source_record_sha256':sha256(a.source_record.read_bytes()).hexdigest(),
 'fee_source_sha256':sha256(fee_path.read_bytes()).hexdigest(),
 'source_mass':str(sum(mass)),'positive_central_cells':sum(w>0 for w in mass),
 'mod225_mass':[str(w) for w in mass],'triangles':triangles,
 'checks':checks,'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
# The complete independent quantities above are fixed before reading new producer output.
if a.compare:
 producer=json.loads(a.compare.read_text())
 pmass=[F(0)]*225
 for row in producer['central_cells']:
  x=row['x_mod225'];ck(pmass[x]==0,'producer central atoms unique');pmass[x]=F(row['mass'])
 for x in range(225):ck(mass[x]==pmass[x],'same actual source at every mod225 atom')
 ck(F(producer['source_mass'])==sum(mass),'producer source mass')
 for tri in triangles:
  other=next(t for t in producer['triangles'] if t['labels']==tri['labels'])
  ck(tri['layout_count']==other['layout_count'],'same complete layout domain')
  ck(F(tri['true_independent_six_factor_envelope'])==F(other['independent_actual_mass_envelope']),'actual independent envelope')
  ck(F(tri['shared_triangle_maximum'])==F(other['exact_common_layout_maximum']),'shared maximum')
  ck(F(tri['sharing_gap'])==F(other['strict_shared_label_saving']),'strict sharing gap')
  ck(tri['maximizing_layouts']==other['maximizing_layouts'],'complete maximizing layouts')
 result['producer_comparison']={'status':'PASS','source_atoms_compared':225,
  'producer_result_sha256':sha256(a.compare.read_bytes()).hexdigest()}
result['checks']=checks
a.output.write_text(json.dumps(result,indent=2)+'\n')
summary={k:v for k,v in result.items() if k not in ('mod225_mass','triangles')}
summary['triangles']=[{k:v for k,v in t.items() if k not in ('layouts',)} for t in triangles]
print(json.dumps(summary,indent=2))
