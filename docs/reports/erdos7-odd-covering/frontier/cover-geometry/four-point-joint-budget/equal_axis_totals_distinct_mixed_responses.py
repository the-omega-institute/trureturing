"""Report504: two literal families agree on axis totals and differ on mixed use."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
from math import prod
import argparse,hashlib,json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--certificate',type=Path)
parser.add_argument('--output',type=Path)
args=parser.parse_args();R=Path(__file__).resolve().parent
c=json.loads((args.certificate or R/'equal_axis_totals_distinct_mixed_responses_certificate.json').read_text())
def need(x,m):
 if not x:raise ValueError(m)
def read_pinned(name,digest):
 raw=(R/name).read_bytes();need(hashlib.sha256(raw).hexdigest()==digest,'fixed input identity '+name);return json.loads(raw)
b=read_pinned(c['base_certificate'],c['base_certificate_sha256'])['cases'][c['case_index']]
e=read_pinned(c['base_result'],c['base_result_sha256'])['axis_realizations'][c['case_index']]
need(b['profiles']==e['profiles'] and b['weight']==e['weight']==c['weight']==[17,16,13],'same fixed three-point interface')
M=e['old_carrier'];points=e['old_points'];centres=e['old_centres'];old_primes=(3,5,7,11,13,17,19)
need(c['mixed_modulus']==23*29 and c['fixed_mixed_residue']==0,'one fixed legal mixed continuation')

def crt_pair(a,m,b,n):return (a+m*((b-a)*pow(m,-1,n)%n))%(m*n)
def family(changed):
 rows=[];tables=[];changes=[]
 for axis in b['axes']:
  p=axis['prime'];sets=[set() for x in points]
  for row in axis['labels']:
   d=prod(q**v for q,v in zip(old_primes,row['exponents']));old=centres[int(row['selector']=='B')]%d;phase=row['digit'];before=phase
   if changed and p==23:
    patch=next((z for z in c['phase_changes'] if z['old_label']==d),None)
    if patch:
     need(phase==patch['old_phase'],'specified old phase');phase=patch['new_phase']
     changes.append({'old_label':d,'modulus':d*p,'old_residue':crt_pair(old,d,before,p),'new_residue':crt_pair(old,d,phase,p),'old_phase':before,'new_phase':phase})
   need(0<=phase<p,'legitimate first-level phase')
   modulus=d*p;residue=crt_pair(old,d,phase,p)
   need(residue%d==old and residue%p==phase,'single CRT residue per full label')
   rows.append({'modulus':modulus,'residue':residue,'prime':p,'old_label':d})
   for i,x in enumerate(points):
    if x%d==old:
     need(phase not in sets[i],'same-point first-level disjointness');sets[i].add(phase)
  tables.append(sets)
 need([x['prime'] for x in b['axes']]==[23,29],'two independent pure-prime axes')
 need(len(rows)==102 and len({z['modulus'] for z in rows})==102 and all(z['modulus']>1 and z['modulus']%2 for z in rows),'distinct odd full numerical labels')
 need(c['mixed_modulus'] not in {z['modulus'] for z in rows},'mixed continuation is an unused modulus')
 if changed:need(len(changes)==2 and {z['old_label'] for z in changes}=={35,13},'exactly the two declared phase changes')
 P,Q=tables
 need([list(map(len,P)),list(map(len,Q))]==c['expected_pure_counts'],'identical per-point axis deletion counts')
 raw=[];fixed_added=[]
 for i,x in enumerate(points):
  # Direct original-congruence enumeration on the common old fibre.
  survivors=[x+M*k for k in range(667) if all((x+M*k)%z['modulus']!=z['residue'] for z in rows)]
  raw.append(len(survivors));fixed_added.append(sum(z%667==0 for z in survivors))
  need(len(survivors)==(23-len(P[i]))*(29-len(Q[i])),'literal CRT count agrees with product of pure survivors')
 need(raw==c['expected_pure_survivor_counts'],'identical combined pure survivor counts')
 response={}
 for a in range(23):
  for q in range(29):response[(a,q)]=sum(w for w,ps,qs in zip(c['weight'],P,Q) if a not in ps and q not in qs)
 fixed=sum(w*n for w,n in zip(c['weight'],fixed_added));best=max(response.values())
 need(fixed==response[(0,0)]==c['expected_fixed_response_numerators'][int(changed)],'literal fixed mixed continuation response')
 need(best==c['expected_best_response_numerators'][int(changed)],'all 667 common mixed-phase choices')
 union=set().union(*P)
 need(len(union)==(23 if changed else 21),'joint prime23 phase occupation')
 if changed:need(0 not in P[0] and 0 not in P[1] and 0 in P[2] and all(0 not in qs for qs in Q),'sharp new phase deletes only third old point before continuation')
 else:need(all(0 not in s for s in P+Q),'baseline common empty phase')
 return {'changed':changed,'literal_family':rows,'phase_changes':changes,'pure_deleted_phase_sets':[[sorted(s) for s in group] for group in tables],'pure_survivor_counts':raw,'fixed_mixed_added_counts':fixed_added,'fixed_response':str(F(fixed,667)),'best_response':str(F(best,667)),'best_phase':list(min(k for k,v in response.items() if v==best)),'response_numerator_histogram':[[v,n] for v,n in sorted(Counter(response.values()).items())]}

out={'old_carrier':M,'old_centres':centres,'old_points':points,'weight':c['weight'],'families':[family(False),family(True)],'fixed_continuation':{'modulus':667,'residue':0},'response_gap':'13/667','boundary':'Actual finite families with the same old points and selectors. Axis totals and joint pure survivor counts agree; the same mixed continuation differs. No universal mass improvement, completed-source occupancy, covering counterexample or Lean verification.'}
f,g=out['families'];need(F(f['fixed_response'])-F(g['fixed_response'])==F(13,667),'strict exact continuation gap')
out=json.loads(json.dumps(out))
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(out==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained result mismatch')
print(json.dumps({'fixed_responses':[x['fixed_response'] for x in out['families']],'best_responses':[x['best_response'] for x in out['families']],'gap':out['response_gap'],'checks':'passed'},indent=2))
