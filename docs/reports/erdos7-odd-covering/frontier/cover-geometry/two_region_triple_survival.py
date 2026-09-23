"""Exact 41-unit survivor lower bound from two exhaustive pure-axis regions."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description="Exact two-region triple survivor bound from the same 51-label inventory.")
parser.add_argument('--input-dir',type=Path,default=ROOT)
parser.add_argument('--certificate',type=Path)
parser.add_argument('--output',type=Path)
args=parser.parse_args();BASE=args.input_dir
CERT=args.certificate or ROOT/'two_region_triple_survival_certificate.json'
certificate=json.loads(CERT.read_text())
def need(ok,msg):
 if not ok:raise ValueError(msg)
def load(name,digest):
 raw=(BASE/name).read_bytes();need(hashlib.sha256(raw).hexdigest()==digest,'input hash '+name)
 return json.loads(raw)
expected_inputs={'integer_selector_tail_interface_certificate.json': '66f155d2d9f65b044017e0c033c1d3e8f9999cea100eabce1b8aa049810ecb5a', 'integer_selector_tail_interface.json': '4681c5b6da42138625dfa6c21e680522edf60ed400a3ae83c817d94bfcf9e4f4', 'mixed_split_complete_weighted_boundary_certificate.json': '1c46cc37e02ffaf4206d628609a1a037de310fcf679770be0026d4a84f2cb015', 'mixed_split_complete_weighted_boundary.json': '87f177f9e2a8744d95ed99f8ce3087b0a3e5ca88573e409948d57d19688c57cb'}
need(certificate['inputs']==expected_inputs,'all four exact 501/503 prerequisites')
source_inputs={name:load(name,digest) for name,digest in expected_inputs.items()}
c501=source_inputs['mixed_split_complete_weighted_boundary_certificate.json']
r501=source_inputs['mixed_split_complete_weighted_boundary.json']
need(r501['certificate_sha256']==expected_inputs['mixed_split_complete_weighted_boundary_certificate.json'],'501 certificate binding')
need(r501['weight']==c501['weight']==[17,16,13] and r501['literal_weighted_capacity']==892 and F(r501['weighted_survivor_lower'])*616==32,'old fixed-weight bound remains 32')
need([b['clip'] for b in certificate['branches']]==[[[1,0,0],20],[[-1,0,0],-20]],'two closed regions cover axis domain at 20')
c=source_inputs['integer_selector_tail_interface_certificate.json']
r=source_inputs['integer_selector_tail_interface.json']['axis_realizations'][0]
P=((4,2,-4,1,2,1,1),(5,-2,4,1,1,1,1),(-5,-3,-2,1,1,1,1))
need(tuple(map(tuple,c['cases'][0]['profiles']))==tuple(map(tuple,r['profiles']))==tuple(map(tuple,c501['profiles']))==tuple(map(tuple,r501['profiles']))==tuple(map(tuple,certificate['profiles']))==P,'same three profiles')
prime=c['old_primes'];boxes=[]
for s in P:
 boxes.append(tuple(set(product(*(range(v) for v in x))) for x in (tuple(max(1,v) for v in s[:3])+s[3:],tuple(max(1,-v) for v in s[:3])+s[3:])))
exps=set().union(*(a|b for a,b in boxes));labels=[]
for e in sorted(exps):
 d=prod(p**v for p,v in zip(prime,e))
 need(r['old_carrier']%d==0,'stable old label')
 masks=[[int(x%d==centre%d) for x in r['old_points']] for centre in r['old_centres']]
 need(masks==[[int(e in pair[j]) for pair in boxes] for j in (0,1)],'CRT and box activation masks agree')
 labels.append({'d':d,'A':masks[0],'B':masks[1]})
need(len(labels)==51 and len({x['d'] for x in labels})==51,'51 unique literal old labels')
need(labels==certificate['literal_labels'] and all(certificate[k]==r[k] for k in ('old_points','old_centres','old_carrier')) and certificate['old_primes']==prime,'retained literal CRT inventory')
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def N(v):return sum(max(dot(v,x['A']),dot(v,x['B'])) for x in labels)
W=((1,0,0),(0,1,0),(1,1,0),(0,0,1),(1,0,1),(0,1,1),(1,1,1),(1,1,2),(1,2,1),(2,1,1))
capacities=[N(v) for v in W]
need(capacities==[22,21,39,30,45,42,58,85,78,79],'all ten original axis capacities')
need(list(map(list,W))==certificate['axis_directions'] and set(W)==set(map(tuple,c501['complete_axis_directions'])) and capacities==certificate['axis_capacities'],'same complete axis directions and capacities')
weight=(17,16,13);need(N(weight)==892 and certificate['original_weight']==list(weight) and certificate['original_capacity']==892,'old weighted inventory')
def det(a):return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])
def constraints(h,clip=None):
 out=[(v,n) for v,n in zip(W,capacities)]
 for i in range(3):
  e=tuple(int(i==j) for j in range(3));out.append((e,h));out.append((tuple(-x for x in e),0))
 if clip is not None:out.append(clip)
 return out
def vertices(cons):
 out={};nonsingular=0
 for ids in combinations(range(len(cons)),3):
  A=[cons[i][0] for i in ids];b=[cons[i][1] for i in ids];den=det(A)
  if not den:continue
  nonsingular+=1;v=[]
  for j in range(3):
   Aj=[[b[i] if k==j else A[i][k] for k in range(3)] for i in range(3)]
   v.append(F(det(Aj),den))
  v=tuple(v)
  if all(dot(a,v)<=b for a,b in cons):out.setdefault(v,ids)
 return sorted(out),out,nonsingular
U,ua,un=vertices(constraints(28));need(len(U)==22,'complete u vertex count')
need(json.loads(json.dumps([{'point':list(map(str,u)),'active_rows':ua[u]} for u in U]))==certificate['u_vertices'],'retained complete u vertices')
branches=[];total=0
for name,clip,v,n,expected_count,expected_min in [('t1_le_20',((1,0,0),20),(17,9,8),671,15,41),('t1_ge_20',((-1,0,0),-20),(9,16,9),662,12,92)]:
 need(N(v)==n,'independent branch capacity')
 V,active,ns=vertices(constraints(22,clip));need(len(V)==expected_count,'complete clipped t vertex count')
 values=[(sum(vi*(22-ti)*(28-ui) for vi,ti,ui in zip(v,t,u))-n,t,u) for t in V for u in U]
 minimum=min(x[0] for x in values);need(minimum==expected_min,'exact branch global minimum')
 need(all(0<=vi<=wi for vi,wi in zip(v,weight)) and sum(v)==34,'weight domination and total')
 total+=len(values)
 branches.append({'region':name,'clip':clip,'weight':v,'capacity':n,'t_vertex_count':len(V),'u_vertex_count':len(U),'checked_vertex_pairs':len(values),'minimum':str(minimum),'minimizers':[{'t':list(map(str,t)),'u':list(map(str,u))} for value,t,u in values if value==minimum],'t_vertices':[{'point':list(map(str,t)),'active_rows':active[t]} for t in V],'nonsingular_active_triples':ns})
need(total==594,'all 594 vertex pairs checked')
# Directly check the two specifically claimed attaining points, separately.
for v,t,u,n,m in [((17,9,8),(18,21,18),(22,12,23),671,41),((9,16,9),(21,18,19),(15,21,21),662,92)]:
 need(t in [tuple(F(x) for x in entry['point']) for branch in branches if branch['weight']==v for entry in branch['t_vertices']] and tuple(map(F,u)) in U,'claimed minimizer is independently enumerated')
 need(sum(vi*(22-ti)*(28-ui) for vi,ti,ui in zip(v,t,u))-n==m,'claimed minimizing value')
for b,retained in zip(branches,certificate['branches']):
 content={k:v for k,v in b.items() if k not in ('t_vertex_count','u_vertex_count','checked_vertex_pairs','minimizers','nonsingular_active_triples')}
 need(json.loads(json.dumps(content))==retained,'retained exact branch certificate')
out={'verified':True,'certificate_sha256':hashlib.sha256(CERT.read_bytes()).hexdigest(),'literal_label_count':len(labels),'axis_capacities':capacities,'branches':[{k:v for k,v in b.items() if k not in ('t_vertices','nonsingular_active_triples')} for b in branches],'vertex_pairs_checked':total,'uniform_616_weighted_survivor_lower':'41','uniform_max_survivor_lower':str(F(41,616*34)),'scope':'Exact minima of the declared two polytope branches and same-family budget transport, not arithmetic sharpness, a new Boolean edge, or a global source-mass improvement. Ordinary proof plus exact arithmetic, not Lean verification.','inputs':certificate['inputs'],'profiles':certificate['profiles'],'old_fixed_objective_minimum':'32','original_weight':list(weight),'original_capacity':892}
out=json.loads(json.dumps(out))
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(out==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained exact result mismatch')
print(json.dumps({'literal_label_count':len(labels),'branch_vertex_pairs':[b['checked_vertex_pairs'] for b in branches],'branch_minima':[b['minimum'] for b in branches],'weighted_bound':out['uniform_616_weighted_survivor_lower'],'max_survivor_bound':out['uniform_max_survivor_lower']},indent=2))
