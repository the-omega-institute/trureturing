#!/usr/bin/env python3
"""Small exact replay for a central-only infinite-Haar-centre dual.

No optimizer or dense source/centre matrix. Source categories and fees are
reconstructed by the canonical source engine, then factorized with its
at-most-one-root1 predicate. All decisions use Fraction and integers.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from hashlib import sha256
import importlib.util,argparse,json,time

ap=argparse.ArgumentParser()
ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent)
ap.add_argument('--witness',type=Path,default=Path(__file__).with_name('joined33_central_only_infinite_dual_witness.json'))
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
ap.add_argument('--metrics',type=Path)
a=ap.parse_args();base=Path(a.base);w=json.loads(Path(a.witness).read_text());start=time.perf_counter();checks=0
def ck(p,msg):
    global checks
    checks+=1
    if not p:raise ArithmeticError(msg)
ck(w['schema']=='central-only-infinite-centre-subprobability-dual-v1','witness schema')
D=w['denominator'];ck(type(D) is int and D>0,'positive integer common budget')
engine_path=base/'clustered_full5_allfield_verify.py'
ck(sha256(engine_path.read_bytes()).hexdigest()==w['source_engine_sha256']=='edc32a8aff0e0fb8319e448da05a882b618d74ea97412cacdb5412bf1c7aca56','pinned source engine')
sp=importlib.util.spec_from_file_location('canonical_source',engine_path);core=importlib.util.module_from_spec(sp);sp.loader.exec_module(core)
class Empty:
    def read_text(self):return json.dumps({'schema':'clustered109-full5-rational-dual-v1','source_sha256':w['source_sha256'],'denominator':D,'rows':[],'expected':{}})
p=core.prepare(base,Empty(),D);Q=core.Q;P=(3,5,*Q);g=core.G;c=1-g
ck([list(z) for z in p['cells']]==w['source_cells'],'same80 central cells')
ck(w['centre_depths']==[2,2,1,1,1,1,1] and w['centre_tails']=='independent Haar at all prime axes','declared centre interface')
C=list(map(F,json.loads((base/'remaining33_global_root_exclusion_certificate.json').read_text())['combined512_coefficients']))
for i,q in enumerate(Q):
    if i:C[256+(1<<i)]+=g/F(q*(q-2))
W=[]
for j in range(512):
    mode,T=divmod(j,32);ex,ey=divmod(mode,4)
    z=(F(1),F(3),F(5),F(8,9))[ex]*(F(1),F(3),F(5),F(1,8))[ey]
    for i,q in enumerate(Q):
        if T>>i&1:z*=F(3,q-1)+F(5*q-3,(q-2)*(q-1)**2)
    W.append(z if j else F(0))
A=[fee-c*weight for fee,weight in zip(C,W)]
ck(min(A)>=0 and list(map(str,A))==w['remaining_coefficients'],'all same loss-only fees')
groups=[j for j,z in enumerate(A) if z>0]
ck(len(groups)==499 and groups==w['query_groups'],'same499 positive query groups')

selectors=[]
ls=(0,1,2,4,5);ms=tuple(x for x in range(20) if x!=5)
for mode in range(16):
    ex,ey=divmod(mode,4)
    for left,right in product(((0,),(0,1),ls,ls)[ex],((0,),(0,1,2,3),ms,ms)[ey]):
        ids=[i for i,(l,m) in enumerate(p['cells']) if (ex==0 or (l//3==left if ex==1 else l==left)) and (ey==0 or (m//5==right if ey==1 else m==right))]
        mult=F(1)
        if ex==3:mult*=(F(81,82) if left==4 else 1)/F(2-(left==4),9)
        if ey==3:mult*=F(4,5)*(F(1875,1876) if right==10 else 1)/F(4-(right==10),75)
        selectors.append((mode,ids,mult))
ck(len(selectors)==559,'complete exact selector list')

def scalar(ci):
    l,m=p['cells'][ci];return F((2-(l==4))*(4-(m==10)),p['M0'])
def contract(ci,factors):
    # All counts are literal source category cardinalities. Special and
    # other children of root1 are cats0,1; the joint source allows at most
    # one coordinate in their union.
    U=[];V=[]
    for counts,phi in zip(p['counts'][ci],factors):
        V.append(sum((counts[k]*phi[k] for k in (0,1)),F(0)))
        U.append(sum((counts[k]*phi[k] for k in range(2,len(counts))),F(0)))
    return scalar(ci)*(prod(U)+sum((V[i]*prod(U[j] for j in range(5) if j!=i) for i in range(5)),F(0)))
ones=[[F(1)]*len(cats) for cats in p['cats']]
masses=[contract(ci,ones) for ci in range(80)]
source_mass=sum(masses,F(0))
ck(source_mass==F(305684996597,646498195200),'exact source mass')

def query_coeff(sid,col):
    mode,ids,mult=selectors[sid]
    coords=[];rem=col
    for n in reversed(p['token_shape']):coords.append(rem%n);rem//=n
    coords.reverse();ck(rem==0,'query column range')
    factors=[]
    for qi,(q,k) in enumerate(zip(Q,coords)):
        scale=5 if q==19 else 1
        factors.append([F(dict(row).get(k,0),scale) for row in p['matrices'][qi]])
    return {ci:mult*contract(ci,factors) for ci in ids},sum((1<<i) for i,k in enumerate(coords) if k)

def Fmatch(q,h,E=None):
    if E is None:return F((h+1)**2)+F(2*(h+1),q-1)+F(q+1,(q-1)**2)
    return F((h+1)**2)+sum((F(2*(h+j)+1,q**j) for j in range(1,E-h+1)),F(0))
roots=[tuple(range(min(q,9)))+((9,) if q>9 else ()) for q in Q]
def centre_coeff(idx,E=None):
    a3,a5,*ext=idx
    ck(0<=a3<9 and 0<=a5<25 and all(0<=i<len(rs) for i,rs in zip(ext,roots)),'full shallow centre indices')
    factors=[]
    for qi,(q,i) in enumerate(zip(Q,ext)):
        centre=roots[qi][i];add=Fmatch(q,1,E)-1;phi=[]
        for k in range(len(p['cats'][qi])):
            root=1 if k<2 else k
            eq=F(int(root==centre),q-9 if root==9 else 1)
            phi.append(1+add*eq)
        factors.append(phi)
    out=[]
    for ci,(l,m) in enumerate(p['cells']):
        z=F(1)
        for q,x,aa in ((3,3*(l%3)+l//3,a3),(5,5*(m%5)+m//5,a5)):
            r=0
            while r<2 and (x-aa)%q**(r+1)==0:r+=1
            z*=Fmatch(q,2,E) if r==2 else (r+1)**2
        out.append(z*contract(ci,factors)-masses[ci])
    ck(min(out)>=0,'unit-subtracted centre charge nonnegative')
    return out

budgets={j:0 for j in groups};budgets['centre']=0
debit=[F(0)]*80;centre_rows=[];query_rows=[];seen=set()
for entry in w['rows']:
    row=entry['row'];num=entry['numerator'];key=tuple(row)
    ck(key not in seen and type(num) is int and num>0,'distinct positive witness row');seen.add(key)
    weight=F(num,D)
    if row[0]=='q':
        _,gid,sid,col=row
        ck(gid in budgets and gid!='centre' and 0<=sid<len(selectors) and type(col) is int and col>=0,'query address')
        coeff,T=query_coeff(sid,col)
        ck(selectors[sid][0]==gid//32 and T==gid%32,'query group support and selector mode')
        budgets[gid]+=num;query_rows.append(entry)
        for ci,z in coeff.items():debit[ci]+=weight*A[gid]*z
    else:
        ck(row[0]=='c' and len(row)==8,'centre row shape');budgets['centre']+=num;centre_rows.append(entry)
        coeff=centre_coeff(row[1:])
        for ci,z in enumerate(coeff):debit[ci]+=weight*c*z
ck(all(0<=n<=D for n in budgets.values()),'exact substochastic budgets')
residual=[g*m-d for m,d in zip(masses,debit)]
upper=sum((max(F(0),r) for r in residual),F(0));target=F(193,100000)
ck(upper<target,'central-only infinite dual below target')

# Same law, finite equal exponent floors: the centre-kernel truncation
# difference is at most the product of matched factors' tail difference,
# uniformly in x and in the selected shallow centre. No Gamma-tail assertion.
beta_mass=F(budgets['centre'],D);infprod=prod(Fmatch(q,h) for q,h in zip(P,w['centre_depths']))
tail_records=[];threshold=None
for e in range(6,31):
    delta=infprod-prod(Fmatch(q,h,e) for q,h in zip(P,w['centre_depths']))
    corrected=upper+c*source_mass*beta_mass*delta
    tail_records.append({'all_exponents_at_least':e,'tail_debit_bound':str(c*source_mass*beta_mass*delta),'central_upper_bound':str(corrected),'below_target':corrected<target})
    if corrected<target:threshold=e;break
ck(threshold is not None,'finite-height uniform correction crosses target')
out={'status':'PASS','exact':True,'checks':checks,'canonical_source_checks':core.CHECKS,
    'source_mass':str(source_mass),'query_rows':len(query_rows),'centre_rows':len(centre_rows),
    'central_cells':80,'denominator':D,'positive_central_residuals':sum(r>0 for r in residual),
    'central_box_upper':str(upper),'central_box_upper_decimal':float(upper),'target':str(target),'margin':str(target-upper),
    'centre_probability_mass':str(beta_mass),'finite_equal_floor_threshold':threshold,'tail_records':tail_records,
    'central_residuals':list(map(str,residual)),
    'witness_sha256':sha256(Path(a.witness).read_bytes()).hexdigest(),
    'source_engine_sha256':sha256(engine_path.read_bytes()).hexdigest(),
    'verifier_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
    'scope':'Exact feasible dual only for f depending on the80 central cells, actual109 source and all unchanged A_j fees. Charged centre family fixes h=(2,2,1,1,1,1,1) and has independent Haar prime tails. Its infinity upper extends by the displayed centre-kernel tail correction to every finite exponent vector above the reported common floor. No conclusion for arbitrary source-dependent retention, arbitrary deep coherent centres, true independent-layout Gamma positivity, or unrestricted covering.'}
Path(a.output).write_text(json.dumps(out,indent=2)+'\n')
if a.metrics:a.metrics.write_text(json.dumps({'elapsed_seconds':time.perf_counter()-start},indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('central_residuals','tail_records')},indent=2))
