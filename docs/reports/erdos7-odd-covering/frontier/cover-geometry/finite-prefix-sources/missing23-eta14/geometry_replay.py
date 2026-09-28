"""Explicit integer-geometry replay for one fixed missing23 comparison node.

Default is cache-only. --fresh permits generating missing full-input geometry
keys. Source thresholds remain fixed. No all-anchor or all-eta claim.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from functools import lru_cache
from hashlib import sha256
import runpy,subprocess,json,time,hashlib

ROOT=Path(__file__).resolve().parent

# This literal pin fixes every numerical prerequisite, source and retained raw
# support-rebuild result. Dynamic hash reporting alone would not certify input.
MANIFEST_SHA256 = "812771d19270ad2447fbacd1d59a045ba6a04d5bb9580d86679678490adce091"
def check_inputs():
    raw=(ROOT/'inputs.sha256.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=MANIFEST_SHA256:
        raise ValueError('fixed input manifest mismatch')
    manifest=json.loads(raw)
    for name,expected in manifest.items():
        if Path(name).is_absolute() or '..' in Path(name).parts:
            raise ValueError('invalid manifest-relative path')
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=expected:
            raise ValueError('pinned input mismatch: '+name)
check_inputs()
v=runpy.run_path(str(ROOT/'source_model.py'))
node=(2,4,1,8,1,2,1,0,13);xi7=xi13=(1,4,7,14);cs=v['cells'](2,4,8)
root=ROOT/'geometry-cache'
cachefolders=(root,)
ALLOW_GENERATE=False
REGENERATE=False
ENUMERATOR=ROOT/'geometry-enumerator'
K7=(11,11,9,6,3)
K11=tuple(int(33*(min(F(1),F(5,3)*F(10-s,11))-F(5,33))) for s in range(5))
if K11!=(28,28,28,28,25):raise ValueError('correct first11 forbidden-root accounting')

# Prefix tree permutation2<->5 mod9 transports the residualB2 andB5 cases.
crt={(x%27,x%5):x for x in range(135)}
def perm(x):
 y=x%27
 if y%9==2:y+=3
 elif y%9==5:y-=3
 return crt[y,x%5]
pi=tuple(perm(x) for x in range(135))
if sorted(pi)!=list(range(135)) or {perm(x) for x in cs}!=set(cs):raise ValueError('prefix permutation domain')
for m in (*v['MODS'],135):
 images=[{perm(x)%m for x in range(135) if x%m==r} for r in range(m)]
 if not all(len(s)==1 for s in images) or len({next(iter(s)) for s in images})!=m:raise ValueError('category permutation')
for reg in v['REGIONS']:
 ws=dict(zip(cs,v['weights'](node,reg)))
 if not all(ws[x]==ws[perm(x)] for x in cs):raise ValueError('anchor weight permutation')
for x in cs:
 if v['counts']((x,),xi7)!=v['counts']((perm(x),),xi7):raise ValueError('fixed7/13 field permutation')
 if v['counts']((x,),(2,4,2,14))!=v['counts']((perm(x),),(2,4,5,14)):raise ValueError('physical11 permutation')

support=json.loads((ROOT/'support.json').read_text())
def support_env(key):
 e=support[key];return F(e['mass']),F(e['whole']),{F(k):F(x) for k,x in e['values'].items()}
BASE={(0,0,0):support_env('ordinary'),(1,0,0):support_env('zero')}
K13=tuple(int(26*(min(F(1),F(3,2)*F(12-s,13))-F(3,26))) for s in range(5))
if K13!=(23,23,23,23,21):raise ValueError('correct zero13 table')
NEW={};USED={}

def co(u,w,m,p,mode):
 out=list(v['coefficients']('ordinary',u,w,m))
 if p:
  for i in ((4,) if mode=='released' else (0,1,3,4)):out[i]-=F(p-1,p)
 if min(out)<0:raise ValueError('nonnegative free-category coefficients')
 return out

def cell_weights(reg,part,xi11,xi13field):
 ws=v['weights'](node,reg)
 if part[0]:ws=tuple(w*K7[s] for w,s in zip(ws,v['counts'](cs,xi7)))
 if part[1]:ws=tuple(w*K11[s] for w,s in zip(ws,([0]*len(cs) if xi11 is None else v['counts'](cs,xi11))))
 if part[2]:ws=tuple(w*K13[s] for w,s in zip(ws,([0]*len(cs) if xi13field is None else v['counts'](cs,xi13field))))
 return ws


def geometry(ws,reg,m,p,t,xip,mode):
 uv=tuple(product(range(1,12) if reg[0] else (0,),range(1,9) if reg[1] else (0,)))
 counts=tuple(int(x%15==xip[3]) for x in cs) if mode=='released' else v['counts'](cs,xip)
 off=[(p-1)*s for s in counts] if p else [0]*len(cs)
 base_m=0 if mode=='prefix7' else m
 den=p or 1;ts=(t,) if p else range(1,29)
 lines=[str(len(cs))]+[f'{x} {w} {o}' for x,w,o in zip(cs,ws,off)];labels=[];bounds=[]
 if not all(0<=w<2**31 and 0<=o<2**31 for w,o in zip(ws,off)):raise ValueError('C++32 cell input range')
 for u,w in uv:
  c=co(u,w,m,p,mode);ic=[int(den*x) for x in c]
  if not all(F(x,den)==y for x,y in zip(ic,c)):raise ValueError('integer query coefficients')
  for tt in ts:
   lines.append(' '.join(map(str,[len(labels),den,den*base_m,*ic,den*tt])));labels.append((u,w,tt))
   bound=sum(weight*max(0,den*base_m+offset+sum(ic)-den*tt) for weight,offset in zip(ws,off))
   if not 0<=bound<2**63 or not -2**63<den*base_m-den*tt or not den*base_m+max(off)+sum(ic)<2**63:raise ValueError('C++64 proven arithmetic range')
   bounds.append(bound)
 body='\n'.join(lines)+'\n';key=sha256(body.encode()).hexdigest()
 existing=None if REGENERATE else next((folder/(key+'.json') for folder in cachefolders if (folder/(key+'.json')).exists()),None)
 if existing:raw=json.loads(existing.read_text())
 else:
  if not ALLOW_GENERATE:raise FileNotFoundError('Missing geometry '+key+'; provide --cache or explicitly use --fresh')
  root.mkdir(exist_ok=True)
  started=time.monotonic();r=subprocess.run([str(ENUMERATOR)],input=body,text=True,capture_output=True,check=True)
  raw=[list(map(int,line.split())) for line in r.stdout.splitlines()]
  (root/(key+'.json')).write_text(json.dumps(raw,separators=(',',':'))+'\n')
  NEW[key]=dict(queries=len(labels),seconds=time.monotonic()-started)
 if len(raw)!=len(labels) or not all(row[0]==i and row[1]==den and 0<=row[2]<=bounds[i] for i,row in enumerate(raw)):raise ValueError('integer geometry output')
 USED[key]=len(raw);table={label:F(row[2],den) for label,row in zip(labels,raw)}
 inc=[max(sum(w for x,w in zip(cs,ws) if x%g==r) for r in range(g)) for g in v['MODS']]
 mass,mx=sum(ws),max(ws);offset=sum((F(w*o,den) for w,o in zip(ws,off)),F(0))
 def linear(u,w):
  c=co(u,w,m,p,mode)
  return base_m*mass+sum(a*b for a,b in zip(c,inc))+c[6]*mx+offset
 return table,linear,mass,tuple(ts)

@lru_cache(None)
def envelope(part,xi11,xi13field,m=1,p=0,t=0,xip=(1,4,7,14),mode="four"):
 # A spatially constant zero numerator scales every maximum homogeneously.
 if part[1] and xi11 is None:
  a,w,values=envelope((part[0],0,part[2]),xi11,xi13field,m,p,t,xip,mode)
  return 28*a,28*w,{k:28*x for k,x in values.items()}
 if part[2] and xi13field is None:
  a,w,values=envelope((part[0],part[1],0),xi11,xi13field,m,p,t,xip,mode)
  return 23*a,23*w,{k:23*x for k,x in values.items()}
 A=W=F(0);vals=None
 for reg in v['REGIONS']:
  ws=cell_weights(reg,part,xi11,xi13field)
  table,linear,mass,ts=geometry(ws,reg,m,p,t,xip,mode)
  if vals is None:vals={F(tt):F(0) for tt in ts}
  ud,ur,ut,ua=v['depth'](3,reg[0],12);vd,vr,vt,va=v['depth'](5,reg[1],9)
  scale=F(1,(1 if reg[0] else 6)*(1 if reg[1] else 20))
  def integral(a,b):return a[0]*b[0]*linear(a[1]/a[0],b[1]/b[0]) if a[0] and b[0] else F(0)
  tail=integral(ut,va)+integral(ur,vt)
  if tail<0:raise ValueError('positive anchor remainder')
  A+=scale*ua[0]*va[0]*mass;W+=scale*integral(ua,va)
  for tt in vals:vals[tt]+=scale*(sum(p*q*table[u,w,tt] for u,p in ud for w,q in vd)+tail)
 return A,W,vals

@lru_cache(None)
def correction(part,xi11,xi13field,xip,mode):
 ans=F(0)
 for reg in v['REGIONS']:
  ws=cell_weights(reg,part,xi11,xi13field)
  scale=F(1,(1 if reg[0] else 6)*(1 if reg[1] else 20))
  scale*= (F(1,3) if reg[0] else 1)*(F(1,5) if reg[1] else 1)
  heads=sum(max(sum(w for x,w in zip(cs,ws) if x%g==r) for r in range(g)) for g in ((15,) if mode=='released' else (3,5,9,15)))
  ans+=scale*(sum(w*s for w,s in zip(ws,(tuple(int(x%15==xip[3]) for x in cs) if mode=='released' else v['counts'](cs,xip))))-heads)
 return ans

cutoff=20
unit=({1:F(1)},F(1),F(1))
pos7=({m:F(9,7**m) for m in range(2,cutoff)},F(13,28),F(3,14))
pos11=({m:F(50,3*11**m) for m in range(2,cutoff)},F(7,22),F(5,33))
COEF={part:F(1,14**part[0]*33**part[1]*26**part[2]) for part in product((0,1),repeat=3)}
pos13=({m:F(18,13**m) for m in range(2,cutoff)},F(25,104),F(3,26))
def mul(a,b):
 out=defaultdict(F)
 for m,w in a[0].items():
  for n,p in b[0].items():
   if m*n<cutoff:out[m*n]+=w*p
 return dict(out),a[1]*b[1],a[2]*b[2]

def upper(t,env):
 A,W,vals=env
 if t<=1:return W-t*A
 if t in vals:return vals[t]
 if t>=max(vals):return vals[max(vals)]
 lo=max(a for a in vals if a<t);hi=min(a for a in vals if a>t)
 return ((hi-t)*vals[lo]+(t-lo)*vals[hi])/(hi-lo)

def hinge(t,dist,env):
 table,mean,prob=dist;A,W,_=env;low={m:w for m,w in table.items() if m<t}
 pr=sum(low.values(),F(0));mm=sum((m*w for m,w in low.items()),F(0))
 if not 0<=pr<=prob or not 0<=mm<=mean:raise ValueError('positive multiplier remainder')
 ans=sum((m*w*upper(F(t,m),env) for m,w in low.items()),F(0))+(mean-mm)*W-t*(prob-pr)*A
 if ans<0:raise ValueError('nonnegative hinge')
 return ans

def current(parts,xi11,xi13field,xip,p,t,mode="four"):
 ans=F(0);details=[]
 for part,dist in parts.items():
  table,mean,prob=dist;low={m:w for m,w in table.items() if m<t}
  pr=sum(low.values(),F(0));mm=sum((m*w for m,w in low.items()),F(0))
  if not 0<=pr<=prob or not 0<=mm<=mean:raise ValueError('positive multiplier remainder')
  A,W,_=envelope(part,xi11,xi13field)
  cor=correction(part,xi11,xi13field,xip,mode)
  tail=(mean-mm)*W+(prob-pr)*(F(p-1,p)*cor-t*A)
  if tail<0:raise ValueError('positive current multiplier tail')
  lowvalue=sum((w*envelope(part,xi11,xi13field,m,p,t,xip,mode)[2][F(t)] for m,w in low.items()),F(0))
  ans+=COEF[part]*(lowvalue+tail)
  details.append(dict(part=part,low_m=list(low),tail_probability=str(prob-pr),tail_mean=str(mean-mm),correction=str(cor),low_value=str(lowvalue),tail_value=str(tail),coefficient=str(COEF[part])))
 return v['up'](ans/(p-1-t)),details

def initial_parts():
 return {part:mul(mul(unit if part[0] else pos7,unit if part[1] else pos11),unit if part[2] else pos13) for part in COEF}

def full(p,t):
 C=F(p-1,p-1-t)
 return ({m:1-C/p if m==1 else C*F(p-1,p**m) for m in range(1,cutoff)},1+C/F(p-1),F(1))


def main():
 global cachefolders,ALLOW_GENERATE,ENUMERATOR,REGENERATE
 import argparse
 parser=argparse.ArgumentParser()
 parser.add_argument('--stage',choices=('ordinary','7','11','13','17','19','29'),required=True)
 parser.add_argument('--xi11',default='2,4,2,14');parser.add_argument('--xi13',default='2,4,5,14')
 parser.add_argument('--projection',default='1,4,7,14');parser.add_argument('--part',default='0,0,0')
 parser.add_argument('--mode',choices=('four','released'),default='four')
 parser.add_argument('--eta',type=int,default=14);parser.add_argument('--all40',action='store_true')
 parser.add_argument('--zero13',action='store_true');parser.add_argument('--flat11',action='store_true');parser.add_argument('--flat13',action='store_true')
 parser.add_argument('--cache',type=Path,action='append',default=[]);parser.add_argument('--fresh',action='store_true')
 parser.add_argument('--regenerate',action='store_true',help='explicitly rerun even cached integer maxima')
 parser.add_argument('--binary',type=Path);parser.add_argument('--output',type=Path)
 args=parser.parse_args();cachefolders=tuple(args.cache)+(root,);REGENERATE=args.regenerate;ALLOW_GENERATE=args.fresh or REGENERATE
 if args.binary:ENUMERATOR=args.binary
 if ALLOW_GENERATE and not ENUMERATOR.exists():subprocess.run(['c++','-O2','-std=c++17',str(ROOT/'geometry.cpp'),'-o',str(ENUMERATOR)],check=True)
 x11=None if args.flat11 else tuple(map(int,args.xi11.split(',')))
 x13=None if args.flat13 else tuple(map(int,args.xi13.split(',')))
 xip=tuple(map(int,args.projection.split(',')))
 if args.mode=='released':
  for i,modulus in ((0,3),(1,5),(2,9)):
   if {x[i] for x in v['PROJECTIONS'] if x[-1]==args.eta}!={x%modulus for x in cs}:raise ValueError('full released domain')
 if args.stage=='ordinary':
  part=tuple(map(int,args.part.split(',')));a,w,values=envelope(part,x11,x13)
  result=dict(part=part,mass=str(a),whole=str(w),values={str(k):str(x) for k,x in values.items()})
 elif args.stage=='7':
  a,w,values=envelope((0,0,0),x11,x13,1,7,1,(1,4,7,14),'prefix7')
  result=dict(stage=7,cost=str(v['up'](values[F(1)]/4)))
 else:
  p=int(args.stage);threshold={11:4,13:4,17:8,19:8,29:16}[p]
  if p==11:parts={(a,0,0):unit if a else pos7 for a in (0,1)}
  elif p==13 or p==17 and not args.zero13:
   parts={(a,b,0):mul(unit if a else pos7,unit if b else pos11) for a,b in product((0,1),repeat=2)}
   if p==17:parts={k:mul(d,full(13,4)) for k,d in parts.items()}
  else:
   parts=initial_parts()
   for q,t in ((17,8),(19,8)):
    if q<p:parts={k:mul(d,full(q,t)) for k,d in parts.items()}
  projections=tuple(x for x in v['PROJECTIONS'] if x[-1]==args.eta) if args.all40 else (xip,)
  rows=[]
  for projection in projections:
   cost,_=current(parts,x11,x13,projection,p,threshold,args.mode)
   rows.append(dict(xi=projection,cost=str(cost)))
  result=dict(stage=p,mode=args.mode,xi11=x11,xi13=x13,rows=rows)
 result.update(new_batches=len(NEW),new_queries=sum(x['queries'] for x in NEW.values()),used_batches=len(USED),used_queries=sum(USED.values()))
 text=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(text)
 print(text,end='')

if __name__=='__main__':main()
