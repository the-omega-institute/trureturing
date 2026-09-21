#!/usr/bin/env python3
"""Exact branch-table audit for eight-prime cores containing {3,5}.

This is an ordinary conditional arithmetic certificate only. It covers the
three omitted-prime regimes not containing both 7 and 11, using the pinned
Chapter-30 geometry/source helpers and Chapter-23 six-child CK rows. It does
not prove unrestricted Erdős--Selfridge #7 or replay external source theorems.
"""
from fractions import Fraction as Q
from importlib.util import module_from_spec, spec_from_file_location
from hashlib import sha256
from math import prod
from pathlib import Path
import argparse
import json, sys

BASE = Path(__file__).resolve().parent
GEOM=BASE/'six_prime_prefix_geometry.json'; GH=BASE/'six_prime_prefix_certificate.py'
SH=BASE/'spine_book_certificate.py'; VH=BASE/'variable_eight_core_certificate.py'
SHA={
 'geometry':'0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1',
 'geometry_helper':'3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4',
 'source_helper':'601c9c94018ab960abe63a126c1cf0d96b84b6b335ef5630c84adfb113db44de',
 'variable_helper':'45b59fa2d0127d6dbaaa46a9dd4046bc0e4537888f864153f95f8496f500a7e6',
}
T=(2,4,4,8,8,12)
SCHEDULE={13:5,17:8,19:10,23:13,29:16,31:19,37:23,41:26,43:28,47:30,53:30}

def load(name,p):
    sp=spec_from_file_location(name,p); m=module_from_spec(sp); sp.loader.exec_module(m); return m

def sh(p): return sha256(p.read_bytes()).hexdigest()

def prime(n): return n>1 and all(n%d for d in range(2,int(n**.5)+1))

def setup():
    for key,p in [('geometry',GEOM),('geometry_helper',GH),('source_helper',SH),('variable_helper',VH)]: assert sh(p)==SHA[key], (key,sh(p))
    geom=json.loads(GEOM.read_text()); assert geom['schema']=='six-prime-prefix-geometry-input-v1'; assert len(geom['batches'])==72
    helper=load('ordinary_geometry',GH); source=load('ordinary_source',SH); variable=load('ck_rows',VH)
    nodes=sorted((a,b,c,-1,j,0,0,0,-1) for a in (1,2) for b in (2,4) for c in (a,3-a) for j in range(1,5)); assert len(nodes)==32
    env=[]
    for node in nodes:
      a,b,c,_,j,*_=node; gamma=3*(a==1)+(b%3==a%3); reserve=Q(135,4)+gamma+(9-gamma)*(Q(c==a,5)+Q(j==a,20)); env.append((node,reserve,helper.envelope(geom['batches'],a,b,c,j)))
    return geom,helper,source,variable,env

def k_rows(variable):
    out={}
    out[11]=Q(variable.ck(tuple(q for q in range(11,200) if prime(q))[:6],4)['K3'])
    for s,t in SCHEDULE.items():
      out[s]=Q(variable.ck(tuple(q for q in range(s,200) if prime(q))[:6],t)['K3'])
    return out

def source_mass(source,helper,env,q):
    row=source.source_mass(helper,env,q,T); m=Q(row['mass_lower_bound']); caps=(Q(1),Q(1))+tuple(Q(p-1,p-1-t) for p,t in zip(q,T)); D=prod(caps)
    return m,D,row

def rows_sum(k,start): return sum((v for p,v in k.items() if p>=start and p<=53),Q(0))

def main():
    geom,helper,source,variable,env=setup(); k=k_rows(variable)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=None)
    args = parser.parse_args()
    f={7:Q(1,8),11:Q(1,24),13:Q(1,48)}
    for p in (17,19,23,29,31,37,41,43,47,53): f[p]=Q(1,2**((p-1)//2))
    assert f[7]==Q(1,8) and f[11]==Q(1,24) and f[13]==Q(1,48)
    # expected rows are generated in six ordinary profile branches. For an
    # omitted small prime r, all possible outside minima >=r are charged by
    # the corresponding CK rows, followed by the all-large tail 2^-28.
    branches=[]
    # contains 7, omits 11: k11 is the omitted-11 direct attachment fee.
    for r,q in [
      (13,(7,17,19,23,29,31)),(17,(7,13,19,23,29,31)),
      (19,(7,13,17,23,29,31)),(23,(7,13,17,19,29,31)),
      (29,(7,13,17,19,23,31)),('exact',(7,13,17,19,23,29))]:
      m,D,row=source_mass(source,helper,env,q); start=31 if r=='exact' else r; B=k[11]+rows_sum(k,start)+Q(1,2**28); branches.append(('7-only',r,q,m,D,B,(m-B)/D))
    # contains 11, omits 7: f(7)=1/8 plus omitted-prime CK rows.
    for r,q in [
      (13,(11,17,19,23,29,31)),(17,(11,13,19,23,29,31)),
      (19,(11,13,17,23,29,31)),(23,(11,13,17,19,29,31)),
      (29,(11,13,17,19,23,31)),('exact',(11,13,17,19,23,29))]:
      m,D,row=source_mass(source,helper,env,q); start=31 if r=='exact' else r; B=Q(1,8)+rows_sum(k,start)+Q(1,2**28); branches.append(('11-only',r,q,m,D,B,(m-B)/D))
    # omits both 7 and 11: f(7)+f(11)=1/6 plus CK rows.
    for r,q in [
      (13,(17,19,23,29,31,37)),(17,(13,19,23,29,31,37)),
      (19,(13,17,23,29,31,37)),(23,(13,17,19,29,31,37)),
      (29,(13,17,19,23,31,37)),(31,(13,17,19,23,29,37)),
      ('exact',(13,17,19,23,29,31))]:
      m,D,row=source_mass(source,helper,env,q); start=37 if r=='exact' else r; B=Q(1,6)+rows_sum(k,start)+Q(1,2**28); branches.append(('neither',r,q,m,D,B,(m-B)/D))
    threshold=Q(1,2200000)
    assert len(branches)==19
    for regime,r,q,m,D,B,h in branches:
      assert m>B and h>threshold,(regime,r,q,float(m),float(B),float(h))
      print(regime, r, q)
      print('  m=',m,'D=',D,'B=',B,'haar=',h,'float=',float(h))
    # Exact source-row regression anchors (the SHA checks bind these to the
    # pinned geometry/helper inputs above).
    expected = {
      ('7-only',13): (Q(66317526337,675000000000),Q(66,7)),
      ('7-only',17): (Q(10953299081,135000000000),Q(297,28)),
      ('7-only',19): (Q(11342978047,150000000000),Q(11)),
      ('7-only',23): (Q(1024461671,15000000000),Q(63,5)),
      ('7-only',29): (Q(20922794137,337500000000),Q(99,7)),
      ('7-only','exact'): (Q(10237584019,168750000000),Q(297,20)),
      ('11-only',13): (Q(213580980617,1350000000000),Q(55,7)),
      ('11-only',17): (Q(196213424369,1350000000000),Q(495,56)),
      ('11-only',19): (Q(190546000687,1350000000000),Q(55,6)),
      ('11-only',23): (Q(15286810021,112500000000),Q(21,2)),
      ('11-only',29): (Q(29539443007,225000000000),Q(165,14)),
      ('11-only','exact'): (Q(7332516433,56250000000),Q(99,8)),
      ('neither',13): (Q(262837077859,1350000000000),Q(36,7)),
      ('neither',17): (Q(30759995083,168750000000),Q(27,5)),
      ('neither',19): (Q(241937042267,1350000000000),Q(28,5)),
      ('neither',23): (Q(235977277699,1350000000000),Q(324,55)),
      ('neither',29): (Q(77357156719,450000000000),Q(324,49)),
      ('neither',31): (Q(231164469293,1350000000000),Q(1188,175)),
      ('neither','exact'): (Q(229603051201,1350000000000),Q(264,35)),
    }
    for regime,r,q,m,D,B,h in branches:
      assert (m,D)==expected[(regime,r)]
    weak=min(branches,key=lambda x:x[-1]); print('weakest=',weak[0:3],float(weak[-1]))
    assert weak[0:2]==('7-only','exact')
    # Finite input identity assertions retained in output.
    assert k[11] == Q(46408,768123)
    assert k[13] == Q(499487,159722442)
    assert k[53] == Q(56140336,76935767377471116605271)
    out={'schema':'eight-prime-profile-budget-v1','scope':'Conditional ordinary transfer for actual eight-prime cores containing {3,5} but not both {7,11}; core containing both is handled by Chapter 38/variable certificate.','thresholds':list(T),'input_sha256':SHA,'f_fees':{str(p):str(v) for p,v in f.items()},'fee_rows':{str(p):str(v) for p,v in k.items()},'tail':'1/2^28','branches':[{'regime':regime,'first_missing':r,'proxy':list(q),'mass':str(m),'joint_cap':str(D),'budget':str(B),'haar_lower':str(h)} for regime,r,q,m,D,B,h in branches],'weakest':{'regime':weak[0],'first_missing':weak[1],'proxy':list(weak[2]),'haar_lower':str(weak[-1])},'monotonicity_scope':'For actual later-prime coordinates coordinatewise >= each proxy, inherited source coupling makes the unnormalised mass nondecreasing and each joint-cap factor nonincreasing; omitted-prime branch budgets dominate every possible outside minimum by distinct-minimum attachment decomposition. These monotonicity/transport facts are ordinary premises, not Lean-checked here.','unrestricted_erdos7':False}
    if args.output is not None:
      args.output.write_text(json.dumps(out,indent=2)+'\n')
    return branches

if __name__=='__main__':
    if sys.version_info<(3,10) or not __debug__: raise SystemExit('Python 3.10+ assertions required')
    main()
