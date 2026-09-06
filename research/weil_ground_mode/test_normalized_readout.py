"""Exact Gaussian-rational regression and negative tests for the readout disk.

These independent arithmetic checks are not extracted Lean and do not check
universal proof terms. Upstream spectral computations are not executed.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import random
import tempfile


def Z(x=0,y=0): return (F(x),F(y))
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def neg(x): return (-x[0],-x[1])
def sub(x,y): return add(x,neg(y))
def mul(x,y): return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def cj(x): return (x[0],-x[1])
def ns(x): return x[0]**2+x[1]**2
def inv(x):
    if not ns(x): raise ZeroDivisionError
    return (x[0]/ns(x),-x[1]/ns(x))
def div(x,y): return mul(x,inv(y))
def vmul(a,v): return tuple(mul(a,x) for x in v)
def vs(v,w): return tuple(sub(x,y) for x,y in zip(v,w))
def va(v,w): return tuple(add(x,y) for x,y in zip(v,w))
def norm2(v): return sum(map(ns,v),F(0))
def ip(v,w):
    s=Z()
    for x,y in zip(v,w): s=add(s,mul(cj(x),y))
    return s


def require(h,msg):
    if not h: raise AssertionError(msg)


def exact_tests():
    rng=random.Random(20260906)
    counts={"gaussian_cases":0,"attaining_witnesses":0,"rejected_queries":0,
            "sharp_boundary_cases":0,"degenerate_cases":0,
            "conjugation_mutations_detected":0,"covariance_sign_mutations_detected":0}
    def vec(n): return tuple(Z(F(rng.randint(-9,9),7),F(rng.randint(-9,9),11)) for _ in range(n))
    def check(b,c,d,a,e,r):
        D=ns(d)-e*norm2(b);C=ip(c,b);B=sub(mul(a,cj(d)),mul(Z(e),C))
        require(D>0,"Anchor premise")
        s=vs(c,vmul(cj(r),b));q=sub(mul(r,d),a)
        residual=ns(q)-e*norm2(s)
        radnum=ns(B)-D*(ns(a)-e*norm2(c))
        require(ns(sub(mul(Z(D),r),B))-radnum==D*residual,"Completed square")
        bads=vs(c,vmul(r,b))
        if ns(q)-e*norm2(bads)!=residual: counts['conjugation_mutations_detected']+=1
        badB=add(mul(a,cj(d)),mul(Z(e),C))
        if ns(sub(mul(Z(D),r),badB))-(ns(badB)-D*(ns(a)-e*norm2(c)))!=D*residual:
            counts['covariance_sign_mutations_detected']+=1
        if residual<=0:
            if norm2(s): w=vmul(div(q,Z(norm2(s))),s)
            else:
                require(q==Z(),"Degenerate numerator")
                w=tuple(Z() for _ in b)
            require(norm2(w)<=e,"Attaining witness norm")
            denominator=add(d,ip(b,w))
            require(denominator!=Z(),"Derived anchor")
            require(div(add(a,ip(c,w)),denominator)==r,"Attaining witness ratio")
            counts['attaining_witnesses']+=1
        else: counts['rejected_queries']+=1
        return residual
    for j in range(1200):
        n=1+j%6;b,c=vec(n),vec(n)
        d=Z(2,F(rng.randint(-3,3),5));a=Z(F(rng.randint(-8,8),3),F(rng.randint(-8,8),5))
        e=F(1,9)/(1+norm2(b));v=vec(n);w=vmul(Z(e/(1+norm2(v))),v)
        require(norm2(w)<=e,"Generated ball member")
        r=div(add(a,ip(c,w)),add(d,ip(b,w)))
        require(check(b,c,d,a,e,r)<=0,"Necessary condition")
        # An independent query exercises both directions, rather than only model outputs.
        check(b,c,d,a,e,Z(F(rng.randint(-20,20),9),F(rng.randint(-20,20),13)))
        # Orthogonal projection Gram, with an exactly unit candidate and arbitrary readouts.
        k=(Z(F(3,5)),Z(0,F(4,5)))+tuple(Z() for _ in range(n))
        h0,h1=vec(n+2),vec(n+2)
        p0=vs(h0,vmul(ip(k,h0),k));p1=vs(h1,vmul(ip(k,h1),k))
        require(ip(k,p0)==Z() and ip(k,p1)==Z(),"Projected vectors")
        require(norm2(p0)==norm2(h0)-ns(ip(h0,k)),"Projected denominator energy")
        require(norm2(p1)==norm2(h1)-ns(ip(h1,k)),"Projected numerator energy")
        require(ip(p1,p0)==sub(ip(h1,h0),mul(ip(h1,k),cj(ip(h0,k)))),"Projected covariance")
        counts['gaussian_cases']+=1
    for j in range(1,121):
        t=F(j,31);phase=Z((1-t*t)/(1+t*t),2*t/(1+t*t))
        w=(mul(Z(F(1,10)),phase),)
        b,c=(Z(1,F(1,3)),),(Z(F(2,3),2),)
        d,a=Z(2,1),Z(3,-2);e=F(1,100)
        r=div(add(a,ip(c,w)),add(d,ip(b,w)))
        require(check(b,c,d,a,e,r)==0,"Exact disk boundary")
        counts['sharp_boundary_cases']+=1
    for b,c,d,a,e,r in [((Z(),),(Z(),),Z(1),Z(2,3),F(1),Z(2,3)),
                        ((Z(1),),(Z(2),),Z(1),Z(2),F(1,4),Z(2)),
                        ((Z(1,2),),(Z(-3,1),),Z(1),Z(-1,2),F(0),Z(-1,2))]:
        require(check(b,c,d,a,e,r)<=0,"Degenerate case")
        counts['degenerate_cases']+=1
    require(counts['conjugation_mutations_detected']>1000,"Conjugation mutation was not exercised")
    require(counts['covariance_sign_mutations_detected']>1000,"Covariance mutation was not exercised")
    # At a non-strict margin a denominator zero is possible; the strict guard is essential.
    require(add(Z(1),ip((Z(1),),(Z(-1),)))==Z(),"Boundary guard example")
    return counts


def run(source:Path,certificate:Path,checker:Path):
    spec=importlib.util.spec_from_file_location('readout_checker',checker)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    counts=exact_tests()
    replays=[]
    for digits in (50,90):
        result=module.certify(source,certificate,digits)
        require(result['main_error_upper']=='3/4000',"Replay budget")
        replays.append(digits)
    rejected=[]
    with tempfile.TemporaryDirectory() as folder:
        folder=Path(folder)
        badsource=folder/'source.py'
        badsource.write_bytes(source.read_bytes().replace(b'1884327',b'1884328',1))
        badcert=folder/'certificate.json'
        data=json.loads(certificate.read_bytes());data['projective_distance_sq_upper']='0'
        badcert.write_text(json.dumps(data,indent=2)+'\n')
        for name,src,cert,digits in [('changed-candidate',badsource,certificate,70),
                ('changed-energy-premise',source,badcert,70),('insufficient-precision',source,certificate,10)]:
            try: module.certify(src,cert,digits)
            except ArithmeticError: rejected.append(name)
            else: raise AssertionError('Corruption accepted: '+name)
    return {'exact_checks':counts,'interval_replay_precisions':replays,'negative_tests_rejected':rejected,
            'kernel_checked':False,'upstream_spectral_verifier_replayed':False,
            'review':'single-author development checks; no independent model review'}


def main():
    root=Path(__file__).resolve().parent
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=root/'certify_prime3_refined.py')
    p.add_argument('--certificate',type=Path,default=root/'prime3_neumann_weighted_certificate.json')
    p.add_argument('--output',type=Path,default=root/'normalized_readout_validation.json')
    a=p.parse_args();r=run(a.source,a.certificate,root/'certify_prime3_normalized_readout.py')
    a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
