"""Exact rank-two real regression and independent interval replay.

Finite regression is not a Lean proof. Spectral premises are not replayed.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import random
import tempfile


def require(h,msg):
    if not h: raise ArithmeticError(msg)


def dot(x,y): return sum((a*b for a,b in zip(x,y)),F(0))
def norm2(x): return dot(x,x)
def scale(a,x): return tuple(a*v for v in x)
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))


def solve(b,c,x,y):
    U,V,C=norm2(b),norm2(c),dot(b,c);det=U*V-C*C
    require(det>0,'Rank two required')
    w=add(scale((V*x-C*y)/det,b),scale((U*y-C*x)/det,c))
    cost=(V*x*x-2*C*x*y+U*y*y)/det
    return w,cost,det


def exact_tests():
    rng=random.Random(2026090607)
    counts={'full_rank_cases':0,'energy_decompositions':0,'scaled_equations':0,
            'orthogonal_witnesses':0,'rank_deficient_rejections':0,
            'symmetry_normalizations':0,'structured_complex_separations':0}
    for n in range(800):
        d=3+n%5
        # First coordinate zero realizes the same candidate-orthogonal space.
        b=(F(0),)+tuple(F(rng.randint(-9,9),7) for _ in range(d-1))
        c=(F(0),)+tuple(F(rng.randint(-9,9),11) for _ in range(d-1))
        if norm2(b)*norm2(c)-dot(b,c)**2<=0:continue
        x,y=F(rng.randint(-5,5),13),F(rng.randint(-5,5),17)
        w,cost,det=solve(b,c,x,y)
        require(dot(b,w)==x and dot(c,w)==y,'Witness constraints')
        require(norm2(w)==cost and cost>=0,'Exact minimum energy')
        require(w[0]==0,'Forbidden candidate direction')
        counts['orthogonal_witnesses']+=1
        v=tuple(F(rng.randint(-5,5),19) for _ in range(d))
        projection,_,_=solve(b,c,dot(b,v),dot(c,v))
        residual=sub(v,projection)
        feasible=add(w,residual)
        require(dot(b,residual)==0 and dot(c,residual)==0,'Nullspace residual')
        require(norm2(feasible)==cost+norm2(residual),'Pythagorean decomposition')
        counts['energy_decompositions']+=1
        for s in (F(2),F(-3,5),F(1,10000)):
            w2,cost2,_=solve(b,scale(s,c),x,s*y)
            require(w2==w and cost2==cost,'Rescaled imaginary equation')
            counts['scaled_equations']+=1
        for ss,tt in ((F(1),F(0)),(F(0),F(1)),(F(2),F(-3))):
            require((ss*x+tt*y)**2<=norm2(add(scale(ss,b),scale(tt,c)))*cost,'Dual inequality')
        counts['full_rank_cases']+=1
    for b,c in [((F(0),F(0)),(F(1),F(0))),((F(1),F(2)),(F(2),F(4)))]:
        try:solve(b,c,F(0),F(1))
        except ArithmeticError:counts['rank_deficient_rejections']+=1
        else:raise ArithmeticError('Singular inverse was accepted')
    # At an off-axis query, allowing complex error changes the feasible set.
    for j in range(1,51):
        eps=F(1,j+1);target=F(1,100)
        real_cost=target**2/eps**2;complex_cost=target**2/(1+eps**2)
        budget=(real_cost+complex_cost)/2
        require(complex_cost<budget<real_cost,'Structured cancellation gap')
        counts['structured_complex_separations']+=1
    # Exact complex scaling of a real eigenvector cancels in projective alignment.
    for n in range(1,101):
        zr,zi=F(n,7),F((-1)**n,11)
        # k=(4/5,3/5,0), u=(z,0,0), alpha=(4/5)z.
        ar,ai=F(4,5)*zr,F(4,5)*zi;den=ar*ar+ai*ai
        pr=(zr*ar+zi*ai)/den;pi=(zi*ar-zr*ai)/den
        require(pr==F(5,4) and pi==0,'Reality after overlap normalization')
        # The third, odd coordinate stays zero. For A=diag(0,4,5), T=64/25.
        k=(F(4,5),F(3,5),F(0));p=(pr,F(0),F(0));w=sub(p,k)
        require(dot(k,w)==0 and norm2(w)==F(9,16),'Projective norm identity')
        require(F(64,25)*norm2(w)==F(36,25),'Coercivity equality')
        counts['symmetry_normalizations']+=1
    return counts


def run(source,energy,checker):
    spec=importlib.util.spec_from_file_location('real_transverse_checker',checker)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    counts=exact_tests();replays=[]
    for digits in (50,90):
        result=mod.certify(source,energy,digits)
        require(result['uniform_certificate']['grid_boxes']==64,'Box replay')
        require(result['uniform_certificate']['rational_transverse_margin']=='257/50000','Margin replay')
        # The even series enclosure also has its correct value at zero.
        require(mod.sinhc_enclosure(mod.Q(0)).a<=1<=mod.sinhc_enclosure(mod.Q(0)).b,'sinhc seam')
        for t in (F(1,1000),F(1,4),F(-1,4)):
            u=mod.Q(t);s=mod.sinhc_enclosure(u);exact=mod.sinh(u)/u
            require(not bool(s.a>exact.b) and not bool(exact.a>s.b),'sinhc independent exponential overlap')
        replays.append(digits)
    rejected=[]
    with tempfile.TemporaryDirectory() as tmp:
        tmp=Path(tmp)
        changed=tmp/'candidate.py';changed.write_text(source.read_text().replace('1884327','1884328',1))
        bad=tmp/'energy.json';data=json.loads(energy.read_text());data['projective_distance_sq_upper']='0';bad.write_text(json.dumps(data))
        for name,src,en,digits in [('candidate-mutation',changed,energy,70),('energy-mutation',source,bad,70),('precision',source,energy,10)]:
            try:mod.certify(src,en,digits)
            except ArithmeticError:rejected.append(name)
            else:raise ArithmeticError('Bad input accepted '+name)
    return {'exact_checks':counts,'directed_interval_replays':replays,'bad_inputs_rejected':rejected,
      'upstream_spectral_verifier_executed':False,'lean_kernel_executed':False,
      'input_scope':'The mathematical candidate literal and four energy fields; not full upstream-file attestation',
      'review_scope':'Single-author exact and interval development checks, no independent proof reviewer'}


def main():
    root=Path(__file__).resolve().parent
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=root/'certify_prime3_refined.py')
    p.add_argument('--energy',type=Path,default=root/'prime3_neumann_weighted_certificate.json')
    p.add_argument('--output',type=Path,default=root/'real_transverse_validation.json')
    a=p.parse_args();r=run(a.source,a.energy,root/'certify_prime3_real_transverse.py')
    a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
