#!/usr/bin/env python3
"""Replay the residual barrier with an independently derived scalar-row enclosure.

The alternative uses a symmetric directional-derivative radius per output row.
It shares the interval primitives, residual evaluator, proposals and traversal.
It is a calculus/enclosure cross-check, not an independent root enumeration or
Lean-kernel proof. All new acceptance arithmetic is outward dyadic integer.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess

ROW_ENCLOSURE = r'''// Scalar-row mean-value enclosure. Each row has its own bound; no
// vector-valued common intermediate point is assumed.
bool sublevel_krawczyk(Box const& X, int mask, ll epsilon, Kr& out) {
  try {
    Box m;
    for(int j=0;j<5;j++)m[j]=I::point(mid(X[j]));
    I f[5],J[5][5],f0[5],J0[5][5],P[5][5];
    eval(m,mask,f0,J0);if(!propose(J0,P))return false;
    eval(X,mask,f,J);out.contraction=0;
    for(int i=0;i<5;i++) {
      I center=m[i];ll radius=0,row=0;
      for(int a=0;a<5;a++)center=center-P[i][a]*f0[a];
      for(int j=0;j<5;j++) {
        I e=I(i==j);
        for(int a=0;a<5;a++)e=e-P[i][a]*J[a][j];
        row=checked((wide)row+absmax(e));
        // Encloses the absolute directional derivative contribution.
        radius=checked((wide)radius+absmax(e*(X[j]-m[j])));
      }
      for(int a=0;a<5;a++)
        radius=checked((wide)radius+absmax(P[i][a]*I(-epsilon,epsilon)));
      out.k[i]=center+I(-radius,radius);
      out.contraction=max(out.contraction,row);
    }
    return true;
  }catch(overflow_error const&){return false;}
}
'''

def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def generate(source: Path, dest: Path) -> None:
    text=source.read_text(encoding='utf-8')
    start=text.index('bool sublevel_krawczyk(')
    end=text.index('\nint main(',start)
    require(text.count('bool sublevel_krawczyk(')==1,'ambiguous contractor')
    dest.write_text(text[:start]+ROW_ENCLOSURE+text[end:],encoding='utf-8')

def inflation_test() -> dict:
    # f(x)=x, m=0, C=1, derivative defect=0. x=eta is a valid
    # eta-sublevel point but is excluded by the ordinary root-only image.
    eta=Fraction(1,262144); x=eta
    root_only=(Fraction(0),Fraction(0)); inflated=(-eta,eta)
    require(not(root_only[0]<=x<=root_only[1]),'bad root-only test')
    require(inflated[0]<=x<=inflated[1],'missing sublevel inflation')
    return {'status':'PASS','example':'f(x)=x, C=1, m=0, x=eta',
            'eta':str(eta),'root_only_image_rejects_valid_sublevel_point':True,
            'inflated_image_contains_it':True}

def run(centers: Path, out: Path, jobs: int, cap: int, charts: list[int]) -> dict:
    require(jobs>0 and cap>0,'invalid execution budget')
    require(charts and len(charts)==len(set(charts)) and all(0<=x<32 for x in charts),
            'invalid charts')
    out.mkdir(parents=True,exist_ok=True)
    verdict=out/'verification.json';verdict.unlink(missing_ok=True)
    source=Path(__file__).with_name('check_real_x_residual_barrier.cpp')
    generated=out/'scalar_row_cover.cpp';generate(source,generated)
    for name,src in [('original',source),('scalar_rows',generated)]:
        subprocess.run(['g++','-std=c++17','-O3','-Wall','-Wextra','-Werror',
                        '-I',str(source.parent),str(src),'-o',str(out/name)],check=True)
    tasks=[(kind,k) for kind in ('original','scalar_rows') for k in charts]
    def one(task: tuple[str,int]) -> dict:
        kind,k=task;path=out/f'{kind}_{k:02d}.json';path.unlink(missing_ok=True)
        p=subprocess.run([str(out/kind),str(centers),str(k),str(cap),'18','12',str(path)],
                         capture_output=True,text=True)
        require(p.returncode==0,f'{kind} chart {k}: {p.stderr}{p.stdout}')
        v=json.loads(path.read_text())
        require(v['status']=='SUBLEVEL_COVERED' and v['chart']==k and
                v['pending']==v['unresolved']==0 and v['epsilon_bits']==18 and
                v['guard_radius_bits']==12,'unproved or wrong coverage')
        v['implementation']=kind
        print(f'{kind} chart {k:02}: {v["nodes"]}',flush=True)
        return v
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        reports=list(pool.map(one,tasks))
    totals={kind:sum(x['nodes'] for x in reports if x['implementation']==kind)
            for kind in ('original','scalar_rows')}
    # Failure semantics: a resource cut-off and malformed inputs never certify a chart.
    negatives=[]
    for name,args in [('budget',[str(out/'scalar_rows'),str(centers),'0','1','18','12',str(out/'budget.json')]),
                      ('bad_eta',[str(out/'scalar_rows'),str(centers),'0','1','0','12',str(out/'bad_eta.json')])]:
        p=subprocess.run(args,capture_output=True,text=True)
        require(p.returncode!=0,f'{name} corruption accepted')
        negatives.append({'test':name,'rejected':True,'exit_code':p.returncode})
    maxq=max(v['max_guard_contraction_dyadic'] for v in reports)
    report={'schema':'mub-scalar-row-sublevel-review-v1','status':'PASS',
        'base':'exact H0 over Q(i,sqrt(21))','eta':'1/262144','guard_halfwidth':'1/4096',
        'charts':charts,'complete_global_replay':charts==list(range(32)),
        'nodes':totals,'pending':0,'unresolved':0,
        'max_guard_contraction':str(Fraction(maxq,2**40)),
        'inflation_test':inflation_test(),'negative_tests':negatives,
        'shared_components':['outward dyadic arithmetic','residual and Jacobian expressions',
                             'preconditioner proposals','phase charts','branch traversal','root proposals'],
        'independent_component':'symmetric rowwise mean-value enclosure replacing interval centered form',
        'new_ambient_region_claimed':False,'lean_elaboration_executed':False,
        'lean_kernel_verified':False,'hashes':{'audit_driver':digest(Path(__file__)),
          'source':digest(source),'generated':digest(generated),'centers':digest(centers),
          'shared_core':digest(source.with_name('check_real_x_global_cover.cpp'))}}
    verdict.write_text(json.dumps(report,indent=2)+'\n')
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('centers',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--jobs',type=int,default=4);p.add_argument('--max-nodes',type=int,default=1500000)
    p.add_argument('--charts',type=int,nargs='*',default=list(range(32)))
    a=p.parse_args();print(json.dumps(run(a.centers,a.output,a.jobs,a.max_nodes,a.charts),indent=2))
