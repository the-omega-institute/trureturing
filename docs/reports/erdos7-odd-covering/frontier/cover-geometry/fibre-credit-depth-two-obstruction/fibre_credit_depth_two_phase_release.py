#!/usr/bin/env python3
"""Release every multi-outside-support shallow phase on one reference source."""
import argparse
import importlib.util
from fractions import Fraction as F
from pathlib import Path
from math import prod
import hashlib,json


def need(ok,msg):
 if not ok:raise RuntimeError(msg)


def load(name):
 path=Path(__file__).resolve().with_name(name+'.py')
 spec=importlib.util.spec_from_file_location(name,path)
 module=importlib.util.module_from_spec(spec)
 spec.loader.exec_module(module)
 return module


def calculate():
 height_api=load('fibre_credit_depth_two_joint_heights')
 fixture_api=load('fibre_credit_depth_two_joint_fixtures')
 source=Path(__file__).resolve().with_name('fibre_credit_depth_two_joint_heights.json')
 retained=json.loads(source.read_text())
 need(retained==json.loads(json.dumps(height_api.calculate())),
      'retained source height certificate agrees with exact reconstruction')
 fixtures=fixture_api.calculate()['cases']
 refs={(c['head_layout'],c['layout']):c for c in fixtures}
 cases=[]
 for h in retained['cases']:
  pairs=next(pairs for name,pairs,_ in fixture_api.HEAD_LAYOUTS if name==h['head'])
  S,A,K,K0,screens=height_api.prefix_certificate(fixture_api,h['layout'],pairs)
  need((str(S),str(A),str(K))==(h['S'],h['source_deep_tail'],h['all_height_query']),
       'shared shallow screens agree with retained source costs')
  c=dict(head=h['head'],layout=h['layout'],S=str(S),deep_tail=str(A),K=str(K),gate=h['gate'])
  free=[];cap=F(0)
  for j,hm,T,first_cap,lift in screens:
   if T.bit_count()<2:continue
   d=3**j*(5 if hm&1 else 1)*(7 if hm&2 else 1)*prod(q for i,q in enumerate((11,13,17,19)) if T>>i&1)
   free.append(d);cap+=first_cap
  need(len(set(free))==len(free)==132,'132 distinct shallow labels with >=2 outside axes')
  ref=refs[c['head'],c['layout']]
  fixed=[r for r in ref['actual_originals'] if r['m'] not in set(free)]
  need(len(fixed)==59,'59 fixed phase slots')
  pure={3,9,5,7,11,13,17,19}
  need(sum(r['m'] in pure for r in fixed)==8,'eight pure and51 mixed fixed slots')
  fixed_hash=hashlib.sha256(json.dumps(fixed,separators=(',',':')).encode()).hexdigest()
  gap=F(c['gate'])-F(566,49)*cap
  alpha=F(c['S'])-F(c['deep_tail'])-cap
  need(gap==F(566,49)*alpha-F(c['K']),'one source pays actual free phases then all deep labels')
  need(gap>0 and alpha>0,'strict robust all-height gate')
  density=49*gap/(616*F(323323,73728))
  cases.append(dict(head=c['head'],layout=c['layout'],fixed_phase_count=59,
   fixed_phase_sha256=fixed_hash,fixed_actual_phases=fixed,released_phase_count=132,
   released_numerical_labels=sorted(free),free_phase_debit=str(cap),
   free_phase_debit_decimal=float(cap),alpha_lower=str(alpha),
   robust_gate=str(gap),robust_gate_decimal=float(gap),
   haar_density_lower=str(density),haar_density_lower_decimal=float(density)))
 out=dict(scope='For each of four reference templates, only the 59 head and singleton-outside shallow phases are fixed. All other 132 shallow phases may be arbitrary or absent; all additional nonternary heights and all 23/29-bearing original phases are arbitrary. Distinct odd nonunit numerical moduli, whole-family v3<=2, support subset of 3,5,7,11,13,17,19,23,29.',
  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),cases=cases)
 return out


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 result=json.loads(json.dumps(calculate()))
 rendered=json.dumps(result,sort_keys=True,indent=2)+'\n'
 if args.output is None:
  retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
  need(retained==result,'retained phase release result agrees with exact replay')
  print(rendered,end='')
 else:
  args.output.write_text(rendered)


if __name__=='__main__':main()
