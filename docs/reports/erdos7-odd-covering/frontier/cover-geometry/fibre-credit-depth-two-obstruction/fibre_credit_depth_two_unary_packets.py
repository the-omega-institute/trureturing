#!/usr/bin/env python3
"""Actual phase families beyond all four literal/affine59 templates."""
import argparse
import importlib.util
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from math import gcd,prod,lcm
import hashlib,json


def need(ok,msg):
 if not ok:raise RuntimeError(msg)


def load(name):
 path=Path(__file__).resolve().with_name(name+'.py')
 spec=importlib.util.spec_from_file_location(name,path)
 module=importlib.util.module_from_spec(spec)
 spec.loader.exec_module(module)
 return module


fixture_api=load('fibre_credit_depth_two_joint_fixtures')
api=vars(fixture_api)
BIG=fixture_api.BIG; W=fixture_api.W; LEAVES=fixture_api.LEAVES


def partitions(mask):
 if not mask:return [()]
 bit=mask&-mask
 out=[]
 for tail in partitions(mask^bit):
  out.append((bit,)+tail)
  for i in range(len(tail)):
   out.append(tail[:i]+(tail[i]|bit,)+tail[i+1:])
 return out


def orbit_options(target,reference,fixed_labels):
 counts={}
 for p in (3,5,7,11,13,17,19):
  mod=9 if p==3 else p; choices=[]
  for u in range(mod):
   if gcd(u,mod)!=1:continue
   v=(reference[9]-u*target[9])%9 if p==3 else (reference[p]-u*target[p])%p
   ok=True
   for m in fixed_labels:
    if m%p:continue
    pe=9 if p==3 and m%9==0 else p
    if (u*target[m]+v-reference[m])%pe:ok=False;break
   if ok:choices.append((u,v))
  counts[str(p)]=len(choices)
 return counts


def calculate():
 phase_api=load('fibre_credit_depth_two_phase_release')
 height_api=load('fibre_credit_depth_two_joint_heights')
 source=Path(__file__).resolve().with_name('fibre_credit_depth_two_phase_release.json')
 phase_result=phase_api.calculate()
 need(json.loads(source.read_text())==json.loads(json.dumps(phase_result)),
      'retained phase certificate agrees with reconstructed reference source')
 fixtures=fixture_api.calculate()['cases']
 refs={(c['head_layout'],c['layout']):c for c in fixtures}
 prefixes={(c['head'],c['layout']):dict(deep_tail=c['source_deep_tail'],K=c['all_height_query'])
           for c in height_api.calculate()['cases']}
 released={(c['head'],c['layout']):c for c in phase_result['cases']}
 parts=partitions(15)
 need(len(parts)==len({tuple(sorted(p)) for p in parts})==15,'all15 set partitions of four outside coordinates')
 k={D:prod((F(1,q-1) for i,q in enumerate(BIG) if D>>i&1),start=F(1)) for D in api['SUPPORTS']}
 H=tuple(api['response']((F(1),)*4,k,15^T) for T in range(16));Z=H[0]
 delta=(F(1,10),F(1,12),F(0),F(0))
 packet_costs=[]
 for part in parts:
  debit=F(0)
  for J in part:
   union=1-prod((1-delta[i] for i in range(4) if J>>i&1),start=F(1))
   debit+=H[J]*union
  packet_costs.append(debit)
 packet=min([Z]+packet_costs)
 single=sum((H[1<<i]*delta[i] for i in range(4)),F(0))
 need(packet<single,'strict improvement by actual cross-coordinate overlap')
 good=bad=0
 for x in product(*(range(1,q) for q in BIG)):
  if sum(v==1 for v in x)>=2:continue
  good+=1
  bad+=x[0]==2 or x[1]==2
 exact=Z*F(bad,good)
 need(exact<=packet<single,'one uniformly thinned actual source bounds the same actual union')
 cases=[];menu_rows=[]
 for head in ('opposite_root','same_root'):
  ref=refs[head,'aligned'];spread=refs[head,'spread']
  refdict={r['m']:r['a'] for r in ref['actual_originals']}
  spreaddict={r['m']:r['a'] for r in spread['actual_originals']}
  headlabels=sorted(m for m in refdict if 315%m==0)
  live=[x for x in range(315) if all(x%m!=refdict[m] for m in headlabels)]
  need(len(live)==ref['head_seven_label_legal_cells'],'actual complete head support')
  cofactors=sorted(c for h,a,b,c in api['COFACTORS'] if c>1)
  null={c:sorted(set(range(c))-{x%c for x in live}) for c in cofactors}
  for c in cofactors:
   sizes={str(q):c+(q-1)*len(null[c]) for q in BIG}
   for q in BIG:
    count=sum(a%q==0 or a%c in null[c] for a in range(c*q))
    need(count==sizes[str(q)],'complete safe-phase menu per full numerical label')
   menu_rows.append(dict(head=head,c=c,null_residue_count=len(null[c]),null_residues=null[c],phase_menu_sizes=sizes))
  b=min(live);l=LEAVES.index(b%9);headmass=W[l]/24
  fixed={r['m'] for r in released[head,'aligned']['fixed_actual_phases']}
  free=set(released[head,'aligned']['released_numerical_labels'])
  for kind in ('zero_debit','positive_packet'):
   target=refdict.copy()
   for m in free:target[m]=spreaddict[m]
   for c in cofactors:
    for q in BIG:
     a,m=api['crt']({c:max(null[c]),q:q-1})
     target[m]=a
   if kind=='positive_packet':
    for q in (11,13):
     a,m=api['crt']({315:b,q:2});target[m]=a
   changed_singletons=sum(target[c*q]!=refdict[c*q] for c in cofactors for q in BIG)
   need(changed_singletons==44,'all44 singleton-outside literal phases changed')
   # Check the actual unary unions at every retained head row.
   for x in live:
    active={q:set() for q in BIG}
    for q in BIG:
     for c in (1,*cofactors):
      a=target[c*q]
      if x%c==a%c and a%q!=0:active[q].add(a%q)
    expected={q:({2} if kind=='positive_packet' and x==b and q in (11,13) else set()) for q in BIG}
    need(active==expected,'full actual same-family unary-root union on every head row')
   extra={25:7,49:9,121:13,169:19,289:23,361:29,23:5,29:7,23*29:31,
          9*25*7*11*23*29:1234567}
   need(not set(target)&set(extra),'added complete numerical labels distinct')
   target.update({m:a%m for m,a in extra.items()})
   actual={m:((a-1)*pow(2,-1,m))%m for m,a in target.items()}
   need(len(actual)==201 and all((2*actual[m]+1)%m==target[m] for m in actual),'one affine normalization of the entire201-original family')
   for m,a in actual.items():
    need(m>1 and m%2 and 0<=a<m,'distinct odd nonunit original with canonical phase')
    remaining=m;v3=0
    for p in (3,5,7,11,13,17,19,23,29):
     while remaining%p==0:
      remaining//=p
      if p==3:v3+=1
    need(remaining==1 and v3<=2,'complete original support and ternary-height scope')
   failures=[]
   for rr in fixtures:
    rd={r['m']:r['a'] for r in rr['actual_originals']}
    counts=orbit_options(actual,rd,fixed)
    need(not all(counts.values()),'target lies outside every prior literal/affine59 template orbit')
    failures.append(dict(reference_head=rr['head_layout'],reference_layout=rr['layout'],local_option_counts=counts))
   baseline=prefixes[head,'aligned'];release=released[head,'aligned']
   debit=headmass*packet if kind=='positive_packet' else F(0)
   single_debit=headmass*single if kind=='positive_packet' else F(0)
   exact_debit=headmass*exact if kind=='positive_packet' else F(0)
   gate=F(release['robust_gate'])-F(566,49)*debit
   density=49*gate/(616*F(323323,73728))
   need(gate>0,'strict repair gate for actual201-original family and arbitrary further heights')
   payload=[dict(a=a,m=m) for m,a in sorted(actual.items())]
   norm=[dict(a=a,m=m) for m,a in sorted(target.items())]
   digest=hashlib.sha256(json.dumps(payload,separators=(',',':')).encode()).hexdigest()
   cases.append(dict(head=head,kind=kind,source_reference='aligned',actual_original_count=201,
    all44_singleton_phases_changed=True,changed_shallow_phases=sum(target[m]!=refdict[m] for m in refdict),
    actual_phase_sha256=digest,actual_originals=payload,normalized_originals=norm,
    single_global_normalization=dict(u=2,v=1,period=str(lcm(*actual))),
    selected_legal_head_residue=b,selected_legal_head_row=[l,b%5,b%7],head_row_base_mass=str(headmass),
    packet_changed_labels=[315*11,315*13] if kind=='positive_packet' else [],
    actual_unary_debit=str(exact_debit),packet_unary_debit=str(debit),singleton_unary_debit=str(single_debit),
    packet_saving=str(single_debit-debit),packet_saving_decimal=float(single_debit-debit),
    uniform_multi_support_debit=release['free_phase_debit'],complete_deep_debit=baseline['deep_tail'],
    complete_query_upper=baseline['K'],gate=str(gate),gate_decimal=float(gate),
    haar_density_lower=str(density),haar_density_lower_decimal=float(density),
    excluded_template_affine_orbits=failures))
 out=dict(scope='Four actual201-original families outside all four prior affine59-slot template orbits. The zero-debit examples use large null-phase menus; the positive examples create two actual co-located unary events and a strictly sharper common-source packet debit. All201 phases arise from one affine inverse, all higher-height continuation claims retain v3<=2 and the fixed nine-prime support.',
  set_partitions=15,common_row_Z=str(Z),conditional_reference_survivor_cells=good,
  conditional_actual_union_cells=bad,conditional_actual_union_mass=str(exact),
  conditional_packet_upper=str(packet),conditional_singleton_upper=str(single),
  minimizing_packet_partitions=[list(p) for p,d in zip(parts,packet_costs) if d==packet],
  reference_certificate_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
  null_menus=menu_rows,cases=cases)
 return out


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 result=json.loads(json.dumps(calculate()))
 rendered=json.dumps(result,sort_keys=True,indent=2)+'\n'
 if args.output is None:
  retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
  need(retained==result,'retained actual phase packet result agrees with exact replay')
  print(rendered,end='')
 else:
  args.output.write_text(rendered)


if __name__=='__main__':main()
