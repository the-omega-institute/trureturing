#!/usr/bin/env python3
"""Exact event-query and weighted-reserve constants on the existing PA supplier.

The ordinary proof supplies all-family and all-query quantifiers. These checks
verify source pins, exact constants, complete geometric tails, and the stated
conditional numerical conclusions; no Lean or unrestricted covering claim.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path
import json

PINS={
 'height_three_clipping_envelope.json':'276d7e266a86ed8e5a1c9da2982b219725c2738bc4ad19da1243bf8575543685',
 'four_level_query_hinge_lift.json':'b224c79716585f16b52aeda277810a1a001a4f2d92d3e092cfc1cc41345dbcfd',
}
Q=(5,7,11,13,17,19)
def ex(v):
 v=F(v)
 return {'exact':str(v),'decimal':float(v)}

def main():
 ap=ArgumentParser(description=__doc__)
 ap.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
 ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
 args=ap.parse_args();checks=[];sources={};provenance=[]
 def need(name,cond):
  if not cond:raise ValueError('FAILED: '+name)
  checks.append(name)
 for name,digest in PINS.items():
  raw=(args.source_dir/name).read_bytes()
  need('source SHA256 '+name,sha256(raw).hexdigest()==digest)
  sources[name]=json.loads(raw);provenance.append({'path':name,'sha256':digest})
 env=sources['height_three_clipping_envelope.json']
 fh=sources['four_level_query_hinge_lift.json']
 B=F(env['B']);K3=max(F(c['K_integer'][3]) for c in env['corners'])
 alpha=min(F(c['alpha']['exact']) for c in fh['corners']);target=F(566,49)
 need('same actual source B',B==F(fh['B']['exact'])==F(432040125182653876501,86355045355449035400))
 need('same all-layout third hinge',K3==F(fh['K']['exact'])==F(12019840537595758779003,5715264751774801992890))
 need('same actual source density constant',alpha==F(7575003978548161,73724315753088000))
 need('same continuation target',F(env['target'])==target)
 a=F(81,74)*(1+B);r=B+a;p=K3/3;pc=a/r
 RH=prod(F(q,q-1) for q in Q)-1
 needed=K3/pc-3;rootdelta=RH-sum(F(1,q) for q in Q)
 need('critical auxiliary event probabilities',0<pc<p<1)
 need('unused reciprocal strictness is insufficient by itself',needed>rootdelta>0)
 rows=[]
 for H in (1,2,3,6,12):
  box=prod(sum(F(1,q**e) for e in range(H+1)) for q in Q)-1
  delta=RH-box;bound=K3/(3+delta)
  need('positive complete query-box tail '+str(H),0<delta<RH)
  need('strict finite completion bound '+str(H),bound<p)
  rows.append({'height':H,'delta':ex(delta),'six_tail_upper':ex(bound)})
 # The geometric identities retain all query and original heights. The finite
 # sums are completed by exact tails, not used as a numerical cutoff.
 for H in (2,3,6,12):
  need('complete weighted-law deep query tail '+str(H),sum((F(9,4*3**e) for e in range(2,H+1)),F(0))+F(9,8*3**H)==F(3,8))
  need('complete general original load tail '+str(H),sum((F(54,3**e) for e in range(4,H+4)),F(0))+F(1,3**H)==1)
 need('same deep coefficients for the two actual roots',F(1,2)*F(9,2)==F(3,4)*3==F(9,4))
 need('root and deep budget base',F(1,2)+F(3,8)==F(7,8))
 density=F(81,4)/alpha
 need('actual density uses disjoint roots',density==F(9,4)*9/alpha)
 need('complete 23/29 density and mass conversion',density*F(616,567)*567==F(12474)/alpha)
 base=B+F(7,8)*(1+B);h=F(2,9)
 need('five-ninths reserve gives exact weight cap',(1-F(5,9))/2==h)
 R9=base+h*(K3+4*p)
 need('U9 exact query value',R9==F(18675891604964416972141967,1645996248511142973952320))
 need('U9 passes full continuation gate',R9<target)
 need('original two-height weights',F(54,3**4)+F(54,3**5)==F(8,9))
 need('two-height counts imply five-ninths reserve',1-6*F(8,9)/12==F(5,9))
 need('same-source two-height mean weight',F(8,9)*B/24==B/27)
 R10=base+h*K3+F(4,27)*B
 need('U10 exact query value',R10==F(849159137346241243429752067,74069831183001433827854400))
 need('U10 passes full continuation gate',R10<target)
 mc=(target-base-h*K3)/4
 need('actual mean-loss threshold exact',mc==F(22258049305083630332220427,107538421569394674298218240))
 need('bare all-height union mean misses threshold',B/27<mc<B/24)
 need('581 raw-capacity barrier remains above target',r>target>R10>R9)
 def row(R):
  H=alpha*(566-49*R)/12474
  need('positive same-law Haar continuation '+str(R),H>0)
  need('same density continuation identity '+str(R),H==((566-49*R)/567)/(density*F(616,567)))
  return {'query_upper':ex(R),'query_margin':ex(target-R),'Haar_survivor_lower':ex(H)}
 weighted={
  'required_contract':'ONE actual selected PA nu; all finite alternative one-phase query layouts obey the common third-hinge bound.',
  'required_geometry':'Exactly pure3 originals 1 mod3 and3 mod9; fixed actual residues and distinct numerical moduli; selected <=2 Q phases per cofactor covers every original through exponent3; actual cB=1 and cA>=1/2.',
  'general_U7':'0<=f<=h => R_Q(f nu)<=h K_t+t integral(f dnu), when the same-source ALL-layout K_t contract holds.',
  'general_U8':'aA=cA/2,aB=1-cA/2,f=(1-cA)/2; R_P<=B+7/8(1+B)+hK_t+(t+1)Ef, f<=h.',
  'source_density_upper':ex(density),'base_query_budget':ex(base),'h_at_cA_five_ninths':ex(h),
  'U9':row(R9),'U9_additional_conditions':'cA>=5/9 and cA=1 outside one actual E with nu(E)<=K3/3.',
  'U10':row(R10),'U10_additional_conditions':'Only nonzero residual A original layers are4 and5, and each actual layer count is at most6. Query heights are unrestricted.',
  'all_height_actual_mean_threshold':ex(mc),'bare_all_height_mean_upper':ex(B/24),'missing_mean_credit':ex(B/24-mc),
  '581_raw_uniform_cap_barrier':ex(r),'compatibility_boundary':'The weighted estimate keeps f nu query incidence omitted by the raw uniform M,lambda numerator; it does not refute581 or all older actual certificates.'}
 out={'schema':'weighted-query-reserve-v1','scope':'Ordinary conditional query theorem, exact source constants and consumers; no Lean or unrestricted Erdos7 claim.',
      'sources':provenance,'B':ex(B),'K3':ex(K3),'alpha':ex(alpha),'target':ex(target),
      'event_budget':{'p':ex(p),'pcrit':ex(pc),'required_delta':ex(needed),'prime_root_inventory_delta':ex(rootdelta),'prime_root_inventory_six_tail_upper':ex(K3/(3+rootdelta)),'complete_box_examples':rows},
      'weighted_query_consumers':weighted,'check_count':len(checks),'checks':checks}
 args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'checks':len(checks),'U9':float(R9),'U10':float(R10),'gate':float(target),'output':str(args.output)}))
if __name__=='__main__':main()
