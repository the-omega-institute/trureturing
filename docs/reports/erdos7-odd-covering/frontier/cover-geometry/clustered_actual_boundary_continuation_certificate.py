#!/usr/bin/env python3
"""Exact reuse of657's unchanged rows, Euler products and full tails.

The actual-source and complete-inventory bridge is an ordinary theorem in680;
this program checks its numerical premise and both unchanged-policy budgets.
It does not construct a new policy or supply an unrestricted covering theorem.
"""
from pathlib import Path
from fractions import Fraction as F
from math import prod
from hashlib import sha256
import argparse,json
P=argparse.ArgumentParser(description=__doc__)
P.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
P.add_argument('--output',type=Path)
args=P.parse_args();checks={};data={}
def ck(name,value):
 if not value:raise ArithmeticError(name)
 checks[name]=checks.get(name,0)+1
pins={'clustered_actual_boundary_gate_certificate.json':'19084aa5788acdd40b3c74a49f3c8b8f0af22f808fc5b9ee1a4988aae2b248bc','ordinary_domain_five_parent_certificate.json':'e46183469f280d262da37a9c33005e724690fc20b0106202c42c9913ed8d8ec0','clustered_actual_boundary_gate_witness.json':'887cd5d78038e2375ebd63d6d43c4c1e954f848f76d4fc145bc0f44b210c32a1','clustered_exact_actual_source.json':'31d7d2b20a4a72805222c7c7782506d3b9babd37c36f7cfb0d287260ba4b1905'}
for name,pin in pins.items():
 raw=(args.directory/name).read_bytes();ck('input_pin',sha256(raw).hexdigest()==pin);data[name]=json.loads(raw)
G=data['clustered_actual_boundary_gate_certificate.json'];R=data['ordinary_domain_five_parent_certificate.json']
ck('both_status_PASS',G['status']==R['status']=='PASS')
Q=(7,11,13,17,19);D=[F(5,6)]+[F(q-2,q-1)-F(2,q*(q-2))for q in Q[1:]]
Dall=prod(D,start=F(1));alpha=F(2673,110656)
ck('same_thinning',list(map(F,G['uniform_factor_thinning']))==D and F(G['thinned_gate'])==Dall*F(G['actual_field_gate']))
# The inherited mode9 additions pay only GUARDED 9q² portions. Replace them
# by the four full mode8 leaf/whole charges before claiming complete inventory.
W=data['clustered_actual_boundary_gate_witness.json'];S=data['clustered_exact_actual_source.json']
coords=list(map(tuple,W['coordinates']));theta={c:F(v,W['field_denominator'])for c,v in zip(coords,W['field_numerators'])};i,j=W['corner']
H={tuple(row['cell']):row['H_by_support_and_root7']for row in S['cells']};extra=[];g=F(200163067,201247200)
for u,q in enumerate(Q):
 if not u:continue
 values={c:F((1 if c[0]==i else 2)*(3 if c[1]==j else 4),675)*theta[c]*F(H[c][1<<u][0])for c in coords}
 full=max(sum((v for c,v in values.items()if c[0]==l),F())for l in {c[0]for c in coords})
 guarded=max(sum((v for c,v in values.items()if c[0]==l and c[1]//5==col),F())for l in {c[0]for c in coords}for col in range(4))
 ck('full_screen_dominates_guard',full>=guarded)
 debit=g*F(1,q*(q-2))*(full-guarded)
 extra.append(dict(q=q,full_screen=str(full),guarded_screen=str(guarded),extra_debit=str(debit)))
extra_fee=sum((F(row['extra_debit'])for row in extra),F());fullgate=F(G['actual_field_gate'])-extra_fee;gamma=Dall*fullgate
ck('full_gate_exact',fullgate==F(2144832980209210799160393676877,119188834050548855719526400000000))
ck('full_scaled_gate_exact',gamma==F(921143501847540509401483050662119383445633,88672944375462709711523174183180697600000000))
ck('larger_than_inherited_head',gamma>F(R['head_gate']))
ck('same_projection',alpha==F(R['projection_alpha']))
for q,d in zip(Q,D):
 ck('factor_domination',0<d<1)
 ck('root_balanced_full_Haar_cap',F(q,q-1)<=F(q-1,q-2))
 ck('all_deep_prefix_ratio',F(q-2,q-1)<1)
 # At root1 in this finite fixture the first-root normalized query cap dominates a surviving deep child.
 ck('root1_deep_comparison',F(q-1,q)>F(q-2,q-1))
actualHaar=F(2)*F(4,3)*Dall*prod((F(q,q-1)for q in Q),start=F(1))*F(5,3)*F(20,11)*F(2)
ck('head_Haar_domination',actualHaar<=1/alpha)
basefee=F(R['finite_fee_upper'])+F(R['complete_five_parent_tail'])+F(R['ordinary_typeI_fee'])
ck('all_fees_retained',basefee==F(R['fee_before_arbitrary']))
ck('same_193_rows',len(R['finite_rows'])==193)
ck('same_Euler_counts',R['Euler_counts']=={'head':10,'finite':193,'half':123})
ck('same_owner_switch',R['first_five_parent_owner']==67)
policies={}
for key,K in [('RS_policy',46),('elementary_policy',68)]:
 row=R[key];fee=F(row['fee']);raw=gamma-basefee-fee;projected=alpha*raw
 ck('same_tail_switch',row['K']==K and int(row['arbitrary_threshold'])==2**K)
 ck('positive_complete_budget',raw>0)
 ck('density_50000',projected>F(1,50000))
 policies[key]=dict(K=K,arbitrary_threshold=str(2**K),complete_fee=str(basefee+fee),raw_margin=str(raw),projected_margin=str(projected),projected_margin_decimal=float(projected),density_denominator=50000)
out=dict(schema='clustered-actual-boundary-657-continuation-v1',status='PASS',new_lean_verification=False,scope='Conditional transport of657 unchanged policies after replacing four guarded9q² mode9 debits by full mode8 debits. Fixed101 core, no further live pure originals at3,5,7,11,13,17,19; all remaining mixed inventory permitted under actual23/29/31 head and declared ordinary/private interfaces.',source_sha256=pins,program_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),original_guarded_gate=G['actual_field_gate'],full_nine_square_extra_fee=str(extra_fee),full_nine_square_charges=extra,full_inventory_gate=str(fullgate),head_gate=str(gamma),projection_alpha=str(alpha),actual_head_Haar_cap=str(actualHaar),uniform_thinning_product=str(Dall),finite_owner_count=193,Euler_counts=R['Euler_counts'],first_five_parent_owner=67,policies=policies,checks=checks,check_count=sum(checks.values()))
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
