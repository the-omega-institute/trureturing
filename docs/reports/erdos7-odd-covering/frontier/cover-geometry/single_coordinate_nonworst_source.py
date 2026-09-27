#!/usr/bin/env python3
"""Exact finite arithmetic for the seven nonworst source charts in report483.
Ordinary source construction, monotone tail domination and original inventory
argument are supplied in the accompanying proof. No Lean certification.
"""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
from collections import defaultdict
from math import factorial,prod
import argparse,json
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
INPUTS={'query_stoploss_completion.json':'44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d','common_law_mass_tail.json':'3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4'}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [encode(v) for v in x]
 return x

def laws(split):
 # For pure coordinates only the surviving mass and the union-tail bound
 # are used. For later coordinates the conditional cap multiplies that tail.
 out=[]
 for p in (3,5,7,11,13,17,19):
  n=2 if p==split else 1
  mass=F(1,2) if p==3 else F(3,4) if p==5 else F(1)
  c=F(1) if p in (3,5) else dict(CAPS)[p]
  tail={0:mass,**{j:min(mass,c*n/F(p**j)) for j in range(1,20)}}
  w={i:tail[i-1]-tail[i] for i in range(1,20)};w[20]=tail[19]
  need(all(v>=0 for v in w.values()) and sum(w.values())==mass,'positive comparison law mass')
  for j in range(1,20):
   need(sum(w[i] for i in range(j+1,21))==tail[j],'exact tail envelope')
  out.append((p,w,mass))
 return out

def convolution(distributions):
 dist={1:F(1)};history=[]
 for p,w,mass in distributions:
  out=defaultdict(F)
  for a,u in dist.items():
   for b,v in w.items():out[min(20,a*b)]+=u*v
  need(sum(out.values())==sum(dist.values())*mass,'convolution preserves full mass')
  dist=dict(out);history.append({'prime':p,'total_mass':sum(dist.values()),'bad_mass':dist.get(20,F())})
 need(sum(dist.values())==F(3,8),'full pure survivor product mass')
 return dist[20],history

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input-dir',type=Path,default=Path(__file__).parent);ap.add_argument('--output',type=Path);args=ap.parse_args()
 data={}
 for name,digest in INPUTS.items():
  raw=(args.input_dir/name).read_bytes();need(sha256(raw).hexdigest()==digest,'source identity '+name);data[name]=json.loads(raw)
 common=data['common_law_mass_tail.json']['common_seven_core_law']
 need([F(x) for x in common['conditional_caps']]==[c for p,c in CAPS],'conditional caps')
 density=F(common['unnormalized_joint_density_cap']);need(density==F(27,2),'joint density cap')
 groups=defaultdict(list)
 for row in data['query_stoploss_completion.json']['rows']:
  groups[tuple(row['node'][:3])].append(F(row['cores']['7']['live_mass_lower_cell_units'])/135)
 need(len(groups)==8 and all(len(v)==4 for v in groups.values()),'32 vertices in eight coarse groups')
 coarse={key:min(vals) for key,vals in groups.items()}
 need(coarse[2,4,1]==F(7235955529,450000000000),'worst source mass')
 other={key:v for key,v in coarse.items() if key!=(2,4,1)}
 m=min(other.values());need(m==F(5891133457,225000000000),'nonworst source lower mass')
 calculations={}
 for q in (3,5,7,11,13,17,19):
  distributions=laws(q);bound,history=convolution(distributions)
  calculations[q]={'laws':distributions,'convolution':history,'BAD_upper':bound,'BAD_upper_float':float(bound)}
 B=max(v['BAD_upper'] for v in calculations.values())
 need(B==calculations[3]['BAD_upper'],'ternary split is the largest of seven bounds')
 need(B==F(3327584991507538462402462818879857311152571720958903957279651,165576938898208242787587584507966922934711827488892566071875000),'exact retained upper')
 # Keep the existing completed source. On the upper-comparison side retain
 # only these finitely many disjoint pure exclusions and release deeper ones.
 # The error pays for that release; no new finite-source theorem is inferred.
 h3,h5=12,8
 eps3,eps5=F(1,2*3**h3),F(1,4*5**h5)
 finite_upper=B+eps3+eps5;rounded=F(201,10000)
 need(finite_upper<rounded,'finite completion remains below201/10000')
 margins={key:v-rounded for key,v in other.items()}
 need(all(v>F(3,500) for v in margins.values()),'all seven coarse GOOD margins')
 gap=m-rounded
 need(gap==F(1368633457,225000000000),'common readable GOOD lower')
 fibre=min(F((22-q)*(28-q)-q,616) for q in range(1,20))
 need(fibre==F(1,77),'original two-axis fibre floor')
 haar=gap*fibre/density
 need(haar==F(1368633457,233887500000000) and haar>F(1,171000),'original Haar lower')
 same_root=(coarse[2,4,1]-F(19,1200))*fibre/density
 coherent=F(449287056937,6056623125000000000)
 need(same_root==F(110955529,467775000000000) and same_root>F(1,15592500),'same-root conversion')
 head_floor=F(1,80000000000)
 need(min(same_root,coherent,haar)>head_floor,'remaining root cases exceed common head floor')
 tail_primes=(3,5,7,11,13,17,19,23,29)
 moment=prod(F(p*(p+1),(p-1)**2) for p in tail_primes)
 need(moment==F(14003665,540672),'complete head moment')
 cutoff,ell=10**13,27
 need(cutoff>=286 and ell>=4 and 3**ell<=cutoff,'inherited analytic tail hypotheses')
 c=F(2*ell*ell+1,2*ell*ell-1)
 tau=c**7/cutoff*F(cutoff,cutoff-3)**2*sum(F(factorial(7),factorial(7-j)*ell**j) for j in range(8))
 tail_cost=moment*tau;tail_margin=head_floor-tail_cost
 need(tail_margin>F(1,125000000000),'strict distorted-mass continuation margin')
 result={'scope':'Two fixed old centres agree at every queried depth except at one old prime q; arbitrary disagreement at q, including different first digits; each complete original later numerical label independently chooses one centre; one legal completed old source has coarse type other than(2,4,1). Other anchor phases and original deep pure classes are unrestricted.',
 'inputs':INPUTS,'all_32_source_vertices':groups,'all_coarse_mass_minima':coarse,'nonworst_coarse_minimum':m,'all_seven_split_coordinate_bounds':calculations,'full_pure_BAD_upper':B,'full_pure_BAD_upper_float':float(B),'retained_pure_prefix_heights':{'3':h3,'5':h5},'released_pure_tail_error':{'3':eps3,'5':eps5,'sum':eps3+eps5},'finite_prefix_BAD_upper':finite_upper,'finite_prefix_BAD_upper_float':float(finite_upper),'strict_readable_BAD_upper':rounded,'all_seven_GOOD_margins':margins,'strict_GOOD_lower':gap,'strict_GOOD_lower_float':float(gap),'joint_density_cap':density,'original_fibre_floor':fibre,'strict_original_Haar_lower':haar,'strict_original_Haar_lower_float':float(haar),'readable_strict_Haar_lower':F(1,171000),'remaining_root_Haar_bounds':{'same_root_strict':same_root,'coherent_nonstrict':coherent},'large_prime_continuation':{'strict_head_Haar_floor':head_floor,'head_moment':moment,'cutoff':cutoff,'ell':ell,'c':c,'tau7':tau,'distorted_mass_cost':tail_cost,'distorted_mass_cost_float':float(tail_cost),'strict_distorted_mass_margin':tail_margin,'strict_distorted_mass_margin_float':float(tail_margin),'readable_strict_distorted_mass_lower':F(1,125000000000)},'worst_chart_closed':False,'source_producers_rerun':False,'Lean_rerun':False,'unrestricted_erdos7_resolved':False}
 text=json.dumps(encode(result),indent=2)+'\n'
 if args.output:args.output.write_text(text)
 else:
  retained=Path(__file__).with_name('single_coordinate_nonworst_source.json')
  need(json.loads(retained.read_text())==json.loads(text),'retained result differs from exact replay')
  print(text,end='')
if __name__=='__main__':main()
