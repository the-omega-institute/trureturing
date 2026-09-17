#!/usr/bin/env python3
"""Verify finite45 exact minimax laws and the universal315 supported-moment lift.

All arithmetic and exhaustive layout checks use only the Python standard library.
The certificate contains probability laws and dual distributions, not solver claims.
The hierarchical symmetry/completion and prime7 lift are ordinary proof inputs.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import permutations,product
from math import lcm,prod
from pathlib import Path
import argparse,json

MODULI=(3,9,5,15,45)
KINDS=('same_root','same_column','different_column')

def require(b,message):
 if not b:raise ValueError(message)

def crt(x,y):return x+9*((y-x)*4%5)

def canonical(root,kind):
 affected=(1,7) if root==1 else (2,5,8)
 other=(2,5,8) if root==1 else (1,7)
 xy=(affected[0],2) if kind=='same_root' else (other[0],1 if kind=='same_column' else 2)
 classes=[(3,0),(9,4),(5,0),(15,crt(affected[0],1)%15),(45,crt(*xy))]
 S=tuple(v for v in range(45) if all(v%m!=r for m,r in classes))
 return classes,S

def integer_probability(values):
 weights=list(map(F,values));require(weights and min(weights)>=0 and sum(weights)==1,'rational probability')
 denominator=lcm(*(w.denominator for w in weights))
 return [int(w*denominator) for w in weights],denominator

def symmetry_check():
 # Automorphisms preserve ternary root/leaf cylinders and quinary columns.
 short,long=(1,7),(2,5,8);columns=(1,2,3,4)
 images={}
 for root,kind in product((1,2),KINDS):
  _,S=canonical(root,kind);orbit=set()
  for ps,pl,pc in product(permutations(short),permutations(long),permutations(columns)):
   rowmap=dict(zip(short+long,ps+pl));colmap=dict(zip(columns,pc))
   image=frozenset(crt(rowmap[v%9],colmap[v%5]) for v in S)
   orbit.add(image)
  require(not any(image in images for image in orbit),'six canonical survivor orbits are disjoint')
  for image in orbit:images[image]=(root,kind)
 raw=0;counts={(r,k):0 for r,k in product((1,2),KINDS)}
 for root,col in product((1,2),columns):
  partial=[(3,0),(9,4),(5,0),(15,crt(root,col)%15)]
  before=[v for v in range(45) if all(v%m!=r for m,r in partial)]
  for deleted in before:
   S=frozenset(v for v in before if v!=deleted)
   require(S in images,'every active normalized forbidden assignment belongs to a canonical orbit')
   counts[images[S]]+=1;raw+=1
 require(raw==140 and len(images)==140,'complete normalized active-assignment enumeration')
 require([counts[(r,k)] for r,k in product((1,2),KINDS)]==[24,12,36,36,8,24],'exact orbit sizes')
 return [{'root':r,'deleted45_orbit':k,'normalized_assignments':counts[(r,k)]} for r,k in product((1,2),KINDS)]

def verify_case(row):
 root,kind=row['root'],row['deleted45_orbit'];classes,S=canonical(root,kind)
 require(row['classes']==[list(pair) for pair in classes] and row['survivors']==list(S),'canonical actual forbidden classes and survivors')
 weights,denominator=integer_probability(row['optimal_probabilities'])
 require(len(weights)==len(S),'one primal probability per survivor')
 residues=[sorted({v%m for v in S}) for m in MODULI]
 masks=[[[int(v%m==r) for v in S] for r in values] for m,values in zip(MODULI,residues)]
 upper=0;profile=[0]*8;uniform_square=0;uniform_profile=[0]*8;layout_count=0
 for choice in product(*masks):
  load=[1+sum(c[j] for c in choice) for j in range(len(S))]
  upper=max(upper,sum(w*l*l for w,l in zip(weights,load)))
  uniform_square=max(uniform_square,sum(l*l for l in load))
  for t in range(8):
   profile[t]=max(profile[t],sum(w*max(l-t,0) for w,l in zip(weights,load)))
   uniform_profile[t]=max(uniform_profile[t],sum(max(l-t,0) for l in load))
  layout_count+=1
 G=F(upper,denominator)
 dual=row['dual_test_layouts'];dual_weights,dual_denominator=integer_probability([r['weight'] for r in dual])
 dual_scores=[0]*len(S)
 for data,w in zip(dual,dual_weights):
  rs=data['residues'];require(len(rs)==len(MODULI) and all(type(r)is int and 0<=r<m for r,m in zip(rs,MODULI)),'valid dual test cylinders')
  for j,v in enumerate(S):
   load=1+sum(v%m==r for m,r in zip(MODULI,rs));dual_scores[j]+=w*load*load
 lower=F(min(dual_scores),dual_denominator)
 require(lower==G==F(row['minimax_Gamma']),'exact primal and dual minimax equality')
 require(layout_count==row['complete_test_layouts']==prod(map(len,residues)),'all effective independent test layouts checked')
 require(F(uniform_square,len(S))==F(row['uniform_Gamma']),'uniform-law comparison moment')
 require([F(row['uniform_stoploss_profile'][str(k)]) for k in range(7)]==[F(v,len(S)) for v in uniform_profile[:7]],'uniform stoploss profile')
 require([F(row['selected_optimal_Gamma_law_stoploss_profile'][str(k)]) for k in range(7)]==[F(v,denominator) for v in profile[:7]],'same rational law has the recorded stoploss profile')
 caps=[F(max(sum(w*c for w,c in zip(weights,mask)) for mask in choices),denominator) for choices in masks]
 R=sum(caps,F(0));require(0<=R<6,'positive prime7 conditional mass')
 # Gamma_(mu x Unif6) <= 3 Gamma_mu/2; mixed7 mass <= R/6.
 # L>=1 yields the improved once-conditioned unit-load moment inequality.
 lift=1+(F(3,2)*G-1)/(1-R/6)
 require(str(R)==row['R45'] and str(lift)==row['supported_Gamma315_upper'],'exact prime7 supported-law lift')
 return {'root':root,'deleted45_orbit':kind,'survivors':len(S),'test_layouts':layout_count,
         'minimax_Gamma45':str(G),'R45':str(R),'supported_Gamma315_upper':str(lift)}

def selected_law_convex_profile(rows):
    """Full315 increasing-convex profile for the fixed rational45 laws."""
    def atoms_from_calls(calls):
        require(calls[0]-calls[1] == 1 and calls[-1] == 0,
                'unit lower support and zero terminal stoploss')
        atoms = {k: calls[k-1]-2*calls[k]+(calls[k+1] if k+1 < len(calls) else 0)
                 for k in range(1, len(calls))}
        require(min(atoms.values()) >= 0 and sum(atoms.values()) == 1,
                'convex integer-threshold calls define a probability law')
        return {k: p for k, p in atoms.items() if p}

    def call(atoms, threshold):
        return sum((p*max(F(k)-threshold, 0) for k, p in atoms.items()), F(0))

    def encode(atoms):
        return {str(k): str(p) for k, p in sorted(atoms.items())}

    cases, common_calls = [], [F(0)]*13
    require([(r['root'], r['deleted45_orbit']) for r in rows] ==
            [(r, k) for r in (1, 2) for k in
             ('same_root', 'same_column', 'different_column')], 'six selected head laws')
    for row in rows:
        calls35 = [F(row['selected_optimal_Gamma_law_stoploss_profile'][str(t)])
                   for t in range(7)]
        old_atoms = atoms_from_calls(calls35)
        # Distribute a convex increment among six prime7 colours, then use
        # h(a+b) <= (h(2a)+h(2b))/2 for the two independent old test layouts.
        pre = {}
        for k, probability in old_atoms.items():
            pre[k] = pre.get(k, F(0))+F(5, 6)*probability
            pre[2*k] = pre.get(2*k, F(0))+probability/6
        removed = F(row['R45'])/6
        survival = 1-removed
        require(0 < survival <= 1, 'positive same-law prime7 survival')
        conditioned = {}
        # Keep the upper survival quantile. Increasing-convex comparison
        # passes to this worst conditional law by the CVaR variational bound.
        for k, probability in sorted(pre.items()):
            take = min(removed, probability)
            removed -= take
            if probability > take:
                conditioned[k] = (probability-take)/survival
        require(removed == 0 and sum(conditioned.values()) == 1,
                'exact top-quantile comparison probability')
        calls = [call(conditioned, F(t)) for t in range(13)]
        common_calls = [max(a, b) for a, b in zip(common_calls, calls)]
        actual_gamma = 1+(F(3, 2)*F(row['minimax_Gamma'])-1)/survival
        require(actual_gamma == F(row['supported_Gamma315_upper']),
                'same selected law also has its separate exact unit-loss moment bound')
        cases.append({'root': row['root'], 'deleted45_orbit': row['deleted45_orbit'],
                      'old_comparison_atoms': encode(old_atoms),
                      'survival_lower': str(survival),
                      'conditioned_comparison_atoms': encode(conditioned),
                      'mean_upper': str(call(conditioned, F(0))),
                      'actual_Gamma_upper': str(actual_gamma)})
    # All loads are integers1..12. Between consecutive integers, linear
    # interpolation of the pointwise maximum endpoint bounds dominates each
    # old call function. Convexity ensures nonnegative second differences.
    common = atoms_from_calls(common_calls)
    mean = sum(k*p for k, p in common.items())
    comparator_second = sum(k*k*p for k, p in common.items())
    actual_second = max(F(r['actual_Gamma_upper']) for r in cases)
    require(mean == F(110151471, 33504305)
            and comparator_second == F(7698860774322, 523303739795)
            and actual_second == F(198583, 15619), 'exact universal same-law profile constants')
    return {'cases': cases, 'universal_comparison_atoms': encode(common),
            'integer_threshold_stoploss_bounds': list(map(str, common_calls)),
            'universal_mean_upper': str(mean),
            'universal_actual_Gamma_upper': str(actual_second),
            'comparison_law_second_moment': str(comparator_second),
            'scope': 'For each distinct forbidden family with moduli dividing315 there is one supported probability law, common to all test layouts and all increasing convex costs, dominated by the displayed comparison law and satisfying the separate actual second-moment bound. No tail11 continuation or315 minimax optimality is claimed.'}


def verify(certificate):
 expected=list(product((1,2),KINDS));rows=certificate['cases']
 require([(r['root'],r['deleted45_orbit']) for r in rows]==expected,'exactly the six required canonical cases')
 orbits=symmetry_check();results=[verify_case(r) for r in rows]
 G45=max(F(r['minimax_Gamma45']) for r in results)
 G315=max(F(r['supported_Gamma315_upper']) for r in results)
 require(G45==F(22570,3361) and G315==F(198583,15619),'universal moment constants')
 summary={'normalized_assignments':140,'canonical_orbits':orbits,'effective_test_layouts':sum(r['test_layouts'] for r in results),
          'universal_sharp_minimax_Gamma45':str(G45),'universal_supported_Gamma315_upper':str(G315),'cases':results}
 require(summary==certificate['verified_result'],'fixed result equals recomputed exact certificate')
 profile=selected_law_convex_profile(rows)
 require(profile==certificate['selected_law_convex_profile'],'fixed same-law full convex profile')
 return {**summary, 'same_law_mean_upper':profile['universal_mean_upper'],
         'same_law_Gamma_upper':profile['universal_actual_Gamma_upper']}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('certificate',nargs='?',type=Path,default=(Path(__file__).resolve().parent / 'certificates/finite_head_geometry_certificate.json'))
 args=parser.parse_args();result=verify(json.loads(read_artifact_text(args.certificate)))
 print(json.dumps({'result':'PASS',**result}))
if __name__=='__main__':main()
