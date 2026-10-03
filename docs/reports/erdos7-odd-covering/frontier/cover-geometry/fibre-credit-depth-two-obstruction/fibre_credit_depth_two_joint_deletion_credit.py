#!/usr/bin/env python3
"""Literal CRT verification of a same-marginals/different-credit pair.
All new originals are actual distinct odd numerical moduli. The common
prior is explicitly weighted and supported; no optimality/covering claim.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import lcm, prod
from pathlib import Path
import argparse,json


def check(ok, why):
    if not ok:
        raise RuntimeError(why)


def crt(pairs):
    modulus = prod(m for m,a in pairs)
    residue = sum(a*(modulus//m)*pow(modulus//m,-1,m) for m,a in pairs) % modulus
    check(all(residue%m == a%m for m,a in pairs), 'literal CRT reconstruction')
    return modulus,residue



def calculate():
    OLD=[(3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
         (21,0),(35,0),(63,0),(105,0),(315,0)]
    BASE=OLD+[(11,0),(13,0)]
    EXTRA=[(17,0),(19,0),(23,0)]
    OLD_SUPPORT=[x for x in range(315) if all(x%d != a for d,a in OLD)]
    check(len(OLD_SUPPORT)==102, 'actual 102-point old support')
    carrier=315*11*13
    prior={}
    coordinates={}
    for x,u,v in product(OLD_SUPPORT,range(3,11),range(3,13)):
        m,r=crt(((315,x),(11,u),(13,v)))
        check(m==carrier and r not in prior, 'background CRT injectivity')
        prior[r]=1
        coordinates[r]=(x,u,v)
    for x,u,v in product((2,47),(1,2),(1,2)):
        m,r=crt(((315,x),(11,u),(13,v)))
        check(r not in prior, 'spike/background supports disjoint')
        prior[r]=120
        coordinates[r]=(x,u,v)
    check(len(prior)==8168 and sum(prior.values())==9120, 'common weighted prior')
    check(all(all(r%d != a for d,a in BASE) for r in prior), 'prior avoids every base original')

    COMMON_NEW=[crt(((7,2),(11,1),(13,2))),crt(((21,2),(11,2),(13,1)))]
    NEW_A=COMMON_NEW+[
        crt(((35,47%35),(11,1),(13,2))),
        crt(((63,47),(11,2),(13,1))),
    ]
    NEW_B=COMMON_NEW+[
        crt(((35,47%35),(11,1),(13,1))),
        crt(((63,47),(11,2),(13,2))),
    ]
    families={'A':BASE+NEW_A, 'B':BASE+NEW_B}
    survivors={}
    for name,family in families.items():
        check(len(family)==17 and len({m for m,a in family})==17, 'distinct original labels')
        check(all(m>1 and m%2==1 and 0<=a<m for m,a in family), 'valid odd original classes')
        check(lcm(*(m for m,a in family))==carrier, 'actual carrier')
        extended=family+EXTRA
        check(len(extended)==len({m for m,a in extended})==20, 'twenty distinct originals on five outside axes')
        check(lcm(*(m for m,a in extended))==carrier*17*19*23, 'full five-axis actual carrier')
        survivors[name]={r:w for r,w in prior.items() if all(r%m != a for m,a in family)}
        check(sum(survivors[name].values())==8640 and len(survivors[name])==8164, 'same survivor mass/support size')
        check(all((w==1) or ((coordinates[r][1]==coordinates[r][2]) if name=='A'
                            else ((coordinates[r][1]==coordinates[r][2]) if coordinates[r][0]==2
                                  else (coordinates[r][1]!=coordinates[r][2])))
                  for r,w in survivors[name].items()), 'coordinate pattern matches actual CRT deletion')


    def marginals(measure):
        old=defaultdict(int)
        single=defaultdict(int)
        for r,w in measure.items():
            x,u,v=coordinates[r]
            old[x]+=w
            single[(x,11,u)]+=w
            single[(x,13,v)]+=w
        return dict(old),dict(single)


    check(marginals(survivors['A'])==marginals(survivors['B']),
          'same full old marginal and both conditional singleton tables')
    core_divisors=[d for d in range(1,316) if 315%d==0]
    slot_profiles=[]
    scores={name:F(0) for name in ('prior','A','B','background')}
    credits={'A':F(0),'B':F(0)}
    measures={'prior':prior,**survivors,'background':{r:w for r,w in prior.items() if w==1}}
    for d in core_divisors:
        saturated=[p for p,h in ((3,2),(5,1),(7,1)) if d%(p**h)==0]
        kappa=prod(F(p,p-1) for p in saturated)-1
        if not kappa:
            continue
        for e11,e13 in product((0,1),repeat=2):
            modulus=d*11**e11*13**e13
            hist={}
            maxima={}
            for name,measure in measures.items():
                cells=defaultdict(int)
                for r,w in measure.items():
                    cells[r%modulus]+=w
                hist[name]=cells
                maxima[name]=max(cells.values(),default=0)
                scores[name]+=kappa*maxima[name]
            row={'old_divisor':d,'outside_support':[p for p,e in ((11,e11),(13,e13)) if e],
                 'numerical_query_modulus':modulus,'kappa':str(kappa),
                 'cylinder_maxima':maxima,'credits':{}}
            for name in ('A','B'):
                # Zero-mass phases give slack equal to old maximum. Including
                # that value covers all unrepresented residue classes exactly.
                minimum=maxima['prior']
                minimizing_phase=None
                for a,old_mass in hist['prior'].items():
                    deleted_mass=old_mass-hist[name].get(a,0)
                    check(deleted_mass>=0, 'genuine measure restriction')
                    value=maxima['prior']-old_mass+deleted_mass
                    if value<minimum:
                        minimum=value
                        minimizing_phase=a
                drop=maxima['prior']-maxima[name]
                check(minimum==drop, 'exact slack-plus-joint-deletion credit')
                credits[name]+=kappa*drop
                row['credits'][name]={'debit_reduction':drop,'minimizing_phase':minimizing_phase}
            slot_profiles.append(row)
    check(len(slot_profiles)==40, 'forty nonzero two-outside slots')
    multiplier=prod(F(p,p-1) for p,a in EXTRA)
    check(multiplier==F(7429,6336), 'eight additional outside-subset factors')
    raw_prior_J=F(9120)-multiplier*scores['prior']
    results={}
    for name,measure in survivors.items():
        mass=F(sum(measure.values()))
        raw_debit=multiplier*scores[name]
        J=mass-raw_debit
        credit=multiplier*credits[name]
        check(J==raw_prior_J-480+credit, 'same-source exact aggregate deletion identity')
        results[name]={'mass':str(mass),'retention_of_prior':str(mass/9120),
                      'weighted_query_debit':str(raw_debit),'J':str(J),
                      'normalized_higher_core_debit':str(raw_debit/mass),
                      'deletion_credit':str(credit)}
    check(F(results['A']['J'])==-F(802469,38016), 'A negative certificate margin')
    check(F(results['B']['J'])==F(9226681,38016), 'B positive certificate margin')
    check(F(results['A']['normalized_higher_core_debit'])==F(329260709,328458240), 'A lambda')
    check(F(results['B']['normalized_higher_core_debit'])==F(319231559,328458240), 'B lambda')
    different=[row for row in slot_profiles if row['cylinder_maxima']['A']!=row['cylinder_maxima']['B']]
    check([(row['old_divisor'],row['outside_support']) for row in different]
          ==[(5,[11,13]),(9,[11,13]),(15,[11,13]),(45,[11,13])], 'precise missing joint slots')
    check(all(row['cylinder_maxima']['A']==240 and row['cylinder_maxima']['B']==120
              for row in different),'literal joint maximum gap')
    raw_haar_cap=carrier*120*multiplier
    Haar_B=F(results['B']['J'])/raw_haar_cap
    background_score=scores['background']
    background_J=F(8160)-multiplier*background_score
    check(background_J>0, 'both actual families admit a different positive supported source')
    output={
        'scope':__doc__, 'base_carrier':carrier,'old_originals':OLD,
        'outside_pure_originals':[(11,0),(13,0)]+EXTRA,
        'new_originals_A':NEW_A,'new_originals_B':NEW_B,
        'original_count_in_five_axis_carrier':20,
        'common_prior':{'old_support_count':102,'background_cells':8160,
                        'background_each_weight':1,'special_old_rows':[2,47],
                        'special_outside_roots':[1,2],'special_cells':8,'special_each_weight':120,
                        'total_mass':9120,'extra_outside_law':'Independent uniform nonzero roots at17,19,23.'},
        'same_old_and_conditional_singleton_marginals':True,
        'full_five_axis_query_multiplier':str(multiplier),
        'prior_weighted_query_debit':str(multiplier*scores['prior']),
        'prior_J':str(raw_prior_J),'results':results,
        'changed_joint_slots':different,'all_nonzero_two_outside_slots':slot_profiles,
        'raw_measure_Haar_cap':str(raw_haar_cap),'B_high_core_Haar_lower':str(Haar_B),
        'common_background_J':str(background_J),
        'conclusion':'Identical retention and all conditional singleton marginals do not determine the sign of the current common-source high-core margin. Both families have another feasible source; this is not a universal source-selection obstruction or a covering.'}
    return output

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        check(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
              'retained result agrees with literal joint deletion-credit replay')
        print(rendered,end='')
    else:args.output.write_text(rendered)

if __name__=='__main__':main()
