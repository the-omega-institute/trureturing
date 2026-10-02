"""One actual A1 source: preserve head mass/caps, improve fixed29 continuation.

All numerical phases are CRT constants. Infinite pure completions are
explicit disjoint antichains with exact geometric masses. Full-height
source reasoning is supplied in the companion note, not inferred from
finite enumeration. No Lean claim.
"""
from fractions import Fraction as F
from math import prod
from pathlib import Path
from collections import Counter
import argparse,json

PRIMES=(3,5,7,11,13,17,19,23,29)
CAPS={7:F(3,2),11:F(5,3),13:F(3,2),17:F(2),19:F(9,5),23:F(11,5),29:F(7,3)}
CORE=((3,0),(9,1),(27,4),(5,0),(25,1),(15,2),(45,8),(75,11),
      (7,0),(21,1),(35,29),(63,16),(105,44),(11,0),(165,89),
      (13,0),(17,0),(19,0),(23,0),(29,0))
XI=(1,4,7,14)


def need(ok,why):
    if not ok:raise ValueError(why)


def crt(pairs):
    modulus=prod(m for m,a in pairs)
    residue=sum(a*(modulus//m)*pow(modulus//m,-1,m)for m,a in pairs)%modulus
    need(all(residue%m==a%m for m,a in pairs),'One simultaneous CRT phase')
    return modulus,residue


def pure_phase(p,e):
    need(p in PRIMES and type(e)is int and e>=1,'Pure label domain')
    if p==3:
        if e<=3:return (0,1,4)[e-1]
        return 13+27*((3**(e-4)-1)//2)
    if p==5:
        if e==1:return 0
        if e==2:return 1
        return 1+5*((5**(e-2)-1)//4)
    if e==1:return 0
    return 1+p*((p**(e-2)-1)//(p-1))


def selected_anchor_mass(x):
    return (1-F(x%27==13,2))*(1-F(x%5==1,4)-F(x%3==2 and x%5==1,5))


def actual_targets(x):
    return {r7 for d,a,r7 in ((3,1,1),(5,4,1),(9,7,2),(15,14,2))if x%d==a}


def padded(x,alternative=False):
    s=sum(x%d==a for d,a in zip((3,5,9,15),XI));roots=set(actual_targets(x))
    for r in range(1,7):
        if len(roots)==s:break
        roots.add(r)
    if alternative and x==34:roots={1,2,4}
    need(actual_targets(x)<=roots and len(roots)==s and 0 not in roots,'Charged legal padding')
    return roots


def head7(x,alternative=False):
    roots=padded(x,alternative)
    good=F(6-len(roots),7)-(F(1,42)if 1 not in roots else 0)
    density=min(CAPS[7],1/good)
    return roots,good,density,min(F(1),CAPS[7]*good)


def original29():
    out=[]
    for a in range(4):
        for b in range(4):
            beta=1+4*a+b
            pairs=[(7,4),(29,beta)]
            if a:pairs.append((3**a,7%(3**a)))
            if b:pairs.append((5**b,4%(5**b)))
            m,r=crt(pairs)
            out.append({'a':a,'b':b,'modulus':m,'phase':r,'root29':beta,
                        'old_modulus':m//29,'old_phase':r%(m//29)})
    return out


def survival29(active):
    if not active:
        good=F(27,28)
    else:
        need(1 in active,'Every nonempty future hit set contains root1 and its complete pure tail')
        good=F(28-len(active),29)
    return min(F(1),CAPS[29]*good)


def calculate():
    future=original29();original=list(CORE)+[(r['modulus'],r['phase'])for r in future]
    need(len(original)==36 and len({m for m,a in original})==36,'36 distinct original numerical labels')
    need(all(m>1 and m%2==1 and 0<=a<m for m,a in original),'Odd nonunit labels and normalized global phases')
    selected=(15,21,35,45,63,75,105,165);phase=dict(CORE)
    for m in selected:
        for d in phase:
            if d<m and m%d==0:
                need(phase[m]%d!=phase[d],'Selected class avoids every declared proper divisor')
    sharp_phase=dict(phase);sharp_phase[105]=79
    for m in selected:
        for d in sharp_phase:
            if d<m and m%d==0:
                need(sharp_phase[m]%d!=sharp_phase[d],'Half-bound sharpness control has legal selected phases')
    sharp_targets=[sharp_phase[m]%7 for m in (21,35,63,105)if 34%(m//7)==sharp_phase[m]%(m//7)]
    need(len(sharp_targets)==4 and len(set(sharp_targets))==2,
         'Separate actual selected-phase control realizes the sharp half survival factor')
    antichain_checks=0
    for p in PRIMES:
        for e in range(1,21):
            ae=pure_phase(p,e)
            need(0<=ae<p**e,'Normalized pure prefix')
            for f in range(1,e):
                need(ae%(p**f)!=pure_phase(p,f),'Disjoint pure antichain at sampled finite depths')
                antichain_checks+=1
    need(sum((F(1,3**e)for e in range(1,4)),F(0))==F(13,27),'Pure3 shallow mass')
    need(F(1,2)-F(13,27)==F(1,54),'All higher pure3 mass is in row13 with relative mass1/2')
    need(F(1,4)-F(1,5)-F(1,25)==F(1,100),'All higher pure5 mass lies in column1 with relative mass1/20')
    for e in range(3,21):need(pure_phase(5,e)%25!=11,'75 child disjoint from every specified pure5 tail')
    cells=[x for x in range(135)if x%3!=0 and x%9!=1 and x%27!=4
           and x%5!=0 and x%15!=2 and x%45!=8]
    need(len(cells)==44 and 34 in cells and 23 in cells,'Actual terminalA1 core')
    coarse=[];masses=[F(0),F(0)]
    for x in cells:
        alpha=selected_anchor_mass(x)
        need(0<alpha<=1,'Actual anchor submeasure on retained cell')
        current=[]
        for alt in (False,True):
            roots,good,density,survival=head7(x,alt)
            for p in (11,13,17,19,23):
                gp=F(9,11)if p==11 and x%15==14 else F(p-2,p-1)
                need(CAPS[p]*gp>=1,'Every stage11..23 current bad set can be avoided at zero loss')
            mass=alpha*survival/F(135);masses[alt]+=mass
            current.append({'padded7_roots':sorted(roots),'good7_haar':good,
                            'live7_density':density,'coarse_mass23':mass})
        need(current[0]['coarse_mass23']==current[1]['coarse_mass23'],'Preserved actual mass at every135cell')
        if x!=34:need(current[0]==current[1],'Physical source differs only at cell34')
        coarse.append({'cell':x,'anchor_relative_mass':alpha,'baseline':current[0],'changed':current[1]})
    need(masses[0]==masses[1]>0,'Equal actual mass23, not merely equal lower bounds')
    need(sum(selected_anchor_mass(x)for x in cells)==F(1473,40),'Exact selected anchor mass')
    need(actual_targets(34)=={1,2}and padded(34)=={1,2,3}and padded(34,True)=={1,2,4},'Actual collision supplies one padding choice')
    loss=[F(0),F(0)];hist=Counter();point_checks=0
    for h in range(3375):
        for root7 in range(7):
            old_mod,old=crt([(3375,h),(7,root7)])
            active={r['root29']for r in future if old%r['old_modulus']==r['old_phase']}
            count=sum(h%(3**a)==7%(3**a)and h%(5**b)==4%(5**b)
                      for a in range(4)for b in range(4))if root7==4 else 0
            need(len(active)==count,'Literal global CRT originals equal nested-prefix hit count')
            retention=survival29(active);hist[len(active)]+=1;point_checks+=1
            bad=(h%27==7 and h%125==4 and root7==4)
            need((retention<1)==bad,'The sole lossy marked cylinder is the actual target prefix')
            if bad:need(retention==F(28,29),'Exact all-height current29 retention')
            if h%135==34:
                need(selected_anchor_mass(34)==1,'No omitted anchor loss on the changed cell')
                for alt in (False,True):
                    roots,good,density,retained=head7(34,alt)
                    if root7!=0 and root7 not in roots:
                        need(root7!=1,'Pure7 higher tail is already in an excluded root')
                        loss[alt]+=density/F(3375*7)*(1-retention)
    need(loss==[F(1,456750),F(0)],'Padding alone removes exactly the actual future29 loss')
    mass29=[masses[j]-loss[j]for j in range(2)]
    need(mass29[1]-mass29[0]==F(1,456750),'Strict gain with equal head mass and same caps')
    variants=[{1,2,r}for r in (3,4,5,6)]
    for roots in variants:
        need(actual_targets(34)<=roots and len(roots)==3,'Every mixed cell34 padding is legal')
        need(F(6-len(roots),7)==F(3,7),'Every cell34 variant has the same pure-tail-aware good mass')
    mixed_densities={r:sum((CAPS[7]if r not in roots else F(0)for roots in variants),F(0))/4
                     for r in (3,4,5,6)}
    need(set(mixed_densities.values())=={F(9,8)},'Averaged actual cell34 live7 density equals its improved cap')
    mixed_loss=mixed_densities[4]/F(3375*7*29)
    need(mixed_loss==F(1,609000)<loss[0],'Uniform admissible padding mixture strictly improves actual29 loss')
    query_bound=F(3,2)*F(3,2)*F(5,4)*F(7,6)*F(101,90)*F(12,11)*F(16,15)*F(18,17)*F(22,21)
    need(query_bound==F(404,85)<28*masses[0],
         'Complete all-height first-moment upper bound is below28 times this actual source mass')
    return {'scope':'One explicit36-original nine-prime family and specified countable pure completion; '
                    'all original phases fixed, all pure heights allowed. Not a theorem for arbitrary A1 families.',
       'originals':[{'modulus':m,'phase':a}for m,a in sorted(original)],'future29':future,
       'a1_node':(2,4,1,8,1,2,1,0,13),'xi':XI,'eta165':14,
       'complete_pure_antichains':'Exact formulas in pure_phase and companion proof; sampled pair checks are supplementary.',
       'pure_prefix_sample_pair_checks':antichain_checks,'physical_coarse_source':coarse,
       'head23_mass':masses[0],'conditional_caps':CAPS,'actual_changed_cell':34,
       'actual_target_prefix':{'mod27':7,'mod125':4,'mod7':4},
       'actual_target_old_phase':crt([(27,7),(125,4)])[1],
       'source_mass_on_target_3_5_prefix':F(1,5250),
       'baseline_mass_on_target_prefix_and7root':F(1,15750),
       'future29_hit_count_histogram':dict(sorted(hist.items())),
       'actual_old_prefix_points_checked':point_checks,
       'baseline_29_loss':loss[0],'changed_29_loss':loss[1],
       'baseline_29_mass':mass29[0],'changed_29_mass':mass29[1],
       'strict_actual29_mass_gain':F(1,456750),
       'cell34_uniform_padding_live7_density':F(9,8),
       'cell34_uniform_padding_29_loss':mixed_loss,
       'cell34_uniform_padding_actual29_mass_gain':loss[0]-mixed_loss,
       'half_survival_sharpness_control':{'only_phase_change':{'modulus':105,'phase':79},
                                        'cell':34,'active_roots':sharp_targets,'survival_factor':F(1,2)},
       'same_all_query_comparison_caps':True,'rho_s_used_as_actual_event':False,
       'actual_full_query_sum_upper_bound':query_bound,
       'actual_full_query_bound_ratio':query_bound/masses[0],
       'arbitrary_single29_first_moment_reserve':masses[0]-query_bound/28,
       'query_bound_scope':'Same bound for both sources; no claim that their exact query maxima agree or differ.',
       'all_height_claim_basis':'Explicit pure antichain sums and full conditional current kernels; no finite-height inference.',
       'lean_verification':False}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-result',type=Path);args=parser.parse_args()
    result=json.loads(json.dumps(calculate(),default=str))
    if args.write_result:args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:need(result==json.loads(Path(__file__).with_suffix('.json').read_text()),'Fresh exact actual source data equals retained result')
    print(json.dumps({k:result[k]for k in ('head23_mass','baseline_29_loss','changed_29_loss','strict_actual29_mass_gain','actual_old_prefix_points_checked','lean_verification')},indent=2))

if __name__=='__main__':main()
