"""Exact fixed-source certificate for all-height corepoint completion margins.

The OLD and NEW digit patterns are precisely Chapter20's actual AP family.
This script reconstructs one coefficient certificate; it does not search phases.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import ceil, prod
from pathlib import Path
import json
from importlib.util import module_from_spec, spec_from_file_location

def load_patterns(path):
    """Reuse the existing Chapter20 source constants; do not copy its table."""
    spec=spec_from_file_location('e7_existing_ch20_patterns',path)
    if spec is None or spec.loader is None:
        raise RuntimeError('Cannot load Chapter20 pattern source')
    source=module_from_spec(spec)
    spec.loader.exec_module(source)
    return source


def require(ok,message):
    if not ok:raise AssertionError(message)


def crt(congruences):
    modulus=prod(m for m,_ in congruences)
    residue=sum(a*(modulus//m)*pow(modulus//m,-1,m) for m,a in congruences)%modulus
    require(all(residue%m==a for m,a in congruences),'literal CRT residues')
    return (modulus,residue)


def coefficients(source):
    PRIMES,OLD,NEW,SUPPORTS=source.PRIMES,source.OLD,source.NEW,source.SUPPORTS
    denominator=[0]*16;numerator=[0]*16;quotient_cells=0
    for word in product(*[(0,)+tuple(range(2,p)) for p in PRIMES]):
        quotient_cells+=1
        if any(tuple(word[i] for i in SUPPORTS[mask])==phase for mask,phase in OLD.items()):
            continue
        zero_mask=sum(1<<i for i,x in enumerate(word) if x==0)
        g=sum(tuple(word[i] for i in SUPPORTS[mask])==phase for mask,(_,phase) in NEW.items())
        denominator[zero_mask]+=1
        numerator[zero_mask]+=g+int(g>0)
    require(quotient_cells==2880,'one fixed original-family quotient')
    require(denominator==[1191,469,274,98,145,54,32,11,117,44,26,9,14,5,3,1],
            'actual survivor polynomial coefficients')
    require(numerator==[2066,394,314,40,202,32,28,2,170,28,24,2,16,2,2,0],
            'same-law joint-load polynomial coefficients')
    slack=[2066*d-1191*n for d,n in zip(denominator,numerator)]
    require(all(v>=0 for v in slack),'coefficientwise joint-load inequality for all heights')
    require(slack[0]==0 and all(v>0 for v in slack[1:]),'strict finite-height slack')
    haar_denominator=[prod(p-1 for i,p in enumerate(PRIMES) if not mask>>i&1)
                      for mask in range(16)]
    haar_slack=[2880*d-1191*c for d,c in zip(denominator,haar_denominator)]
    require(all(v>=0 for v in haar_slack),'coefficientwise Haar survivor lower bound')
    return denominator,numerator,slack,haar_denominator,haar_slack


def materialize(heights,source):
    PRIMES,OLD,NEW,SUPPORTS=source.PRIMES,source.OLD,source.NEW,source.SUPPORTS
    old=[];new=[]
    for mask,ids in SUPPORTS.items():
        for exponents in product(*(range(1,heights[i]+1) for i in ids)):
            powers=[PRIMES[i]**e for i,e in zip(ids,exponents)]
            old.append(crt([(power,digit*PRIMES[i]**(e-1))
                            for power,i,e,digit in zip(powers,ids,exponents,OLD[mask])]))
            color,digits=NEW[mask]
            new.append(crt([(3,color)]+[(power,digit*PRIMES[i]**(e-1))
                            for power,i,e,digit in zip(powers,ids,exponents,digits)]))
    old.sort();new.sort()
    expected=prod(h+1 for h in heights)-1
    require(len(old)==len(new)==expected,'complete original cofactor inventory')
    require(len({d for d,_ in old+new})==2*expected,'distinct numerical original moduli')
    require(all(d>1 and 0<=a<d for d,a in old+new),'nonunit original labels and residues')
    return old,new


def literal_signature_control(heights,old,new,primes):
    # Decode and count actual numerical congruences. Pattern tables are not
    # consulted below: each coordinate is partitioned by full label membership.
    labels=old+new;nold=len(old);nlabels=len(labels)
    all_bits=(1<<nlabels)-1;old_bits=(1<<nold)-1;new_bits=all_bits^old_bits
    axes=[];signature_counts=[]
    for p,height in zip(primes,heights):
        requirements=[];pure_old_bits=0
        for index,(modulus,residue) in enumerate(labels):
            cofactor=modulus if index<nold else modulus//3
            require(index<nold or modulus%3==0 and modulus%9!=0,'literal first ternary layer')
            power=1;remainder=cofactor
            while remainder%p==0:
                power*=p;remainder//=p
            requirements.append((power,residue%power))
            if index<nold and remainder==1:
                pure_old_bits|=1<<index
        signatures=Counter()
        for leaf in range(p**height):
            bits=0
            for index,(power,residue) in enumerate(requirements):
                if leaf%power==residue:bits|=1<<index
            if bits&pure_old_bits:continue
            signatures[bits]+=1
        signature_counts.append(len(signatures));axes.append(tuple(signatures.items()))
    histogram=Counter();checked=0
    for cell in product(*axes):
        checked+=1;bits=all_bits;weight=1
        for signature,mass in cell:
            bits&=signature;weight*=mass
        if bits&old_bits:continue
        histogram[(bits&new_bits).bit_count()]+=weight
    survivors=sum(histogram.values())
    raw_g=sum(g*w for g,w in histogram.items())
    raw_union=survivors-histogram[0]
    return dict(axis_signature_counts=signature_counts,signature_cells=checked,
                survivor_count=survivors,g_histogram=dict(sorted(histogram.items())),
                Eg=F(raw_g,survivors),Pr_g_positive=F(raw_union,survivors),
                joint_load=F(raw_g+raw_union,survivors))


def evaluate(coefficient,u):
    return sum((F(c)*prod(u[i] for i in range(4) if mask>>i&1)
                for mask,c in enumerate(coefficient)),F(0))


def build_certificate(pattern_source):
    source=load_patterns(pattern_source)
    D,N,slack,haar_denominator,haar_slack=coefficients(source)
    PRIMES=source.PRIMES
    heights=(4,3,2,2)
    old,new=materialize(heights,source)
    control=literal_signature_control(heights,old,new,PRIMES)
    weights=[(p**h-1)//(p-1) for p,h in zip(PRIMES,heights)]
    u=[F(1,w) for w in weights]
    require(control['survivor_count']==prod(weights)*evaluate(D,u),'literal survivor denominator equals polynomial')
    require(control['joint_load']==evaluate(N,u)/evaluate(D,u),'literal joint load equals polynomial')
    require(control['survivor_count']==1821723476,'outside-strip literal survivor count')
    require(control['Eg']==F(1977830909,1821723476)>1,'nontrivial high first-layer mean')
    require(control['joint_load']<F(2066,1191),'strict joint-load budget at actual finite heights')
    R=F(1301,1185);joint=F(2066,1191);load=(R+joint)/2;margin=F(3,2)-load
    require(R+joint==F(444189,156815)<3,'same-law point-selection budget')
    require(load==F(444189,313630) and margin==F(13128,156815)>0,'uniform actual corepoint margin')
    good_eta=margin/2
    mu_good=margin/(3-margin)
    haar_survivor=F(397,960)
    haar_good=haar_survivor*mu_good
    require(good_eta==F(6564,156815) and mu_good==F(4376,152439),
            'positive-mass core margin')
    require(haar_good==F(217159,18292680),'height-independent Haar good-set mass')
    M1=prod(F(p,p-1) for p in PRIMES)
    M2=prod(F(p*(p+1),(p-1)**2) for p in PRIMES)
    density_cap=85
    cutoff_integer=ceil(density_cap*M2)
    require(1/haar_good<density_cap,'rounded Haar density cap is valid')
    require(M1==F(1001,576) and M2==F(7007,1440),'original head moment sums')
    require(density_cap*M2==F(119119,288) and cutoff_integer==414,'rounded-cap tail cutoff integer')
    require(ceil(M2/haar_good)==410,'exact-cap tail cutoff integer')
    require(F(1,3**250)<good_eta,'tail error fits the pointwise good-set margin')
    return dict(scope='All old Chapter20 classes present; first-layer child patterns fixed, classes may be omitted, and mod3 residues arbitrary per modulus. Arbitrary positive finite core heights, later original phases and ternary height. No unrestricted early-phase theorem.',
                source='problem-details/20-original-ap-three-color-intersections-can-exceed-the-residual-threshold.md',
                primes=PRIMES,zero_mask_bit_order=PRIMES,
                survivor_coefficients=D,joint_load_coefficients=N,coefficientwise_slack=slack,
                haar_denominator_coefficients=haar_denominator,haar_survivor_slack=haar_slack,
                universal_joint_bound=joint,existing_later_layout_envelope=R,
                universal_core_load_upper=load,uniform_margin_below_three_halves=margin,
                good_set=dict(psi_threshold=3-margin,load_margin=good_eta,
                              mu_mass_lower=mu_good,haar_survivor_lower=haar_survivor,
                              haar_mass_lower=haar_good,haar_density_upper=1/haar_good),
                tail_interface=dict(haar_density_cap=density_cap,M1=M1,M2=M2,
                                    cutoff_integer=cutoff_integer,cutoff_expression='3^256 * 414^3',
                                    exact_cap_cutoff_integer=ceil(M2/haar_good),
                                    weighted_tail_numerator=324*density_cap*M1,
                                    weighted_tail_error_upper=F(1,3**250)),
                outside_strip_control=dict(heights=heights,old_originals=old,first_layer_originals=new,**control),
                proof_boundary='The all-height result follows from nonnegative polynomial coefficients and the existing same-law later-layout theorem; the finite signature control checks one literal original family.')


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [encode(v) for v in value]
    return value


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='Optional exact JSON destination; default is stdout.')
    parser.add_argument('--pattern-source',type=Path,
                        default=Path(__file__).with_name('k5_three_color_ap_control.py'))
    args=parser.parse_args();result=build_certificate(args.pattern_source)
    payload=json.dumps(encode(result),indent=2)+'\n'
    if args.output is None:
        print(payload,end='')
    else:
        args.output.write_text(payload)
        control=result['outside_strip_control']
        print(json.dumps(encode(dict(joint_bound=result['universal_joint_bound'],
              core_load_upper=result['universal_core_load_upper'],margin=result['uniform_margin_below_three_halves'],
              signature_cells=control['signature_cells'],axis_signature_counts=control['axis_signature_counts'],
              original_label_count=len(control['old_originals'])+len(control['first_layer_originals']),
              survivor_count=control['survivor_count'],Eg=control['Eg'],joint_load=control['joint_load'],
              tail_interface=result['tail_interface'])),indent=2))

if __name__=='__main__':main()
