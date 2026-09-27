"""A finite original-cofactor frontier consumes report456's core margin.

The exact source constants are read from the existing report456 JSON. The
literal control imports only Chapter20's pattern provider, changes actual
old and first-layer residues above the frontier, omits shallow labels, and
keeps one numerical original class per modulus through ternary height six.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from math import ceil, prod
from pathlib import Path
import json


def require(condition,message):
    if not condition:
        raise AssertionError(message)


def load_patterns(path):
    spec=spec_from_file_location('e7_existing_patterns',path)
    require(spec is not None and spec.loader is not None,'existing pattern source is loadable')
    module=module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def smooth_prefix(primes,cutoff):
    values={1}
    for prime in primes:
        old=tuple(values)
        for value in old:
            current=value*prime
            while current<=cutoff:
                values.add(current)
                current*=prime
    return sorted(values)


def constants(reference):
    primes=tuple(reference['primes'])
    A=F(reference['universal_joint_bound'])+F(reference['existing_later_layout_envelope'])
    old_mass=F(reference['good_set']['haar_survivor_lower'])
    M1=F(reference['tail_interface']['M1'])
    M2=F(reference['tail_interface']['M2'])
    eta=F(1,50)
    threshold=3-2*eta
    seed_mass=old_mass*(1-A/threshold)
    cutoff=6125
    prefix=smooth_prefix(primes,cutoff)
    reciprocal_tail=M1-sum((F(1,a) for a in prefix),F(0))
    retained_mass=seed_mass-2*reciprocal_tail
    previous=prefix[-2]
    previous_tail=reciprocal_tail+F(1,cutoff)
    require(A==F(444189,156815),'existing selector constant')
    require(seed_mass==F(99917,5612160),'retuned seed mass')
    require(len(prefix)-1==57 and prefix[-1]==cutoff and previous==5929,'numerical cofactor frontier')
    require(reciprocal_tail==F(48136815122003,12637837812600000),'complete reciprocal tail')
    require(retained_mass==F(752533150011826549,73880799852459600000),'remaining good-set mass')
    require(retained_mass>F(1,100),'rounded density cap 100')
    require(seed_mass-2*previous_tail<F(1,100),'preceding numerical prefix fails the chosen mass certificate')
    box_rows=[]
    for caps in [(3,3,3,3),(4,3,2,2),(3,2,2,2)]:
        box_tail=M1*(1-prod(1-F(1,p**(cap+1)) for p,cap in zip(primes,caps)))
        mass=seed_mass-2*box_tail
        box_rows.append(dict(caps=caps,fixed_cofactors=prod(cap+1 for cap in caps)-1,
                             reciprocal_tail=box_tail,remaining_mass_lower=mass,
                             meets_density_100=mass>=F(1,100)))
    tail_integer=ceil(100*M2)
    require(tail_integer==487,'tail cutoff integer')
    require(324*100*M1==F(225225,4),'weighted tail coefficient')
    require(F(1,3**250)<eta,'tail error below core margin')
    return dict(primes=primes,reference_selector_upper=A,reference_survivor_haar_lower=old_mass,
                pointwise_load_margin=eta,selector_threshold=threshold,reference_good_haar_lower=seed_mass,
                changed_label_reciprocal_budget=seed_mass-F(1,100),
                cofactor_cutoff=cutoff,fixed_nonunit_cofactors=prefix[1:],fixed_cofactor_count=len(prefix)-1,
                maximum_fixed_original_phase_constraints=2*(len(prefix)-1),
                complete_one_layer_reciprocal_tail=reciprocal_tail,
                final_good_haar_lower=retained_mass,mass_surplus_over_one_hundredth=retained_mass-F(1,100),
                preceding_numeric_cutoff=previous,preceding_prefix_mass_lower=seed_mass-2*previous_tail,
                box_comparison=box_rows,
                tail_interface=dict(haar_density_cap=100,M1=M1,M2=M2,cutoff_integer=tail_integer,
                                    cutoff_expression='3^256 * 487^3',weighted_tail_numerator=324*100*M1))


def crt(pairs):
    modulus=prod(m for m,_ in pairs)
    residue=sum(a*(modulus//m)*pow(modulus//m,-1,m) for m,a in pairs)%modulus
    require(all(residue%m==a for m,a in pairs),'literal CRT construction')
    return modulus,residue


def materialize_reference(source,heights):
    old={};first={}
    for mask,indices in source.SUPPORTS.items():
        for exponents in product(*(range(1,heights[i]+1) for i in indices)):
            powers=[source.PRIMES[i]**e for i,e in zip(indices,exponents)]
            old_pairs=[(power,digit*source.PRIMES[i]**(e-1))
                       for power,i,e,digit in zip(powers,indices,exponents,source.OLD[mask])]
            a,residue=crt(old_pairs)
            old[a]=(a,residue)
            color,digits=source.NEW[mask]
            first_pairs=[(power,digit*source.PRIMES[i]**(e-1))
                         for power,i,e,digit in zip(powers,indices,exponents,digits)]
            first[a]=crt([(3,color)]+first_pairs)
    return old,first


def literal_control(source,certificate):
    primes=tuple(source.PRIMES);heights=(4,3,2,2);H=6
    Q=prod(p**h for p,h in zip(primes,heights));cutoff=certificate['cofactor_cutoff']
    reference_old,reference_first=materialize_reference(source,heights)
    cofactors=sorted(reference_old)
    require(len(cofactors)==179,'complete outside-strip reference inventory')
    target={e:[] for e in range(H+1)}
    changed={0:set(),1:set()}
    for a in cofactors:
        if a!=5:  # Actual missing shallow old original.
            residue=reference_old[a][1] if a<=cutoff else 0
            target[0].append((a,residue))
            if residue!=reference_old[a][1]:changed[0].add(a)
        if a!=7:  # Actual missing shallow first-layer modulus 21.
            cofactor_residue=reference_first[a][1]%a if a<=cutoff else 3%a
            target[1].append(crt([(3,(a+1)%3),(a,cofactor_residue)]))
            if cofactor_residue!=reference_first[a][1]%a:changed[1].add(a)
        for e,cofactor_residue in [(2,0),(3,2),(4,3),(5,4),(6,0)]:
            target[e].append(crt([(3**e,(17*e+a)%(3**e)),(a,cofactor_residue%a)]))
    actual=[label for e in range(H+1) for label in target[e]]
    require(len(actual)==len({m for m,_ in actual})==1251,'distinct actual original numerical moduli')
    require(all(m>1 and 0<=r<m for m,r in actual),'actual nonunit original labels')
    require(changed[0] and changed[1],'both early layers genuinely changed')
    require(all(a>cutoff for e in (0,1) for a in changed[e]),'changes occur only beyond the cofactor frontier')
    require(5 not in {m for m,_ in target[0]} and 21 not in {m for m,_ in target[1]},'missing shallow old and first labels')
    for e in range(H+1):
        for m,r in target[e]:
            a=m//(3**e)
            require(m%3**e==0 and a%3!=0 and a in reference_old,'original ternary depth and cofactor')
            if e in (0,1) and a<=cutoff:
                expected=reference_old[a][1] if e==0 else reference_first[a][1]%a
                require(r%a==expected,'present shallow cofactor phase is literally retained')

    # Probes below are only literal numerical residue classes. The signature
    # count does not consult support masks, pattern digits, or valuation cells.
    probes=[];group_bits={};bad_bits=0
    def add_group(name,labels,e):
        nonlocal bad_bits
        bits=0
        for m,r in labels:
            a=m//(3**e)
            index=len(probes);bit=1<<index
            probes.append((a,r%a));bits|=bit
            if name in ('actual_0','actual_1') and a in changed[e]:bad_bits|=bit
        group_bits[name]=bits
    add_group('reference_old',list(reference_old.values()),0)
    add_group('reference_first',list(reference_first.values()),1)
    for e in range(H+1):add_group(f'actual_{e}',target[e],e)
    axes=[];axis_counts=[]
    for p,height in zip(primes,heights):
        requirements=[]
        for a,r in probes:
            power=1;remaining=a
            while remaining%p==0:
                power*=p;remaining//=p
            requirements.append((power,r%power))
        frequencies=Counter();representatives={}
        for leaf in range(p**height):
            bits=0
            for i,(power,residue) in enumerate(requirements):
                if leaf%power==residue:bits|=1<<i
            frequencies[bits]+=1
            representatives.setdefault(bits,leaf)
        axis=[(bits,count,representatives[bits]) for bits,count in frequencies.items()]
        axes.append(axis);axis_counts.append(len(axis))
    all_bits=(1<<len(probes))-1
    late_scale=sum(3**(H-e) for e in range(2,H+1));load_scale=3**(H-1)
    totals=Counter();psi_sum=0;good_max=-1;good_max_word=None;g_increases=0
    histogram=Counter()
    for cell in product(*axes):
        active=all_bits;mass=1
        for bits,count,_ in cell:active&=bits;mass*=count
        totals['complete_period']+=mass
        if not active&group_bits['actual_0']:totals['actual_survivors']+=mass
        if active&group_bits['reference_old']:continue
        totals['reference_survivors']+=mass
        g_ref=(active&group_bits['reference_first']).bit_count()
        g_actual=(active&group_bits['actual_1']).bit_count()
        late=sum(3**(H-e)*(active&group_bits[f'actual_{e}']).bit_count() for e in range(2,H+1))
        psi_num=late_scale*(g_ref+int(g_ref>0))+late
        psi_sum+=mass*psi_num
        if 25*psi_num>74*late_scale:continue
        totals['reference_good']+=mass
        if g_actual>g_ref:g_increases+=mass
        if active&bad_bits:
            totals['reference_good_lost_to_changed_actual_classes']+=mass
            continue
        totals['actual_good']+=mass
        require(not active&group_bits['actual_0'],'selected set avoids every actual old class')
        require(g_actual<=g_ref,'actual first-layer count is dominated on selected set')
        load_num=load_scale*g_actual+late
        require(25*load_num<=37*load_scale,'pointwise actual margin on the entire selected set')
        histogram[load_num]+=mass
        if load_num>good_max:
            good_max=load_num;good_max_word=tuple(row[2] for row in cell)
    require(totals['complete_period']==Q,'full original core Haar counting')
    Epsi=F(psi_sum,late_scale*totals['reference_survivors'])
    require(Epsi<=certificate['reference_selector_upper'],'fixture consumes the reference same-law selector')
    require(F(totals['reference_good'],Q)>=certificate['reference_good_haar_lower'],'reference good-set mass')
    require(F(totals['actual_good'],Q)>F(1,100),'actual good-set density cap')
    W={e:sum((F(1,a) for a in changed[e]),F(0)) for e in (0,1)}
    lost=F(totals['reference_good_lost_to_changed_actual_classes'],Q)
    require(lost<=W[0]+W[1],'one-sided actual new-cylinder loss')
    require(all(W[e]<=certificate['complete_one_layer_reciprocal_tail'] for e in (0,1)),'finite changes fit complete tails')
    require(g_increases>0,'changed first phases increase the raw count on some reference good points')
    require(good_max_word is not None,'literal selected witness exists')
    _,witness=crt([(p**h,leaf) for p,h,leaf in zip(primes,heights,good_max_word)])
    require(not any(witness%m==r for m,r in target[0]),'witness literal old avoidance')
    direct_load=sum((F(1,3**(e-1))*sum(witness%(m//3**e)==r%(m//3**e) for m,r in target[e])
                     for e in range(1,H+1)),F(0))
    require(direct_load==F(good_max,load_scale),'literal numerical witness completion equals cell count')
    return dict(core_heights=heights,ternary_height=H,core_period=Q,
                reference_is_auxiliary='Uniform on complete patterned reference survivors, not actual perturbed survivors.',
                actual_originals={e:target[e] for e in range(H+1)},
                missing_shallow_original_moduli=[5,21],changed_old_cofactors=sorted(changed[0]),
                changed_first_layer_cofactors=sorted(changed[1]),changed_reciprocal_weights=W,
                original_count=len(actual),axis_signature_counts=axis_counts,signature_cells=prod(axis_counts),
                counts=dict(totals),reference_Epsi=Epsi,
                actual_good_haar_mass=F(totals['actual_good'],Q),actual_good_mass_lower_from_measured_reference=F(totals['reference_good'],Q)-W[0]-W[1],
                actual_first_load_increases_on_reference_good_mass=F(g_increases,Q),
                actual_good_max_load=F(good_max,load_scale),maximum_load_witness=witness,
                changed_actual_union_loss_on_reference_good=lost,
                boundary='The literal count verifies one perturbed original family. Arbitrary phases and heights are supplied only by the directed union bound and report456 reference theorem.')


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [encode(v) for v in value]
    return value


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--reference',type=Path,default=Path(__file__).with_name('fixed_early_phase_core_margin.json'))
    parser.add_argument('--pattern-source',type=Path,default=Path(__file__).with_name('k5_three_color_ap_control.py'))
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    reference=json.loads(args.reference.read_text())
    certificate=constants(reference)
    source=load_patterns(args.pattern_source)
    require(tuple(source.PRIMES)==certificate['primes'],'pattern and reference prime inventories agree')
    certificate['literal_control']=literal_control(source,certificate)
    payload=json.dumps(encode(certificate),indent=2)+'\n'
    if args.output is None:print(payload,end='')
    else:
        args.output.write_text(payload)
        control=certificate['literal_control']
        print(json.dumps(encode(dict(fixed_cofactor_count=certificate['fixed_cofactor_count'],
              complete_one_layer_reciprocal_tail=certificate['complete_one_layer_reciprocal_tail'],
              final_good_haar_lower=certificate['final_good_haar_lower'],tail_interface=certificate['tail_interface'],
              original_count=control['original_count'],signature_cells=control['signature_cells'],
              changed_layer_counts=[len(control['changed_old_cofactors']),len(control['changed_first_layer_cofactors'])],
              counts=control['counts'],actual_good_max_load=control['actual_good_max_load'],
              actual_first_load_increases_on_reference_good_mass=control['actual_first_load_increases_on_reference_good_mass'])),indent=2))

if __name__=='__main__':
    main()
