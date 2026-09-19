#!/usr/bin/env python3
"""Complete original-label tail budgets for entry to the aligned guard.

This calculator does not enumerate a CRT source or compute its qJ/rho.
Its conditional finite-data thresholds retain every omitted tail.
"""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from decimal import Decimal, localcontext
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
DEFAULT_CUTS = ((20,20,20),(17,10,8),(34,24,19))
CONSUMER = 'certificates/source_norms/j-source/j_aligned_explicit_parameter_neighborhood.json'
DEFAULT_PROOF = 'profile-notes/j-source/326-finite-original-label-tests-preserve-the-explicit-aligned-source-guard.md'
DEFAULT_CERTIFICATE = 'certificates/source_norms/j-source/j_aligned_source_guard_truncation.json'
ANCHORS = (
    'profile-notes/46-one-forbidden-carrier-mixture-strengthens-survival.md',
    'profile-notes/48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md',
    'profile-notes/71-global-j-k-control-faces-and-exact-escape-gaps.md',
    'profile-notes/301-three-missing-source-pairs-clear-the-complete-core-comparisons.md',
    'profile-notes/j-source/302-a-positive-actual-source-neighborhood-keeps-j-below403.md',
    'profile-notes/305-ineffective-leading-pairs-retain-the-complete-core-bounds.md',
    'profile-notes/j-source/311-imperfect-j-source-alignment-forces-a-sharp-sector-surplus.md',
    'profile-notes/j-source/325-an-explicit-aligned-parameter-neighborhood-keeps-the-complete-comparison-below400.md',
    'frontier/j-source/j_aligned_explicit_parameter_neighborhood.py',
)


def require(value, message):
    if not value:
        raise ValueError(message)


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):
        return [encode(v) for v in value]
    return value


def product(values):
    out=F(1)
    for value in values:
        out*=value
    return out


def cut_bounds(A,B,C,eta,rstar):
    require(all(type(v) is int for v in(A,B,C)) and A>=4 and B>=1 and C>=1,
            'Original3/9,45/135/405 and positive-seven labels retained')
    t3,t5,t7=F(1,2*3**A),F(1,4*5**B),F(1,6*7**C)
    v7=F(1,7**C)
    T35=F(15,8)*(1-(1-F(1,3**(A+1)))*(1-F(1,5**(B+1))))
    T357=F(35,16)*(1-product(1-F(1,p**(n+1)) for p,n in((3,A),(5,B),(7,C))))
    Tlate=F(1,72)*(1-(1-F(1,3**(A-2)))*(1-F(1,5**B)))
    Tearly=t3+F(13,9)*t5
    # Independent one-coordinate finite sums check the whole-complement
    # formulas. These are geometric identities, not residue enumeration.
    head={p:sum((F(1,p**j) for j in range(n+1)),F(0)) for p,n in((3,A),(5,B),(7,C))}
    require(T35==F(15,8)-head[3]*head[5]
            and T357==F(35,16)-product(head.values()),
            'Complete old35 and357 union tails')
    require(Tlate==F(1,72)-sum((F(1,3**j) for j in range(3,A+1)),F(0))*(head[5]-1)
            and T35==Tearly+Tlate and v7==6*t7,
            'Original early/late label partition and entire carrier tail')
    qdown=28*t5+72*Tearly
    qup=12*t5+72*Tlate+18*t3+v7
    require(qdown==F(36,3**A)+F(33,5**B), 'Exact directed qJ loss')
    T2err=t5/30+3*t3/20
    rhoup=T35+v7/3
    rhodown=F(6,5)*T357+T2err
    qmax=(1-F(1,3**(A-2)))**2*(1-F(1,5**B))**4*(1-v7)
    require(min(t3,t5,t7,T35,T357,Tlate,Tearly,qdown,qup,T2err,rhoup,rhodown)>0
            and 0<qmax<1, 'Positive complete tails and finite missing-budget cap')
    half_forward=qdown<=eta/2 and rhoup<=eta/2
    half_backward=qup<=eta/2 and rhodown<=eta/2
    if (A,B,C) in DEFAULT_CUTS[:2]:
        require(1-qmax>eta, 'Each old core cannot itself satisfy the325 qJ guard')
    if (A,B,C)==DEFAULT_CUTS[2]:
        outward=(F('2.713e-15'),F('1.235e-15'),F('7.302e-17'),F('9.882e-17'))
        require(all(v<u<eta/2 for v,u in zip((qdown,qup,rhoup,rhodown),outward)),
                'All four strict rational half-buffer enclosures in the proof')
        require(half_forward and half_backward and 1-qmax<eta/2,
                'Both buffered implications and no missing-budget obstruction to the scalar half-guard')
    return {
        'cut':{'3':A,'5':B,'7':C},
        'all_omitted_tails':{'pure3':t3,'pure5':t5,'pure7':t7,'old35':T35,
            'complete357':T357,'late35':Tlate,'early35':Tearly,'carrier_weight':v7},
        'complete_measure_errors':{
            'pure3_variation':t3,'raw35_variation':T35,
            'normalized357_full_variation':F(6,5)*(T357+t7),
            'survivor_mass_full_minus_core_lower':-F(6,5)*T357,
            'survivor_mass_upper_coefficient_of_core_S':v7/5,
            'carrier_l1':2*v7},
        'stage_errors':{
            'pure5_z_monotone_drop':t5,'each_d_section_monotone_drop':3*t5,
            'alpha1_change_lower':-t5,'alpha1_change_upper':t5,
            'root1_beta_width_sum_change_lower':-6*t5,
            'root1_beta_width_sum_change_upper':t5,
            'root1_late_raw_change_lower':-Tearly,'root1_late_raw_change_upper':Tlate,
            'qJ_deficit_carrier_factor_monotone_gain':18*t3+v7},
        'qJ_full_minus_core':{'lower':-qdown,'upper':qup},
        'carrier_mass_S0_errors':{
            'T2_monotone_drop':T2err,
            'S0_full_minus_core_lower_constant':-T35,
            'S0_lower_coefficient_of_core_s':-2*v7/5,
            'S0_full_minus_core_upper':T2err},
        'rho_full_minus_core':{
            'lower':-rhodown,'uniform_upper':rhoup,
            'sharper_upper_constant':T35,
            'sharper_upper_coefficient_of_core_S':v7/5,
            'sharper_upper_coefficient_of_core_s':2*v7/5},
        'conditional_finite_data_thresholds':{
            'core_qJ_lower':1-eta+qdown,
            'core_rho_upper':rstar+eta-rhoup,
            'literal_low_labels':[3,9,45,135,405],
            'full_original_source_values_computed':False,
            'condition':'Actual retained source in the same effective9 chart; original45 and135 present and aligned; retained original residues unchanged.'},
        'half_buffer':{
            'core_to_full_sufficient':half_forward,
            'full_to_core_sufficient':half_backward,
            'qJ_lower':1-eta/2,'rho_upper':rstar+eta/2,
            'conditional_only_no_source_membership_asserted':True},
        'finite_missing_budget':{
            'universal_core_qJ_upper':qmax,'universal_core_qJ_deficit_lower':1-qmax,
            'obstructs_325_qJ_guard':1-qmax>eta,
            'obstructs_half_qJ_guard':1-qmax>eta/2},
    }


def calculate(base,proof,cuts,io):
    raw=io.read_artifact_bytes(base/CONSUMER)
    source=json.loads(raw,object_pairs_hook=io._unique)
    require(source['schema']=='erdos7-aligned-explicit-parameter-neighborhood-v1',
            'Existing explicit actual-source parameter neighborhood')
    eta=F(source['source_domain']['epsilon']);rstar=F(source['source_domain']['rho_upper'])-eta
    require(eta==F(1,10**14) and rstar==F(2,675)
            and F(source['source_domain']['qJ_lower'])==1-eta,
            'Unchanged exact325 aligned guard')
    pins={CONSUMER:sha256(raw).hexdigest()}
    for path in ANCHORS:
        pins[path]=sha256(io.read_artifact_bytes(base/path)).hexdigest()
        if path in source['source_sha256']:
            require(pins[path]==source['source_sha256'][path], 'Current325 bound source '+path)
    proof_raw=io.read_artifact_bytes(proof)
    entries=[cut_bounds(*cut,eta,rstar) for cut in cuts]
    return encode({
        'schema':'erdos7-aligned-source-guard-truncation-v1',
        'source_sha256':pins,
        'ordinary_proof':{'sha256':sha256(proof_raw).hexdigest(),'byte_count':len(proof_raw)},
        'producer_sha256':sha256(io.read_artifact_bytes(Path(__file__))).hexdigest(),
        'full_variation_convention':'Full signed variation, without factor1/2.',
        'target_guard':{'epsilon':eta,'qJ_lower':1-eta,'rho_floor':rstar,'rho_upper':rstar+eta},
        'cuts':entries,
        'scope':'Complete geometric tail and buffered finite-data guard formulas for the existing325 J comparison. Does not enumerate original CRT residues, compute a source qJ/rho, assert source realization, alter a consumer, reuse old core errors on a new law, prove a global source join or continue arbitrary later primes.'
    })


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--proof',type=Path,help='Override the proof; default is --base/'+DEFAULT_PROOF)
    parser.add_argument('--certificate',type=Path,help='Override the certificate; default is --base/'+DEFAULT_CERTIFICATE)
    parser.add_argument('--cut',type=int,nargs=3,action='append',metavar=('A','B','C'))
    modes=parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write',action='store_true')
    modes.add_argument('--check',action='store_true')
    args=parser.parse_args()
    proof=args.proof if args.proof is not None else args.base/DEFAULT_PROOF
    certificate=args.certificate if args.certificate is not None else args.base/DEFAULT_CERTIFICATE
    cuts=tuple(map(tuple,args.cut)) if args.cut is not None else DEFAULT_CUTS
    require(cuts and len(cuts)==len(set(cuts)), 'Nonempty distinct requested exponent cuts')
    spec=importlib.util.spec_from_file_location('guard_truncation_io',args.base/'certificate_io.py')
    require(spec is not None and spec.loader is not None, 'Canonical certificate IO')
    io=importlib.util.module_from_spec(spec);spec.loader.exec_module(io)
    result=calculate(args.base,proof,cuts,io)
    if args.write:
        io.write_certificate_text(certificate,json.dumps(result,indent=2)+'\n')
    else:
        given=json.loads(io.read_artifact_bytes(certificate),object_pairs_hook=io._unique)
        require(given==result, 'Exact complete tail and source-binding replay')
    with localcontext() as ctx:
        ctx.prec=18
        for entry in result['cuts']:
            values=[-F(entry['qJ_full_minus_core']['lower']),F(entry['qJ_full_minus_core']['upper']),
                    F(entry['rho_full_minus_core']['uniform_upper']),-F(entry['rho_full_minus_core']['lower'])]
            print('cut',tuple(entry['cut'].values()),'Qdown,Qup,rho_up,rho_down',
                  *(str(Decimal(v.numerator)/Decimal(v.denominator)) for v in values))
    print('PASS complete directed tails; no actual CRT source qJ/rho was computed')


if __name__=='__main__':
    main()
