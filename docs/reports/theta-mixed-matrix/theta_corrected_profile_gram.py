"""Direct common-source corrected Gram with a centered zero control."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

import flint
from flint import acb,arb,ctx,fmpq

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('shared_basis',HERE/'theta_shared_witness_gram.py')
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
p,m=s.p,s.m

def produce(profiles_path,basis_path,precision=192):
    if precision<128:
        raise ValueError('At least 128-bit precision required')
    ctx.prec=precision
    profiles=s.read_profiles(profiles_path,precision)
    basis=json.loads(basis_path.read_text())
    if basis['profile_rows_sha256']!=hashlib.sha256(profiles_path.read_bytes()).hexdigest():
        raise ValueError('Witness and profile rows must have the same source')
    if basis['runtime']['precision_bits']!=precision or basis['radial_boxes']!=profiles['radial_boxes']:
        raise ValueError('Same declared precision and complete common witness grid required')
    if basis['producer_sha256']!=hashlib.sha256((HERE/'theta_shared_witness_gram.py').read_bytes()).hexdigest():
        raise ValueError('Current shared witness source contract required')
    critical=s.CriticalAction(basis['critical_denominator'])
    dual=s.dual_action(basis['dual_denominator'],basis['zero_index'])
    actions=[p.ProfileAction(c) for c in profiles['centers_exact']]
    scales=[arb(fmpq(w)).sqrt() for w in profiles['cell_widths_exact']]
    coefficients=[[fmpq(int(a),int(b)) for a,b in row] for row in basis['primal_dual_coefficients_exact']]
    count=len(actions)
    if len(coefficients)!=count or len(basis['fresh_witness_rows'])!=profiles['radial_boxes']:
        raise ValueError('One shared correction and complete witness rows per profile required')
    scenarios={'centered_zero':[[fmpq(0),fmpq(0)] for _ in actions],'centered_corrected':coefficients}
    radius=fmpq(profiles['spatial_radius_exact']);boxes=profiles['radial_boxes']
    decode=s.decode
    tail=s.tail

    def centered_source(i,r,ab,c):
        return scales[i]*actions[i].source(acb(r),1)-arb(ab[0])*critical.source(acb(r))-c

    mass=4*critical.constants[0]*tail(2,radius)
    A_lower=4*arb.pi()**2-6*arb.pi();assert A_lower>0
    critical_source_tail=(8*critical.constants[0]/basis['critical_denominator']**2
                          *((critical.constants[1]/A_lower)**2*tail(6,radius)+tail(2,radius)/16))
    profile_source_tail=[2*(-5*arb(action.center)).exp()*m.bounds.exponential_integral_upper(
        2,arb.pi()*(-2*arb(action.center)).exp(),(2*arb(radius)).exp()) for action in actions]
    constants={};l1={};exterior={};grams={};records={}
    for name,ab_list in scenarios.items():
        constants[name]=[(scales[i]*actions[i].source(acb(0))-arb(ab[0])*critical.source(acb(0))).real.mid()
                         for i,ab in enumerate(ab_list)]
        l1[name]=[arb(0) for _ in actions]
        for j in range(boxes):
            lo,hi=radius*j/boxes,radius*(j+1)/boxes
            r=arb((lo+hi)/2,arb((hi-lo)/2).upper())
            phi,_=actions[0].weighted_source(acb(r),1)
            for i,ab in enumerate(ab_list):
                f=centered_source(i,r,ab,constants[name][i])
                l1[name][i]+=4*arb(hi-lo)*abs(phi*f).upper()*(r/2).cosh().upper()
        for i,ab in enumerate(ab_list):
            start=(2*arb(radius)).exp();pi=arb.pi()
            # Weighted-source tails, including the freely removed constant.
            weighted_tail=(scales[i]*actions[i].weighted_tail(start)
                           +abs(arb(ab[0]))*(critical.constants[1]*tail(4,radius)
                                            +critical.constants[0]*tail(2,radius)/4)/basis['critical_denominator']
                           +abs(constants[name][i])*critical.constants[0]*tail(2,radius))
            l1[name][i]=(l1[name][i]+4*weighted_tail).upper()
        exterior[name]=[(3*(scales[i]**2*profile_source_tail[i]
                             +arb(ab[0])**2*critical_source_tail+constants[name][i]**2*mass)
                         +l1[name][i]**2*mass+2*arb(ab[1])**2*mass/basis['dual_denominator']**2).upper()
                        for i,ab in enumerate(ab_list)]
        grams[name]=[[arb(0) for _ in actions] for _ in actions];records[name]=[]

    for j,(cell,witness) in enumerate(zip(profiles['cells'],basis['fresh_witness_rows'])):
        midpoint=radius*fmpq(2*j+1,2*boxes);half=radius/(2*boxes)
        assert cell['index']==witness['index']==j
        assert fmpq(cell['midpoint_exact'])==fmpq(witness['midpoint_exact'])==midpoint
        r=arb(midpoint,arb(half).upper())
        critical_point=decode(witness['B_critical_point']);dual_point=dual.witness(acb(midpoint)).real
        density=decode(cell['folded_density']);gap=decode(cell['support_gap_lower']).lower()
        assert gap>0;coth=gap.cosh()/gap.sinh()
        critical_derivative=critical.source_derivative(r)
        dual_derivative=dual.witness_derivative(r)
        for name,ab_list in scenarios.items():
            residuals=[];columns=[]
            for i,ab in enumerate(ab_list):
                point=(scales[i]*decode(cell['columns'][i]['B_source'])
                       -arb(ab[0])*critical_point-arb(ab[1])*dual_point)
                f=centered_source(i,r,ab,constants[name][i])
                derivative=scales[i]*actions[i].source_derivative(r)-arb(ab[0])*critical_derivative
                lipschitz=(abs(derivative).upper()+coth*(abs(f).upper()+l1[name][i]))/2
                lipschitz+=abs(arb(ab[1]))*abs(dual_derivative).upper()
                residual=point+arb(0,(arb(half)*lipschitz).upper());assert residual.is_finite()
                residuals.append(residual)
                columns.append({'point_residual':m.endpoints(point),'whole_cell_residual':m.endpoints(residual),
                                'lipschitz_upper':m.endpoints(lipschitz.upper())})
            for i in range(count):
                for k in range(i,count):
                    grams[name][i][k]+=arb(radius/boxes)*density*residuals[i]*residuals[k]
                    grams[name][k][i]=grams[name][i][k]
            records[name].append({'index':j,'midpoint_exact':str(midpoint),'columns':columns})
    results={}
    for name,gram in grams.items():
        centers,inflation,tau,upper,pivots=s.upper_gram(gram,exterior[name])
        norm=s.norm_upper(upper)
        results[name]={'coefficients_exact':[[[str(v.p),str(v.q)] for v in row] for row in scenarios[name]],
                       'removed_transport_constants':list(map(m.endpoints,constants[name])),
                       'source_l1_upper':list(map(m.endpoints,l1[name])),
                       'exterior_column_squared_upper':list(map(m.endpoints,exterior[name])),
                       'interior_cross_gram':[[m.endpoints(v) for v in row] for row in gram],
                       'interior_center_matrix':[[m.endpoints(v) for v in row] for row in centers],
                       'row_inflation':list(map(m.endpoints,inflation)),
                       'exterior_gram_norm_upper':m.endpoints(tau),
                       'positive_ldl_pivots':list(map(m.endpoints,pivots)),
                       'positive_upper_gram':[[m.endpoints(v) for v in row] for row in upper],
                       'gram_norm_upper':m.endpoints(norm),'cells':records[name]}
    result={'scope':'Conditional directed corrected Gram and same-method zero-witness control under actual-model, numerical-supplier and certified-input-row premises; no new action grid, complete growing family, signs, Lean, RH or Robin certificate',
            'runtime':{'python':sys.version.split()[0],'python_flint':flint.__version__,'precision_bits':ctx.prec},'radial_boxes':boxes,
            'centers_exact':profiles['centers_exact'],'cell_widths_exact':profiles['cell_widths_exact'],
            'spatial_radius_exact':str(radius),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'shared_factory_sha256':hashlib.sha256((HERE/'theta_shared_witness_gram.py').read_bytes()).hexdigest(),'scenarios':results,
            'profile_rows_sha256':hashlib.sha256(profiles_path.read_bytes()).hexdigest(),
            'witness_rows_sha256':hashlib.sha256(basis_path.read_bytes()).hexdigest(),
            'new_metric_action_callbacks':0,'old_quadratic_rows_or_grid_producers_used':False}

    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profiles',type=Path,required=True)
    parser.add_argument('--basis',type=Path,required=True)
    parser.add_argument('--precision',type=int,default=192)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=produce(args.profiles,args.basis,args.precision)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({name:v['gram_norm_upper'] for name,v in result['scenarios'].items()},indent=2))


if __name__=='__main__':
    main()
