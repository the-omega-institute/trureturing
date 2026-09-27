#!/usr/bin/env python3
"""Exact aligned parameter neighborhood from the complete source modulus.

Consumes already checked source bounds and dual feasibility. This companion
prices their full banks and zero-column restoration, evaluates complete strip
bounds, and propagates all 18 own-observation errors through all 59 envelopes.
"""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
DEFAULT_BASE = Path(__file__).resolve().parents[2]
CERTIFICATE = Path('certificates/source_norms/j-geometry/j_aligned_explicit_parameter_neighborhood.json')
SOURCE = 'certificates/source_norms/j-geometry/j_aligned_complete_moment_comparison.json'
ROWS = 'certificates/source_norms/j-geometry/j_aligned_source_row_transport.json'
RESTORED = 'certificates/source_norms/j-geometry/j_actual_rows_zero_restoration.json'
DEFINITIONS = 'certificates/source_norms/j-geometry/j_face_heavy_positive175189_complete_moment_cost_comparison.json'
ANCHORS = (
    'profile-notes/321-384/323-actual-aligned-source-and-row-transport.md',
    'profile-notes/321-384/324-complete-aligned-source-prefixes-and-tails-have-an-explicit-modulus.md',
    'profile-notes/257-320/311-imperfect-j-source-alignment-forces-a-sharp-sector-surplus.md',
    'profile-notes/257-320/312-an-aligned-j-source-has-a-complete-own-test-and-residual-deletion-interface.md',
    'profile-notes/257-320/317-the-complete-actual-aligned-j-comparison-crosses403.md',
    'frontier/j-geometry/j_aligned_source_row_transport.py',
    'frontier/j-geometry/j_aligned_retained375_heads.py',
    'frontier/j-geometry/j_aligned_quadratic_complete_heads.py',
    'frontier/j-geometry/j_explicit_actual_neighborhood.py',
    'frontier/retained-transport/retained135_heavy_comparison.py',
)


def require(value, message):
    if not value:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Readable provider '+str(path))
    out = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(out)
    return out


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def ceiling(value):
    return -(-value.numerator // value.denominator)


def definitions(source, old):
    used = {r['name'] for r in source['basis']}
    rows = {r['name']: r for r in old['basis']}
    quadratic = {
        'square': (F(1), {1:F(3)}, F(2), 2),
        'factorial2': (F(0), {}, F(1), 2),
        'factorial3': (F(0), {}, F(1), 3),
        'factorial5': (F(0), {}, F(1), 5),
        'cost48': (F(0), {3:F(5)}, F(2), 3),
        'cost49': (F(0), {2:F(31,16),3:F(17,16)}, F(2), 2),
    }
    out = {}
    for name in sorted(used):
        row = rows[name]
        low = list(map(F,row['low_load_values']))
        poly = tuple(map(F,row['tail_polynomial']))
        require(len(low)==8 and len(poly)==3, 'Whole original function '+name)
        if name in quadratic:
            a, co, f, k = quadratic[name]
        else:
            require(poly[2]==0, 'All other active functions have affine tails')
            vals = low+[poly[0]+9*poly[1]]
            a, f, k = vals[0], F(0), 1
            co = {1:vals[1]-vals[0]}
            co.update({i:vals[i]-2*vals[i-1]+vals[i-2] for i in range(2,9)})
            co = {i:v for i,v in co.items() if v}
        A = sum(co.values(),F(0))
        require(min(a,f,A)>=0 and all(v>=0 for v in co.values()),
                'Nonnegative exact expansion '+name)
        value = lambda n:a+sum(v*max(n-i,0) for i,v in co.items())+f*max(n-k,0)*max(n-k+1,0)/2
        require([value(n) for n in range(1,9)]==low, 'All original low values '+name)
        require((a-sum(i*v for i,v in co.items())+f*k*(k-1)/2,
                 A+f*F(1-2*k,2),f/2)==poly, 'Entire original polynomial tail '+name)
        require(a+64*A+80*f<=3300 and A+6*f<=51 and f/2<=1,
                'Complete 324 source modulus coefficients '+name)
        # The constant a*S is outside physical coordinates. All retained
        # state functions are increasing, so each physical increment is no
        # larger than the whole function at load14. Raw seven kernels are
        # <=1 for hinges and have factorial slope <=14. Restored E3/E5
        # coordinates have coefficient zero; theta is not discarded.
        survivor_cap = 14*A+91*f
        raw_cap = A+14*f
        require(max(survivor_cap,raw_cap)<706, 'Every physical coefficient below706 '+name)
        out[name] = {'constant':a,'hinges':co,'hinge_slope':A,
                     'factorial_weight':f,'factorial_threshold':k,
                     'physical_survivor_coefficient_bound':survivor_cap,
                     'physical_raw_coefficient_bound':raw_cap}
    require(len(out)==18 and max(r['hinge_slope'] for r in out.values())==F(403,8),
            'All and only18 source functions; heavy slope unchanged')
    return out


def inventory(base, source, rows, read, pins):
    prior = module('aligned_parameter_price_api', base/'frontier/j-geometry/j_explicit_actual_neighborhood.py')
    codec = module('aligned_parameter_dual_codec', base/'frontier/retained-transport/retained135_heavy_comparison.py')
    paths = sorted(p for p in source['source_sha256']
                   if p.startswith('certificates/source_norms/j-geometry/j_aligned_'))
    records, classified = [], []
    small = read('certificates/source_norms/j-geometry/j_aligned_joint_selected_heads.json')['model']
    supported = {
        (small['variables'],small['inequalities'],small['equalities']):small['rows_sha256'],
        **{tuple(v[k] for k in ('variables','inequalities','equalities')):v['rows_sha256']
           for k,v in rows['consumed_models'].items() if k in ('315','316')},
    }
    for path in paths:
        value = read(path)
        require(pins[path]==source['source_sha256'][path], 'Current317 source pin '+path)
        locations = list(prior.record_paths(value))
        if not locations:
            classified.append({'source':path,'classification':'no-source-duals','dual_count':0})
            continue
        model = value.get('model')
        if model is None:
            require(value.get('model_sha256')==small['rows_sha256'], 'Aligned remaining hinges use313 source')
            model = small
        dims = tuple(model[k] for k in ('variables','inequalities','equalities'))
        require(dims in supported and model['rows_sha256']==supported[dims],
                'Only323-supported actual aligned source matrices')
        if 'encoded_rational_duals' in value:
            require(locations==[('encoded',('encoded_rational_duals',))],
                    'No skipped nested encoded source bank')
            bank = codec.decode_dual_bank(value['encoded_rational_duals'],
                    inequality_count=dims[1],equality_count=dims[2])
            field = 'encoded_rational_duals'
        else:
            require('rational_duals' in value and all(kind=='record' and len(loc)==2
                    and loc[0]=='rational_duals' for kind,loc in locations),
                    'All original uncompressed source records retained')
            bank = value['rational_duals']
            require(len(bank)==len(locations), 'No omitted source record')
            field = 'rational_duals'
        declared = value.get('distinct_dual_count',value.get('distinct_duals'))
        require(len(bank)==declared, 'Every declared adopted dual priced')
        priced = prior.price(bank,dims[1],dims[2])
        priced.update(source=path,sha256=pins[path],bank_field=field,
                      dimensions=list(dims),rows_sha256=model['rows_sha256'])
        records.append(priced)
        classified.append({'source':path,'classification':field,'dual_count':len(bank)})
        print('Priced',path,len(bank),'duals',flush=True)
    total = sum(r['dual_count'] for r in records)
    maximum = max(F(r['maximum_L1']) for r in records)
    require(len(paths)==8 and len(records)==5 and total==2883 and ceiling(maximum)==84526,
            'Complete aligned313--316 inventory: five banks and2883 adopted duals')
    return {'source_certificate_count':len(paths),'priced_bank_count':len(records),
            'priced_dual_count':total,'source_classification':classified,
            'maximum_L1':maximum,'ceiling_maximum_L1':ceiling(maximum),
            'source_banks':records,
            'scope':'Full adopted bank prices only; pinned endpoint dual feasibility is consumed, not replayed.'}


def restore(rows, original):
    require(rows['consumed_zero_restoration']=={
        'zero_columns':4634,'zero_rows':2645,'maximum_column_bound':'17','sum_column_bounds':'56866/5'},
        'The published323 zero-restoration theorem')
    pairs = []
    for batch in original['column_bound_batches']:
        require(batch['start']==len(pairs), 'Complete original restored-column order')
        pairs.extend(batch['rows'])
        require(batch['stop']==len(pairs), 'Complete original restored-column batch')
    bounds = {int(c):F(v) for c,v in pairs}
    require(len(pairs)==len(bounds)==4634 and min(bounds.values())>0
            and sum(bounds.values())==F(56866,5) and max(bounds.values())==17,
            'All original nonzero restoration coefficients')
    physical = set()
    for cell in range(25):
        for mask in range(16):
            col=16*cell+mask
            physical.update((col,425+col))
            for state in range(1,8):
                physical.update((876+400*(state-1)+col,3676+400*(state-1)+col))
            for state in range(8):
                physical.update((6531+400*state+col,9731+400*state+col))
    nonphysical=sorted(set(bounds)-physical)
    require(len(physical)==12800 and len(nonphysical)==26
            and set(nonphysical)<=set(range(825,875)) and 875 not in bounds,
            'Every restored nonphysical column is a zero-objective E3/E5 coordinate; theta retained')
    price = 706*sum(bounds.values())
    require(ceiling(price)==8029480, 'Full706-per-column restoration price')
    return {'column_count':len(bounds),'induction_row_count':2645,
            'sum_column_bounds':sum(bounds.values()),'maximum_column_bound':max(bounds.values()),
            'physical_columns':len(physical),'restored_zero_objective_E3_E5_columns':nonphysical,
            'restored_physical_column_count':len(bounds)-len(nonphysical),'objective_coefficient_bound':706,
            'uniform_restoration_price':price,'ceiling_restoration_price':ceiling(price),
            'scope':'All4634 original column bounds are read and priced; no zero-induction replay.'}


def consumer(source):
    bounds = {r['name']:F(r['upper']) for r in source['basis']}
    targets = {r['name']:{k:F(v) for k,v in r['coefficients'].items()}
               for r in source['results']}
    require(len(bounds)==18 and len(targets)==len(source['results'])==59,
            'Exactly18 independent source observations and59 whole envelopes')
    for row in source['results']:
        vec=targets[row['name']]
        require(set(vec)<=set(bounds) and all(v>=0 for k,v in vec.items() if k!='mass'),
                'Only mass may have negative envelope coefficients')
        require(sum(v*bounds[k] for k,v in vec.items())==F(row['upper']),
                'Complete317 envelope upper '+row['name'])
    require(set(bounds)=={k for vec in targets.values() for k,v in vec.items() if v},
            'Every source observation has an actual consumer')
    def linear(*terms):
        ans={k:F(0) for k in bounds}
        for scale,vec in terms:
            for k,v in vec.items():ans[k]+=scale*v
        return ans
    mass={'mass':F(1)}
    alpha=F(source['count_law']['remaining_hinge1_coefficient'])
    beta=F(source['count_law']['whole_constant_coefficient'])
    tail=linear((alpha,targets['mean']),(beta-alpha,mass))
    den=linear((F(1),mass),(-F(1,6),targets['hinge4']),(-F(1,7),tail),
               *((-F(1,7),targets['AP11-'+str(i)]) for i in range(4)))
    weights=list(map(F,source['cost_weights']))
    require(len(weights)==52 and min(weights)>0, 'Every original positive cost weight')
    num=linear((F(source['signed_mass_coefficient']),mass),
               (F(source['complete_square_weight']),targets['square']),
               *((w,targets['cost-'+str(i)]) for i,w in enumerate(weights)))
    offset=F(source['offset'])
    margin=linear((403-offset,den),(-F(1),num))
    evaluate=lambda v:sum(v[k]*bounds[k] for k in bounds)
    E,N,G=map(evaluate,(den,num,margin))
    require((E,N,G)==tuple(F(source['comparison_upper'][k]) for k in
            ('denominator','numerator','target403_numerator_margin')),
            'Same complete317 signed comparison')
    require(min(E,N,G)>0 and offset+N/E==F(source['comparison_upper']['comparison']),
            'Positive endpoint denominator and exact original ratio')
    require(all(den[k]<=0 and num[k]>=0 and margin[k]<=0 for k in bounds if k!='mass'),
            'One-sided nonmass errors preserve every signed direction')
    EL={k:abs(v) for k,v in den.items()}
    NL={k:abs(v) for k,v in num.items()}
    GL={k:abs(v) for k,v in margin.items()}
    return {'source_observations':list(bounds),'basis_bounds':bounds,
            'envelope_coefficients':targets,'denominator_coefficients':den,
            'numerator_coefficients':num,'margin403_coefficients':margin,
            'denominator_error_prices':EL,'numerator_error_prices':NL,'margin403_error_prices':GL,
            'denominator_price_sum':sum(EL.values()),'numerator_price_sum':sum(NL.values()),
            'margin403_price_sum':sum(GL.values()),'endpoint_denominator':E,
            'endpoint_numerator':N,'endpoint_margin403':G,'offset':offset,
            'mass_hypothesis':'abs(S-413/2700)<=r; keep actual signed S until combination'}


def calculate(base,io):
    pins,cache={},{}
    def read(path):
        if path not in cache:
            raw=io.read_artifact_bytes(base/path)
            pins[path]=sha256(raw).hexdigest()
            cache[path]=json.loads(raw,object_pairs_hook=io._unique)
        return cache[path]
    source,rows,original=read(SOURCE),read(ROWS),read(RESTORED)
    require(source['schema']=='erdos7-aligned-complete-moment-comparison-v1'
            and rows['schema']=='erdos7-aligned-source-row-transport-v1',
            'Pinned317 endpoint and323 actual row theorem')
    require(rows['uniform_row_modulus']=={'delta':5,'epsilon_star':30}, 'Same actual row error r')
    for path,digest in rows['source_sha256'].items():
        read(path)
        require(pins[path]==digest, 'Current323 consumed theorem input '+path)
    shape=definitions(source,read(DEFINITIONS))
    price=inventory(base,source,rows,read,pins)
    restoration=restore(rows,original)
    signed=consumer(source)
    t=F(1,10**13)
    r=30*t
    require(t<=F(rows['domain']['delta_max']) and t<=F(rows['domain']['epsilon_star_max']),
            'Entire t triangle satisfies actual-source domain guards')
    L=A=B=30
    B1=(L*L-1)*r+F(15,8)*(F(1,3**L)+F(1,5**L))
    B2=r*(A+1)**2*(B+1)**2+F(15*(A+2),8*3**A)+F(3*(4*B+7),8*5**B)
    D,R=price['ceiling_maximum_L1'],restoration['ceiling_restoration_price']
    omega=(D+R+3300)*r+51*B1+B2
    require(omega<F(1,10000), 'Complete uniform18-observation error below1e-4')
    errors={name:(r if name=='mass' else omega) for name in signed['source_observations']}
    loss=lambda prices:sum(prices[name]*errors[name] for name in errors)
    E=signed['endpoint_denominator']-loss(signed['denominator_error_prices'])
    N=signed['endpoint_numerator']+loss(signed['numerator_error_prices'])
    G=signed['endpoint_margin403']-loss(signed['margin403_error_prices'])
    require(min(E,N,G)>0, 'Positive denominator, numerator and signed403 margin')
    J=signed['offset']+N/E
    outward=F(ceiling(J*10**9),10**9)
    require(J<=outward<F(399927,1000)<400<403, 'Outward rational whole-comparison upper')
    outward_E=F((E*10**10).numerator//(E*10**10).denominator,10**10)
    require(F(877902567,10**10)<=outward_E<E, 'Outward rational positive denominator lower')
    epsN=F(1,10**14)
    eps_star_box=F(43,36)*epsN
    t_box=epsN+eps_star_box
    require(t_box==F(79,36)*epsN<t,
            'Actual qJ/rho rectangle implies the entire proved t triangle')
    # The implication uses epsilon_*=S-D-2g_delta/5>=0 and
    # epsilon_*<=rho-2/675+7delta/36, already proved in312.
    box={'epsilon':epsN,'qJ_lower':1-epsN,'rho_upper':F(2,675)+epsN,
         'epsilon_star_upper':eps_star_box,'delta_plus_epsilon_star_upper':t_box,
         'aligned_guard':'Original45 and135 occupy the same surviving root1 mod9 cell; actual effective9 source'}
    for path in ANCHORS:
        pins[path]=sha256(io.read_artifact_bytes(base/path)).hexdigest()
    return encode({'schema':'erdos7-aligned-explicit-parameter-neighborhood-v1',
        'source_sha256':pins,'source_domain':box,'delta_plus_epsilon_star_maximum':t,
        'uniform_row_error_maximum':r,'source_function_expansions':shape,
        'adopted_dual_price_inventory':price,'restored_column_price':restoration,
        'complete_strip_bound':{'B1_box_L':L,'B2_box_A':A,'B2_box_B':B,
            'B1_upper':B1,'B2_upper':B2,'omitted_geometric_strips_included':True},
        'modulus_coefficients':{'D':D,'R':R,'linear_overhead':3300,'B1':51,'B2':1},
        'uniform_observation_error':omega,'source_observation_errors':errors,'signed_consumer':signed,
        'nearby_denominator_lower':E,'nearby_numerator_upper':N,'nearby_margin403_lower':G,
        'nearby_comparison_upper':J,'outward_comparison_upper':outward,
        'outward_denominator_lower':outward_E,
        'source_observation_count':18,'original_envelope_count':59,'original_cost_count':52,
        'scope':'Explicit actual aligned qJ/rho parameter neighborhood from ordinary323/324 source lemmas. All independent own loads, adopted duals, restored physical columns, assigned exponent tails and signed mass are paid. This is not a full-source TV hypothesis, global source join, unrestricted later-prime continuation, Lean proof or unrestricted Erdős7 result.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=DEFAULT_BASE)
    parser.add_argument('--certificate',type=Path)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    base=args.base.resolve()
    io=module('aligned_parameter_io',base/'certificate_io.py')
    result=calculate(base,io)
    path=args.certificate or base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        given=json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique)
        require(result==given,'Every explicit parameter neighborhood certificate field reconstructs')
    print('PASS aligned parameter neighborhood; duals',
          result['adopted_dual_price_inventory']['priced_dual_count'],
          'omega',float(F(result['uniform_observation_error'])),
          'J <=',result['outward_comparison_upper'],flush=True)


if __name__=='__main__':
    main()
