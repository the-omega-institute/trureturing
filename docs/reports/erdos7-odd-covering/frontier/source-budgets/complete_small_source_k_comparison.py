#!/usr/bin/env python3
"""Assemble all52 original costs and the complete AP denominator below403.

The conclusion is restricted to the certified positive K-source box. All
independent labels, signed actual mass, exponent tails and count tails remain.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/complete_small_source_k_comparison.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765', 'certificates/source_norms/retained-transport/complete_small_retained_heads.json': '0003323c4898d5255c9c3abf204b6b321eaf781770dbf0911df021ae3b0a2777', 'certificates/source_norms/retained-transport/legacy_retained_complete_head_transport.json': '4671c87e2938eb6e4429b5ce8c71ee60f646a2b3f4e3a6feffd67d59777b3c40', 'certificates/source_norms/retained-transport/small_source_square_factorial_transport.json': '3194d3489f042e3c180b8d0e62c3aa79b2d0f5ee2f7208cbb64a7ddec3edf9f6', 'certificates/source_norms/comparison-bounds/uniform_complete_k_comparison.json': '0df6d4d58c94097993ac4f424d6c11a4be3197f483f5a61ad6bf840abf2af4ad', 'certificates/source_norms/moments-survival/uniform_ap_survival_denominator.json': '080ecc953d56c722d9026fcc8517fa08dbd67ae7381a5af581c3afc20d48db3a', 'certificates/source_norms/comparison-bounds/load_two_cost_remainders.json': 'f4224aa378cf67701c4d67bc6e7781277163ad429970727013673aa4e3b2a9e3', 'certificates/source_norms/endpoint-bounds/k_neighborhood_radius_1_50.json': '72de469bb9a4aec09c8135626bb6a9897bff4f98f42878a0d803e90cae03e2d7', 'certificates/source_norms/source-budgets/carrier_mass_residual_bound.json': '5ec6d2857f0dfe90bce554944fa29d72413e9bb0c359de77b7daf54ca4ceb32b', 'certificates/source_norms/retained-transport/retained135125_survival_comparison.json': '51e1c09c96c819b1fb292762dbc082f293d9ba3f6c22a504959f04ae508ca47e', 'certificates/source_norms/retained-transport/retained135125_heavy_comparison.json': '451537f6ee699920c955ba0401cedba672f0aaabc97ad193cb282163bcfaf6cf', 'certificates/source_norms/retained-transport/retained_deletion_survival_comparison.json': '646acfad14cbb6e3476c7d33a1fb2ce3ba068305dc02fa75635df8c8509fff87', 'certificates/source_norms/moments-survival/whole_quadratic_same_head.json': 'c0f131821927a5aaa8e6e4f1b9fa7ed972ee3c5481e78ff39234f2653a25704f', 'frontier/retained-transport/complete_small_retained_heads.py': 'e559f49dd42b44f4251f826580690d646befd4f9898c933502f725bdb9a49149', 'frontier/retained-transport/legacy_retained_complete_head_transport.py': '5ca020f049128169429d6e99b7bc1b554c27c4d2b2a7dfea537ab2d1a33f37c5', 'frontier/retained-transport/small_source_square_factorial_transport.py': '4462ae0cd22f14a7698b76a109dc3b870ae41b4ebd036687d1e1504b1a4aa2ea', 'frontier/comparison-bounds/uniform_complete_k_comparison.py': '75db40896f9a0fb1d7cd6ee17f6f8b7af5ef4c2bf074811b6df8ca3327809fd3', 'frontier/moments-survival/uniform_ap_survival_denominator.py': '181a1793bd15059074d2998eb820322a3b9c2158bac5edfcb3bc057b7e78f180', 'frontier/comparison-bounds/load_two_cost_remainders.py': '4bb1f09f0768f92b9dc447156ad0c816e1858c7a1e553c2b422ebe878d7d0ec2', 'frontier/source-budgets/source_barrier_saturation.py': '6fe57e39274df1fa4a80ae4d4a22cab7b1d78d28c4f428b789071e3fb7776a64', 'frontier/source-budgets/carrier_mass_residual_bound.py': 'b455566fe256dac370d3afb97c6e357d2c75296a2e36f483e6f189fda436141c', 'frontier/endpoint-bounds/k_neighborhood_radius_study.py': 'f5b6d2df57ee047a3d47660812e8fc3ff0a81239db15881634b4ad0b01633b0f', 'profile-notes/065-128/106-the-actual-denominator-shares-the-carrier-mass-residual.md': '52a160f306181cccd0813e1b46968f7e7678ee910a57f184f583cca777c8a207', 'profile-notes/129-192/146-a-global-mass-floor-and-coupled-costs-expand-the-k-radius.md': 'e5edf49af5c9adaf905b6f78a739b303ca095b2cbddb2b5b560cde042ff52d38', 'profile-notes/193-256/202-eight-original-costs-have-an-exact-load-two-remainder.md': '673cec27e5888d47163e3030210e1bb8e1b91e4298eb95f3208584e60d61af69', 'profile-notes/193-256/235-every-original-head-candidate-transports-on-a-positive-source-box.md': 'bdd7610e78704f98506beb05cc806aa043cf8b6eaefd614589eea2cc0f989640', 'profile-notes/193-256/237-the-sixteen-legacy-heads-transport-with-their-survivor-cap-prices.md': '30b00187f5cb3a6021055b861fc9d443abd9bd470a448cde1f0d3da6a15de0af', 'profile-notes/193-256/238-the-shared-square-and-complete-factorial-bound-extend-to-the-small-source-box.md': '005af5d960151ca814d068c5c82db844f861a5b13bcf23f2747c36e2a325d7b6'}
SOURCES = ('complete_small_retained_heads', 'legacy_retained_complete_head_transport', 'small_source_square_factorial_transport', 'uniform_complete_k_comparison', 'uniform_ap_survival_denominator', 'load_two_cost_remainders', 'k_neighborhood_radius_1_50', 'carrier_mass_residual_bound', 'retained135125_survival_comparison', 'retained135125_heavy_comparison', 'retained_deletion_survival_comparison', 'whole_quadratic_same_head')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original mathematical input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):
        return [encode(v) for v in value]
    return value


def coefficients(value):
    result = {int(t):F(a) for t,a in value.items() if F(a)}
    require(result and all(1<=t<=8 and a>0 for t,a in result.items()), 'Original positive hinge vector')
    return result


def affine_identity(source, tag, expected):
    """Bind each new head to its exact original function, including all loads."""
    degree,leading,constant,cutoff = source.zero5_cost_metadata(tag)
    f = lambda n:source.zero5_cost(tag,n)
    a = {1:f(2)-f(1)} | {t:f(t+1)-2*f(t)+f(t-1) for t in range(2,9)}
    require(degree==1 and 1<=cutoff<=8 and min(a.values())>=0 and f(1)>=0,
            'Original nonnegative affine-tail representation')
    expansion = lambda n:f(1)+sum(v*max(n-t,0) for t,v in a.items())
    require({t:v for t,v in a.items() if v}==coefficients(expected)
            and all(expansion(n)==f(n) for n in range(1,10))
            and sum(a.values())==leading and f(1)-sum(t*v for t,v in a.items())==constant,
            'Finite transitions and the complete affine continuation bind the same original cost')
    return {'at_one':f(1),'hinge_coefficients':{t:v for t,v in a.items() if v},
            'tail_entrance':cutoff,'tail_slope':leading,'tail_constant':constant}


def count_law(source, original, old_den):
    """Retain the entire count law and every original AP11 block coefficient."""
    probabilities = {n:source.ap_count_probability(11,F(5,3),n) for n in range(1,5)}
    identities = {1:{5:F(1)},2:{2:F(1),3:F(1)},3:{1:F(1),2:F(2)},4:{1:F(3),2:F(1)}}
    tail0,tail1 = tuple(F(50,3)*v for v in source.geom(11,5)[:2])
    require(encode(probabilities)==original['count_probabilities'] and encode(identities)==original['all_load_identities']
            and (tail0,tail1)==(F(5,43923),F(17,29282))
            and sum(probabilities.values())+tail0==1
            and sum(n*p for n,p in probabilities.items())+tail1==F(7,6),
            'Complete count probabilities and infinite first moment')
    for n,a in identities.items():
        require(min(a.values())>0 and sum(a.values())==n and sum(t*v for t,v in a.items())==5
                and all(sum(v*max(k-t,0) for t,v in a.items())==max(n*k-5,0) for k in range(1,7)),
                'Every integer transition and the full affine count identity')
    blocks = {}
    for e in range(4):
        a = {t:sum(probabilities[n]*identities[n].get(t,0)/n for n in range(e+1,5))
                 +(tail0 if t==1 else 0) for t in (1,2,3,5)}
        blocks[e] = {t:v for t,v in a.items() if v}
        require(blocks[e]==coefficients(original['AP11_block_results'][e]['hinge_coefficients']),
                'Original independently labelled AP11 block')
    h,s = tail1-4*tail0,tail1-5*tail0
    tail = original['full_count_tail']
    require((h,s)==(F(1,7986),F(1,87846))
            and F(tail['remaining_hinge1_coefficient'])==F(old_den['full_count_tail']['remaining_H1_coefficient'])==h
            and F(tail['whole_constant_coefficient'])==F(old_den['full_count_tail']['remaining_S_coefficient'])==s,
            'The two complete remaining count-tail coefficients')
    return blocks, {'count_probabilities':probabilities,'all_load_identities':identities,
                    'tail_probability':tail0,'tail_first_moment':tail1,
                    'remaining_hinge1_coefficient':h,'whole_constant_coefficient':s}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest()==PINS['certificate_io.py'], 'Pinned canonical artifact reader')
    io = module('small_consumer_io',base/'certificate_io.py')
    docs = {n:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', n+'.json'))) for n in SOURCES}
    pins = dict(PINS)
    for name,doc in docs.items():
        for path,pin in doc['source_sha256'].items():
            require(path not in pins or pins[path]==pin, 'Consistent source identity '+name+': '+path)
            pins[path] = pin
    for path,pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin, 'Pinned mathematical input '+path)
    newer,legacy,moments = [docs[n] for n in ('complete_small_retained_heads','legacy_retained_complete_head_transport','small_source_square_factorial_transport')]
    uniform,old_den,identities = [docs[n] for n in ('uniform_complete_k_comparison','uniform_ap_survival_denominator','load_two_cost_remainders')]
    original,heavy_source,legacy_source,uniform_origin = [docs[n] for n in ('retained135125_survival_comparison',
        'retained135125_heavy_comparison','retained_deletion_survival_comparison','whole_quadratic_same_head')]
    require(newer['domain']==legacy['domain']==moments['domain'], 'One actual source box for every new head and moment')
    domain = newer['domain'];par = domain['parameters']
    d,R,G = (F(par[k]) for k in ('delta','rho','gap'))
    require((d,R,G)==(F(1,10**8),F(1,10**11),F(1,60)), 'The complete certified small source box')
    oldpar = uniform['parameters']
    require(oldpar==old_den['parameters'] and d<=F(oldpar['delta']) and R<=F(oldpar['rho'])
            and F(domain['guards']['actual_r_upper'])==5*R<=F(uniform['original_slot_bound'])==F(1,520),
            'The small actual domain is contained in every unchanged145/139 domain')
    mass_floor = docs['k_neighborhood_radius_1_50']['global_mass_floor']
    upper_mass = docs['carrier_mass_residual_bound']
    D = F(mass_floor['minimum_S0'])
    require(D==F(53,360) and mass_floor['minimum_integer']==53 and mass_floor['integer_scale']==360
            and mass_floor['source_vertices']==1296 and mass_floor['joint_entries']==23328,
            'The existing complete146 source-product mass theorem')
    require(F(upper_mass['S0_upper_constant'])==D and F(upper_mass['S0_upper_sigma_coefficient'])==F(5,9)
            and F(upper_mass['E_upper_rho_coefficient'])==1, 'The106 actual carrier mass upper interface')
    S_upper = D+5*d/9+R
    load = lambda n:module('small_consumer_'+n,io.named_artifact(base/'frontier', n+'.py'))
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path)==pin for path,pin in engine.pins.items()), 'The complete original cost inventory is source-bound')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s',F(81,n*n)) for n in range(1,7)]
    weights = list(map(F,original['cost_weights']))
    require(len(tags)==len(weights)==52 and min(weights)>0 and tags[48]==('s',F(9)), 'All52 positive-weight original tests and the exact raw-square9 function')
    for name,doc in (('226',original),('225',heavy_source),('218',legacy_source)):
        require(encode(tags)==doc['original_cost_tags'] and doc['all_original_indices']==list(range(52))
                and list(map(F,doc['cost_weights']))==weights, 'Unchanged original labels and weights in'+name)
    require(list(map(F,uniform_origin['cost_weights']))==weights
            and len(uniform_origin['improved_cost_bounds'])==52
            and all(encode(tags[r['index']])==r['tag'] for r in uniform_origin['quadratic_results']),
            'The original113 cost order, weights and explicit quadratic labels inherited by145')
    rows = []
    require(len(uniform['cost_results'])==52, 'Every original145 uniform cost is retained as an available bound')
    for i,record in enumerate(uniform['cost_results']):
        require(record['index']==i and F(record['weight'])==weights[i], 'Same original cost order and outside weight')
        rows.append({'index':i,'original_tag':tags[i],'weight':weights[i],
                     'candidates':{'uniform145':F(record['uniform_upper'])},
                     'uniform145_group':record['group']})
    bynew = {r['objective']:r for r in newer['complete_tests']}
    require(set(bynew)=={'heavy0','heavy16','AP11-B0','AP13'}, 'All four original235 heads')
    require(set(legacy['tests'])=={'AP11-'+str(i) for i in range(4)}|{'AP13'}
            |{'linear-'+str(i) for i in (1,2,7,10,17,18,23,26,32,33,36)}, 'All sixteen available237 heads')
    for record in bynew.values():
        require(record['original_containing_choices']==62500000, 'The complete new head includes every original containing choice')
    transported = []
    for index,label in ((0,'heavy0'),(16,'heavy16')):
        head = bynew[label]
        identity = affine_identity(engine.source,tags[index],head['hinge_coefficients'])
        source = next(r for r in heavy_source['heavy_results'] if r['index']==index)
        require(identity['hinge_coefficients']==coefficients(source['scan']['coefficients'])
                and identity['at_one']==F(source['at_one']), 'The original225 heavy function')
        bound = identity['at_one']*S_upper+F(head['complete_hinge_upper'])
        rows[index]['candidates']['complete235'] = bound
        transported.append({'index':index,'source':'235','head':label,'identity':identity,'complete_cost_upper':bound})
    for record in legacy_source['linear_results']:
        index = record['index'];name = 'linear-'+str(index);head = legacy['tests'][name]
        require(head['covered_containing_choices']==62500000 and head['source_counts']['prefix_available']==0,
                'The complete legacy head retains every candidate')
        identity = affine_identity(engine.source,tags[index],head['original_coefficients'])
        require(identity['hinge_coefficients']==coefficients(record['scan']['coefficients'])
                and identity['at_one']==F(record['at_one'])==0, 'The source-bound original218 affine cost')
        bound = identity['at_one']*S_upper+F(head['complete_hinge_upper'])
        rows[index]['candidates']['complete237'] = bound
        transported.append({'index':index,'source':'237','head':name,'identity':identity,'complete_cost_upper':bound})
    require(len(transported)==13 and len({r['index'] for r in transported})==13, 'Thirteen independently bound original numerator functions')
    source_count = module('small_consumer_count',base/'verify_joint_frontier.py')
    block_coefficients,count = count_law(source_count,original,old_den)
    block_bounds = []
    for e in range(4):
        name,source = ('AP11-B0','235') if e==0 else ('AP11-'+str(e),'237')
        head = bynew[name] if e==0 else legacy['tests'][name]
        co = head['hinge_coefficients'] if e==0 else head['original_coefficients']
        require(coefficients(co)==block_coefficients[e], 'Transported AP11 head is the original complete count mixture')
        block_bounds.append({'block':e,'source':source,'head':name,'hinge_coefficients':block_coefficients[e],
                             'complete_upper':F(head['complete_hinge_upper'])})
    require(coefficients(bynew['AP13']['hinge_coefficients'])=={4:F(1)}, 'The independent AP13 fourth hinge')
    U4 = F(bynew['AP13']['complete_hinge_upper'])
    H1 = F(old_den['H1']['upper'])
    tail_cost = count['remaining_hinge1_coefficient']*H1+count['whole_constant_coefficient']*S_upper
    denominator = D-U4/6-(sum(r['complete_upper'] for r in block_bounds)+tail_cost)/7
    require(denominator>0 and H1>0 and S_upper>=D>0, 'Correctly directed positive complete denominator')
    Q = F(moments['square']['complete_square_upper'])
    T5 = F(moments['factorial']['complete_factorial_upper'])
    require(Q>=F(8201,1800) and T5>=F(619,720) and Q-D>=0, 'Uniform whole-square and existing138 factorial inputs')
    # Each current candidate is a separate valid bound on the same original function.
    direct = [min(r['candidates'].values()) for r in rows]
    U9 = direct[48]
    require(rows[48]['candidates']=={'uniform145':U9}, 'The entire old uniform raw-square9 is retained')
    identity_provider = load('load_two_cost_remainders')
    expected = {r['index']:r for r in identities['exact_integer_identities']}
    require(set(expected)=={41,42,43,44,45,49,50,51}, 'Exactly the original eight202 identities')
    feedback = []
    for support in identity_provider.SUPPORTS:
        index = support[0]
        identity = identity_provider.verify_identity(engine.source,tags[index],support)
        require(all(encode(v)==expected[index][k] for k,v in identity.items()), 'The identical all-load202 identity')
        a,b,c,e = (identity[k] for k in ('square_minus_mass','raw_square9','hinge4','factorial5'))
        require(min(a,b,c,e)>=0 and identity['load_two_remainder']>0, 'Every moment payment has its proved direction')
        payments = {'square_minus_mass':a*(Q-D),'raw_square9':b*U9,'hinge4':c*U4,'factorial5':e*T5}
        bound = sum(payments.values())
        rows[index]['candidates']['identity202_uniform_moments'] = bound
        feedback.append({'index':index,'identity':identity,'moment_payments':payments,'complete_cost_upper':bound,
                         'discarded_remainder':'The nonnegative original load-two event charge; no positive event mass is asserted.'})
    for row in rows:
        value = min(row['candidates'].values())
        row['complete_upper'] = value
        row['selected_candidates'] = [k for k,v in row['candidates'].items() if v==value]
        row['weighted_upper'] = row['weight']*value
    signed,square_weight,offset = (F(original[k]) for k in ('signed_mass_coefficient','complete_square_weight','offset'))
    require(signed==F(uniform['signed_mass_coefficient'])==F(identities['signed_mass_coefficient'])<0
            and square_weight==F(uniform['complete_square_weight'])==F(identities['complete_square_weight'])>0
            and offset==F(uniform['offset'])==F(identities['offset']), 'The original signed coefficient, whole-square weight and offset')
    positive = sum(row['weighted_upper'] for row in rows)
    mass_payment,square_payment = signed*D,square_weight*Q
    numerator = mass_payment+positive+square_payment
    require(numerator>0 and len(rows)==52 and [r['index'] for r in rows]==list(range(52)), 'One positive complete signed numerator with no missing or duplicate cost')
    comparison = offset+numerator/denominator
    target_budget = (F(403)-offset)*denominator-numerator
    require(target_budget>0 and comparison<F(403) and target_budget==(403-comparison)*denominator,
            'Exact strict403 local comparison, without summing independent improvement claims')
    return encode({'schema':'erdos7-complete-small-source-k-comparison-v1','source_sha256':pins,
        'domain':domain,'original_slot_bound':F(1,520),'baseline_uniform_domain':uniform['parameters'],
        'all_original_indices':list(range(52)),'original_cost_tags':tags,'cost_weights':weights,
        'mass_lower':D,'mass_upper':S_upper,'mass_floor_source':'146 complete effective source-product theorem; S=S0+rho>=53/360',
        'cost_results':rows,'transported_affine_costs':transported,'integer_identity_feedback':feedback,
        'unchanged_uniform_cost_indices':[r['index'] for r in rows if r['selected_candidates']==['uniform145']],
        'complete_square_upper':Q,'complete_factorial_upper':T5,'uniform_raw_square9_upper':U9,
        'uniform_hinge4_upper':U4,'AP11_block_results':block_bounds,'count_law':count,
        'full_count_tail':{'H1_source':'139 uniform domain delta<=1/10000,rho<=1/100000',
                           'H1_upper':H1,'positive_mass_upper':S_upper,'remaining_cost_upper':tail_cost},
        'AP13_penalty_upper':U4/6,'AP11_penalty_upper':(sum(r['complete_upper'] for r in block_bounds)+tail_cost)/7,
        'uniform_denominator_lower':denominator,'signed_mass_coefficient':signed,'signed_mass_upper':mass_payment,
        'positive_cost_sum':positive,'complete_square_weight':square_weight,'complete_square_payment':square_payment,
        'numerator_upper':numerator,'offset':offset,'comparison_upper':comparison,'room_below403':403-comparison,
        'strict403_numerator_margin':target_budget,
        'head_consumer_counts':{'new235':4,'legacy237':14,'affine_costs':13,'AP11_blocks':4,'AP13_tests':1},
        'scope':'Complete original52-cost signed comparison below403 on both actual K-source neighborhoods sigma<=10^-8,rho<=10^-11. The actual r<=5rho satisfies the inherited r<=1/520 condition. All independent tests, complete square, complete factorial, four AP11 blocks, separate AP13 test, complete count law and every exponent tail remain. No untransported face-only cost,174 factorial,207 raw-square9,previous218 minimum or unexplained improvement subtraction is used. The residual/source complement, global K join,actual-family attainment,Lean verification and unrestricted Erdos7 remain separate.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    args = parser.parse_args();result = calculate(args.base)
    io = module('small_consumer_output',args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact complete52-cost local certificate')
    for k in ('numerator_upper','uniform_denominator_lower','comparison_upper','room_below403'):
        print(k+' = '+str(float(F(result[k]))))
    print('PASS: all52 original costs and complete signed/count-tail consumer below403 on the small source box; global complement remains separate.')


if __name__=='__main__':
    try:
        main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError) as error:
        print('FAIL: '+str(error),file=sys.stderr)
        raise SystemExit(1)
