#!/usr/bin/env python3
"""Complete original J moments with seven retained old labels on the same source."""
import argparse,importlib.util,json,sys
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import combinations,product
from math import lcm
from pathlib import Path
from types import MethodType
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-source/j_face_triple_pair_factorial_heads.json'
PINS={'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j-source/j_face_joint_pair_factorial_heads.py': '323a21c1a77cb8030be4e860f69e2c42882c4c749259797f4c04e3e249aaa993', 'certificates/source_norms/j-source/j_face_joint_pair_factorial_heads.json': '503746ba3ecb18cce6255c74414a8e416e3331edc1fd4b8befff283b3faec9df', 'profile-notes/j-source/276-actual-retained-tail-pairs-strengthen-original-j-costs-and-square.md': 'b2c05708f6be7b6404052e504369148505736859b021ec72679cad7ebdc70a8c', 'frontier/j-source/j_face_triple_second_depth_heads.py': 'c6c1f5dc4a06a9a16bb6291abaea28e08a3c7fb776edfff55e226bb723954f3a', 'certificates/source_norms/j-source/j_face_triple_second_depth_heads.json': '28efda83f17bffed4a75f49448820c118ee300a4515f807aa4fd677bc3ea8743', 'profile-notes/j-source/264-seven-retained-states-and-two-seven-depths-control-complete-j-heads.md': '7eadaa5f36996f8afc2af013fba2d83d27b7e581ebf667507f67483d5169550a', 'frontier/j-source/j_face_pure_low_factorial_heads.py': 'ddee35c8f61e626eae68e116788eb2c7958a90f831a72d2ecc7ac5cffd60c15b', 'certificates/source_norms/j-source/j_face_pure_low_factorial_heads.json': 'dc38003f46c3d5323fecb935267593078a18873db226dc5f358bd14bc71bc384', 'profile-notes/j-source/278-two-pure-factorial-observations-strengthen-the-j-source.md': 'c311bcb6e191e3e6119beac57423dfec0a7afbbde0b2080a7bbd9a16d1b04947'}
TARGETS=(('cost-48',48,3),('cost-49',49,2),('square',-1,1),('factorial5',-5,5),('factorial2',-2,2),('factorial3',-3,3))
RETAINED=(25,27,75,81,135,125,225)

def require(ok,message):
    if not ok:raise ValueError(message)

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable published mathematical source')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value

def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v)for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v)for v in value]
    return value


def pair_partitions(source,coherent,prior,generalized):
    def survivor(d):
        a,b=source.exponents(d)
        if b==0:return F(11,20*3**a)
        if a<=2:return (F(13,30),F(1,3),F(1,9))[a]/5**b
        return F(1,d)
    raw=lambda d:coherent.raw_cap(*source.exponents(d))
    oo=[{'labels':(a,b),'lcm':lcm(a,b),'assigned_survivor_cap':survivor(lcm(a,b))}for a,b in combinations(RETAINED,2)]
    oz=[]
    blocks=((1,'all-positive-depths',F(1,5)),(3,1,F(6,35)),(5,1,F(6,35)),(9,1,F(6,35)),(15,1,F(6,35)),(3,2,F(6,245)),(5,2,F(6,245)))
    for d in RETAINED:
        for c,depth,w in blocks:
            m=lcm(d,c);cap=raw(m)
            oz.append({'old_label':d,'positive7_cofactor':c,'depth':depth,'complete_depth_weight':w,'old_lcm':m,'assigned_raw_cap':cap,'assigned_payment':w*cap})
    require(encode([r for r in oo if 225 not in r['labels']])==encode(prior['selected_POO_pairs'])
            and encode([r for r in oz if r['old_label']!=225])==encode(prior['selected_POZ_blocks']),
            'Every previously selected original pair payment is unchanged')
    poo=sum(r['assigned_survivor_cap']for r in oo);poz=sum(r['assigned_payment']for r in oz)
    require(len(oo)==21 and len(oz)==49 and poo==F(11537,202500)and poz==F(17351,275625),
            'Exactly21 original old-old pairs and49 selected original old-positive-seven blocks')
    require(poo-F(prior['selected_POO_payment'])==F(134,10125)
            and poz-F(prior['selected_POZ_payment'])==F(229,55125),
            'Only the six225 old-old pairs and seven225 raw positive-seven blocks are added')
    original_poo,original_poz=F(prior['original_POO_upper']),F(prior['original_POZ_upper'])
    require(original_poo==F(111,800)and original_poz==F(121,720)
            and original_poo-poo==F(132479,1620000)and original_poz-poz==F(51501,490000)
            and original_poo+original_poz+F(89,240)==F(4879,7200),
            'Every unselected original pair and infinite tail remains in its complete positive complement')
    selected=list(generalized.SELECTED_WEIGHTS);selected[3]+=F(1,25)
    remaining=list(generalized.REMAINING_WEIGHTS);remaining[3]-=F(1,25)
    require(tuple(remaining)==(F(1,162),F(1,500),F(1,100),F(1,100),F(7,1080))
            and all(a+b==c for a,b,c in zip(selected,remaining,generalized.OLD_WEIGHTS)),
            'The old225 cross occupies only its original cell-five coefficient1/25')
    for mask,state in product(range(16),range(8)):
        q,n=mask.bit_count(),state.bit_count()
        bits=tuple((mask>>bit)&1 for bit in range(4))+tuple((state>>bit)&1 for bit in range(3))
        require(sum(bits)==q+n and sum(a*b for a,b in combinations(bits,2))==F(q*(q-1),2)+q*n+F(n*(n-1),2),
                'Every actual seven-label Boolean count and all21 pair multiplicities')
    return {'retained_old_labels':RETAINED,'selected_POO_pairs':oo,'selected_POO_payment':poo,
            'selected_POZ_blocks':oz,'selected_POZ_payment':poz,'new225_POO_payment':F(134,10125),'new225_POZ_payment':F(229,55125),
            'original_POO_upper':original_poo,'original_POZ_upper':original_poz,'remaining_POO_upper':original_poo-poo,
            'remaining_POZ_upper':original_poz-poz,'original_PZZ_upper':F(89,240),'original_complete_pair_tail':F(4879,7200),
            'old_cross_weights':generalized.OLD_WEIGHTS,'selected_cross_weights':selected,'remaining_cross_weights':remaining,
            'state_identity_checks':128,'positive7_cross_tail_unchanged':True}


def inputs(base):
    source=module('triple_pair_source276',base/'frontier/j-source/j_face_joint_pair_factorial_heads.py')
    data=source.inputs(base);io,core=data['io'],data['core']
    read=lambda n:json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(n+'.json')),object_pairs_hook=core.unique)
    heads=read('j-source/j_face_joint_pair_factorial_heads');lowheads=read('j-source/j_face_pure_low_factorial_heads')
    prior256=read('j-source/j_face_second_depth_retained_heads');prior264=read('j-source/j_face_triple_second_depth_heads')
    pins=dict(data['pins'])
    for item in(heads,lowheads,prior256,prior264):
        require(item['geometry']==heads['geometry']and F(item['survivor_mass'])==F(3,20),'Both entire original actual saturated J faces')
        for path,pin in item['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent inherited input '+path);pins[path]=pin
    require(PINS,'Exact published input pins')
    for path,pin in PINS.items():
        require(path not in pins or pins[path]==pin,'Consistent direct input '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical source '+path)
    require(encode(data['conditional'].record)==heads['conditional_positive7']==lowheads['conditional_positive7']
            and encode(data['payments'])==heads['pair_partitions']==lowheads['pair_partitions'],
            'The published complete conditional PZZ tables and every original selected pair payment')
    triple=module('triple_pair_model264',base/'frontier/j-source/j_face_triple_second_depth_heads.py')
    low=module('triple_pair_scanner278',base/'frontier/j-source/j_face_pure_low_factorial_heads.py')
    coherent=module('triple_pair_coherent258',base/'frontier/j-source/j_face_coherent_positive7_pairs.py')
    reference=triple.TripleSecondDepthJHead(base,*[data[n]for n in('j','core','pair','depth','prior244','prior251')],prior256)
    require(reference.specification==prior264['model']and reference.lp.nvars==6531 and len(reference.lp.rows)==11211 and len(reference.lp.equalities)==19,
            'The complete unchanged264 actual raw/survivor model, all seven states and independent225 profile')
    payments=pair_partitions(source,coherent,data['payments'],data['generalized'])
    data.update(source=source,low=low,triple=triple,reference=reference,heads=heads,lowheads=lowheads,pins=pins,triple_payments=payments)
    return data


def make_problem(base,data,k,expansion,bank):
    source,j,generalized=data['source'],data['j'],data['generalized'];reference=data['reference']
    problem=source.make_problem(base,*[data[n]for n in('j','core','pair','depth','second','moment','shift','generalized','prior244','prior251')],
                                F(4879,7200),k,data['conditional'],data['payments'])
    require(problem.parts.cache_info().currsize==0,'Fresh immutable-threshold complete affine compiler')
    problem.fc,problem.atone=expansion['factorial_coefficient'],expansion['at_one']
    problem.lp,problem.specification,problem.codec=reference.lp,reference.specification,reference.codec
    problem.bank=dict(bank);problem.used=set();problem.verified={};problem.proposer=None
    native=reference.objective;mom=data['moment'].JMomentHead(j);payment=data['triple_payments'];triple=data['triple']
    @lru_cache(None)
    def crosses(layout):
        H=problem.head.bridge.head_load(layout);h=tuple(F(max(b-k+1,0))for b in H)
        z=tuple(w*v for w,v in zip(mom.w,h));p,d=mom.pre,mom.descendant
        coefficients=(max(sum(p[5*c+s]*z[5*c+s]for s in range(5))for c in range(5)),
            max(sum(d[5*c+s]*z[5*c+s]for c in range(5))for s in range(5)),
            max(sum(d[5*c+s]*z[5*c+s]for c in range(5)if j.ROOT[c]==r)for r,s in product(range(2),range(5))),
            max(a*b for a,b in zip(d,z)),max(z))
        old=sum(a*b for a,b in zip(coefficients,generalized.OLD_WEIGHTS))
        selected=sum(a*b for a,b in zip(coefficients,payment['selected_cross_weights']))
        remaining=sum(a*b for a,b in zip(coefficients,payment['remaining_cross_weights']))
        require(old==mom.old_tail(z)==selected+remaining and min(old,selected,remaining)>=0,'Complete same-head old-tail cross partition')
        # This positive-seven term still contains225*7^e for every positive e.
        residual=remaining+mom.old_tail(h)/5
        endpoints=tuple(residual+sum(weight*max(mom.lp(tuple(a*b for a,b in zip(mask,h)),theta)for mask in family)
            for family,weight in zip(mom.masks[1:],generalized.RAW_MASK_WEIGHTS))for theta in(j.LO,j.HI))
        return {'head':H,'h':h,'zero7_coefficients':coefficients,'old_zero7_cross':old,'selected_zero7_payment':selected,
                'remaining_zero7_cross':remaining,'complete_cross_residual_endpoints':endpoints}
    def objective(self,co,layout,projection):
        require(self.k==k,'One immutable factorial threshold')
        fc,at=self.fc,self.atone;obj,const=native(co,layout,projection);cross=crosses(layout)
        H,h=cross['head'],cross['h'];c0,c1=cross['complete_cross_residual_endpoints'];p0,p1=data['conditional'].endpoints(tuple(projection))
        obj[875]+=fc*((c1-c0)+(p1-p0))
        const+=at*F(3,20)+fc*(c0+F(4879,7200)-F(89,240)+p0-payment['selected_POO_payment']-payment['selected_POZ_payment'])
        r,s,c63,r105,s105,r147,s245=projection
        for i,(b,hv)in enumerate(zip(H,h)):
            c,slot=divmod(i,5)
            m1=int(j.ROOT[c]==r)+int(slot==s)+int(c==c63)+int(j.ROOT[c]==r105 and slot==s105)
            m2=int(j.ROOT[c]==r147)+int(slot==s245);weight=F(1,5)+F(6,35)*m1+F(6,245)*m2
            phi=F(max(b-k,0)*max(b-k+1,0),2)
            for mask in range(16):
                cell=16*i+mask;q=mask.bit_count()
                obj[cell]+=fc*(hv+q)*weight;obj[425+cell]+=fc*(phi+hv*q+F(q*(q-1),2))
                for state in range(1,8):
                    n=state.bit_count()
                    obj[triple.U+400*(state-1)+cell]+=fc*n*weight
                    obj[triple.V+400*(state-1)+cell]+=fc*(hv*n+q*n+F(n*(n-1),2))
        require(len(obj)==6531 and isinstance(const,F)and all(isinstance(a,F)for a in obj)
                and all(a>=0 for i,a in enumerate(obj)if i!=875),'Entire original objective; only the common-theta secant coordinate may be signed')
        return obj,const
    problem.objective=MethodType(objective,problem);problem.triple_cross_parts=crosses
    return problem


def calculate(base,bank,seed_rows):
    data=inputs(base);source,low=data['source'],data['low']
    require([(r['name'],r['index'],r['threshold'])for r in seed_rows]==list(TARGETS),'All six unchanged targets in canonical order')
    previous={r['name']:F(r['adopted_upper'])for r in data['heads']['results']}
    previous.update({r['name']:F(r['complete_factorial_upper'])for r in data['lowheads']['results']})
    rows=[];used=set();digest=sha256();layout_count=0;checked_seeds=[]
    for (name,index,k),seed in zip(TARGETS,seed_rows):
        if index>=0:ex=data['generalized'].shifted_identity(data['engine'].source,data['quad'],data['tags'][index],k)
        elif index==-1:ex=source.square_expansion()
        elif k==5:ex=source.pure_factorial_expansion()
        else:ex=low.expansion(k)
        co=ex['hinge_coefficients'];problem=make_problem(base,data,k,ex,bank);seeds=[]
        for record in seed['branches']:
            layout,projection=tuple(record['layout']),tuple(record['projection'])
            upper,key,constant=problem.dual_upper(co,layout,projection)
            row={'layout':layout,'projection':projection,'upper':upper,'key':key,'constant':constant}
            require(encode(row)==record,'Every supplied seed recomputes from the complete6531-column objective');seeds.append(row)
        for layout in data['j'].layouts():
            component={'name':name,'threshold':k,'layout':layout,'factorial_parts':problem.parts(layout),'cross_components':problem.triple_cross_parts(layout)}
            digest.update(json.dumps(encode(component),separators=(',',':')).encode());layout_count+=1
        if co:scan=source.conditional_factorial_scan(problem,data['j'],data['shift'],data['conditional'],co,seeds,name)
        elif k==5:scan=source.pure_factorial_scan(problem,data['conditional'],seeds)
        else:scan=low.pure_factorial_scan(problem,data['conditional'],seeds)
        if co:scan['scanner_kind']='complete-original-conditional-two-four-six'
        upper=scan['complete_cost_upper'];used.update(problem.used)
        require(0<upper<previous[name]and scan['covered_containing_choices']==62500000 and not problem.prior_used and problem.used<=set(bank),
                'A strict full-domain improvement with complete old pruning, all infinite tails and only supplied exact duals')
        branch=scan['maximizing_certificate_branch'];checked_seeds.append({'name':name,'index':index,'threshold':k,'branches':seeds})
        rows.append({'name':name,'original_cost_index':index if index>=0 else None,'factorial_threshold':k,'expansion':ex,
            'all_head_tail_split':data['generalized'].all_tail_split(k),'scan':scan,'complete_cost_upper':upper,'adopted_upper':upper,
            'previous_adopted_upper':previous[name],'improvement_over_previous':previous[name]-upper,
            'maximizing_cross_components':problem.triple_cross_parts(tuple(branch['layout'])),
            'maximizing_conditional_PZZ_endpoints':data['conditional'].endpoints(tuple(branch['projection21_35_63_105_147_245']))})
        print('Complete seven-label '+name+' <= '+str(float(upper)),flush=True)
    require(layout_count==75000,'Every original layout at all six fixed target thresholds')
    kept={key:bank[key]for key in sorted(used)};codec=data['reference'].codec
    encoded=codec.encode_dual_bank(kept,inequality_count=11211,equality_count=19)
    require(codec.decode_dual_bank(encoded,inequality_count=11211,equality_count=19)==kept,'Lossless canonical exact consumed dual bank')
    return encode({'schema':'erdos7-j-face-triple-pair-factorial-heads-v1','source_sha256':data['pins'],'geometry':data['heads']['geometry'],
        'source_mass':F(1,4),'survivor_mass':F(3,20),'model':data['reference'].specification,
        'original_cost_indices':[48,49],'outside_targets':['square','factorial5','factorial2','factorial3'],
        'original_affine_pruning_pair_tail':F(4879,7200),'complete_positive7_hinge_tail':F(37,1225),'complete_old_hinge_tail':F(6151,405000),
        'pair_partitions':data['triple_payments'],'conditional_positive7':data['conditional'].record,'original_head_count':12500,
        'threshold_layout_record_count':layout_count,'cross_endpoint_record_count':2*layout_count,
        'all_factorial_and_cross_components_sha256':digest.hexdigest(),'seed_rows':checked_seeds,'results':rows,'encoded_rational_duals':encoded,
        'distinct_dual_count':len(kept),'rational_column_checks':6531*len(kept),'total_containing_choices':375000000,
        'total_independent_affine_checks':sum(r['scan']['independent_affine_checks']for r in rows),
        'scope':'Six complete unchanged original functions on both entire actual saturated J faces; all62500000 original independent containing choices per target, the complete late interval and every old and positive-seven tail. The unchanged264 source retains all seven135/125/225 states with the independent225 raw profile. Exactly21 original POO pairs and49 POZ blocks replace only their assigned cap payments; every complementary pair and positive-seven cofactor remains. Complete276/278 affine pruning and conditional PZZ are unchanged. No actual attainment, off-face extension, complete52-cost comparison, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes=parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    parser.add_argument('--proposal',type=Path);args=parser.parse_args()
    require(args.proposal is None or args.write,'Only the writer accepts a proposal')
    require(not args.write or args.proposal is not None,'Writer requires original seeds and complete canonical duals')
    io=module('triple_pair_reader',args.base/'certificate_io.py');core=module('triple_pair_json',args.base/'frontier/j-source/j_face_joint_selected_heads.py')
    proposed=json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE),object_pairs_hook=core.unique)
    codec=module('triple_pair_codec',args.base/'frontier/transport/retained135_heavy_comparison.py')
    bank=codec.decode_dual_bank(proposed['encoded_rational_duals'],inequality_count=11211,equality_count=19)
    result=calculate(args.base,bank,proposed['seed_rows'])
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==proposed,'Every complete seven-label source certificate field recomputes exactly')
    print('PASS six complete seven-label J moments;375000000 original choices;'+str(result['distinct_dual_count'])+' exact6531-column duals; every infinite tail.',flush=True)


if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
