#!/usr/bin/env python3
"""Complete original J costs, square and Phi5 with actual retained tail-pair counts."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product,combinations
from math import lcm
from pathlib import Path
from types import MethodType
from time import perf_counter
import importlib.util,json,sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j_face_joint_pair_factorial_heads.json'
PINS={'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j_face_generalized_factorial_heads.py': 'f46eb9ffcc278a356c8b48df6add91746daff164c4ba0fc4319feed0ad237d8f', 'certificates/source_norms/j_face_generalized_factorial_heads.json': 'da98088a723917a401769cde842bd30cc7534c74ada57a7c446e3b05ebb66be4', 'profile-notes/274-generalized-factorial-thresholds-strengthen-two-original-j-costs.md': 'daa926a8f9fe27a8cddc4e94f5cb98e165963334cad07c42623b932fe90ab7ae', 'frontier/j_face_generalized_factorial_complete_moment_cost_comparison.py': '95a08a05d6a8619bedc56dbfaef422134001bd4ac2f1d698a712cf87c4b79e0c', 'certificates/source_norms/j_face_generalized_factorial_complete_moment_cost_comparison.json': '31f6ee08f263b7cfe5d3a50c8cabb0ed0e629ca86ea7d72b34a25db7e453f717', 'profile-notes/275-generalized-factorial-observations-improve-the-complete-j-comparison.md': '745490a332d3f21d5be02d459a3bef0172e5c3845a19a5874cbc61835f98725c', 'frontier/j_face_raw_prime_path_pairs.py': '63563f4034949eeb4cb7c5b9bc4b4d19174939a682c60993a0a54a85a2bf651a', 'certificates/source_norms/j_face_raw_prime_path_pairs.json': '93b616897af512407e827a5b2fffacc1986261bd3dbadb71426603c837a44fd2', 'profile-notes/265-complete-raw-prime-paths-improve-the-positive-seven-pair-block.md': '33f2c477c72f36123ce1c0e44e169c10a2349c88c1d5382b7b208d2d1b93849b'}
TARGETS=((48,3),(49,2),(-1,1),(-3,5))
RETAINED=(25,27,75,81,135,125)

def require(ok,message):
    if not ok:raise ValueError(message)

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Loadable actual mathematical input')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value

def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v) for v in value]
    return value

def exponents(modulus):
    require(isinstance(modulus,int) and modulus>0,'Positive original old-cofactor modulus')
    a=b=0
    while modulus%3==0:modulus//=3;a+=1
    while modulus%5==0:modulus//=5;b+=1
    require(modulus==1,'Only original three/five cofactor labels')
    return a,b


def pair_partitions(source265,coherent,tail):
    # The original full OO and OZ series are inherited, not reestimated.
    original=source265['complete_tail_distinct_pairs']
    require(F(original)==F(4879,7200) and F(source265['complete_PZZ_upper'])==F(89,240),
            'The complete265 pair complement and positive-seven block')
    surviving_coefficients=tuple(map(F,tail['surviving_pure_coefficients']))
    require(surviving_coefficients==(F(11,20),F(13,30),F(1,3),F(1,9)),
            'The complete original241 survivor cap coefficients')
    def surviving(modulus):
        a,b=exponents(modulus);require(a>=3 or b>=2,'An original omitted old label')
        if b==0:return surviving_coefficients[0]/3**a
        if a<=2:return surviving_coefficients[a+1]/5**b
        return F(1,3**a*5**b)
    def raw(modulus):return coherent.raw_cap(*exponents(modulus))
    oo=[{'labels':(a,b),'lcm':lcm(a,b),'assigned_survivor_cap':surviving(lcm(a,b))}
        for a,b in combinations(RETAINED,2)]
    oo_payment=sum(row['assigned_survivor_cap']for row in oo)
    require(len(oo)==15 and oo_payment==F(8857,202500),'Exactly fifteen distinct assigned old-old pair payments')
    oz=[]
    for d in RETAINED:
        for cofactor,depth,weight in ((1,'all-positive-depths',F(1,5)),
            (3,1,F(6,35)),(5,1,F(6,35)),(9,1,F(6,35)),(15,1,F(6,35)),
            (3,2,F(6,245)),(5,2,F(6,245))):
            m=lcm(d,cofactor);cap=raw(m)
            oz.append({'old_label':d,'positive7_cofactor':cofactor,'depth':depth,
                       'complete_depth_weight':weight,'old_lcm':m,'assigned_raw_cap':cap,'assigned_payment':weight*cap})
    oz_payment=sum(row['assigned_payment']for row in oz)
    require(len(oz)==42 and oz_payment>0,'All six old labels times the same seven complete selected positive-seven blocks')
    poo,poz=F(tail['old_old_distinct']),F(tail['old_positive7'])
    require(poo+poz+F(89,240)==F(original) and poo>oo_payment and poz>oz_payment,
            'Only the assigned known POO and POZ summands are replaced; their entire complements stay positive')
    return {'retained_old_labels':RETAINED,'selected_POO_pairs':oo,'selected_POO_payment':oo_payment,
            'selected_POZ_blocks':oz,'selected_POZ_payment':oz_payment,
            'original_POO_upper':poo,'original_POZ_upper':poz,
            'remaining_POO_upper':poo-oo_payment,'remaining_POZ_upper':poz-oz_payment,
            'original_complete_pair_tail':F(original),'original_PZZ_upper':F(89,240)}


class ConditionalPositiveSeven:
    """Exact full-head weighted maxima for the first two independent depths."""
    def __init__(self,j,moment,joint,raw_paths,source265):
        self.j=j;mom=moment.JMomentHead(j)
        p,_,e,_=j.source_tables(j.LO);c3=tuple(sum(row)for row in p);c5=tuple(sum(row[s]for row in e)for s in range(5))
        require(encode(c3)==source265['raw_prime_caps']['three_cells']
                and encode(c5)==source265['raw_prime_caps']['five_slots'],
                'Exact original raw prime-cylinder caps without survivor density')
        omitted={k:F(v)for k,v in source265['complete_raw_omitted_tail'].items()
                 if k in ('raw_omitted_distinct_pairs','raw_omitted_diagonal')}
        self.a1,self.b1,self.a2,self.b2=F(6,35),F(1,70),F(6,245),F(1,70)
        self.atail,self.btail=F(1,245),F(1,210)
        q=F(1,7)
        require(self.a1+self.a2+self.atail==F(6,5)*q/(1-q)==F(1,5)
                and self.b1+self.b2+self.btail==F(1,30),
                'Complete geometric depth and unequal-depth partner weights')
        # For every e>=1: beta_e=((e-1)*u_e+sum_(f>e)u_f)/2
        # =u_e*((e-1)/2+1/12). The upper partner tail is u_e/6.
        require(q/(1-q)==F(1,6) and F(6,5)*q*q/(2*(1-q)**2)+F(1,12)*F(1,5)==F(1,30),
                'Exact all-depth unequal-partner coefficient identity and its complete sum')
        self.tail=self.atail*F(125,96)+self.btail*F(53,16)
        self.first={};self.second={};digest=sha256();n=0;best={'pair':F(-1),'square':F(-1)}
        for layout in j.layouts():
            B=joint.head_load(j,layout);cross=mom.old_tail(B)
            A3=tuple(sum(p[c][s]*B[5*c+s]for s in range(5))for c in range(5))
            A5=tuple(sum(e[c][s]*B[5*c+s]for c in range(5))for s in range(5))
            blocks={name:[raw_paths.path_bound(3,3,A3,c3,name=='square'),
                          raw_paths.path_bound(5,2,A5,c5,name=='square')]for name in best}
            changes={name:sum(row['block_change']for row in rows)for name,rows in blocks.items()}
            r,c,s,rr,ss,cc,tt=layout
            for ep,theta in enumerate((j.LO,j.HI)):
                oldpair=mom.lp(tuple(F(b*(b-1),2)for b in B),theta)+cross+omitted['raw_omitted_distinct_pairs']
                oldsquare=mom.lp(tuple(F(b*b)for b in B),theta)+2*cross+2*omitted['raw_omitted_distinct_pairs']+omitted['raw_omitted_diagonal']
                P,Q=oldpair+changes['pair'],oldsquare+changes['square']
                require(isinstance(P,F) and isinstance(Q,F) and 0<P<=F(125,96) and 0<Q<=F(53,16),
                        'Every complete same-head raw pair and square cap uses exact rational arithmetic')
                row={'layout':layout,'theta':theta,'raw_cross_coefficients3':A3,'raw_cross_coefficients5':A5,
                     'complete_raw_old_cross':cross,'previous_pair_upper':oldpair,'previous_square_upper':oldsquare,
                     'pair_change':changes['pair'],'square_change':changes['square'],'complete_pair_upper':P,'complete_square_upper':Q}
                digest.update(json.dumps(encode(row),separators=(',',':')).encode())
                key=(r,s,c,rr,ss,ep);key2=(r,s,ep)
                self.first[key]=max(self.first.get(key,F(-1)),self.a1*P+self.b1*Q)
                self.second[key2]=max(self.second.get(key2,F(-1)),self.a2*P+self.b2*Q)
                best['pair']=max(best['pair'],P);best['square']=max(best['square'],Q);n+=1
        require(n==25000 and len(self.first)==1000 and len(self.second)==20
                and best=={'pair':F(125,96),'square':F(53,16)}
                and digest.hexdigest()==source265['raw_head_scan']['all_endpoint_components_sha256'],
                'Every original265 raw head and complete prime path recomputes exactly before conditioning')
        first_rows=[{'projection21_35_63_105':key,'endpoint_upper':tuple(self.first[key+(ep,)]for ep in range(2))}
                    for key in sorted({key[:-1]for key in self.first})]
        second_rows=[{'projection147_245':key,'endpoint_upper':tuple(self.second[key+(ep,)]for ep in range(2))}
                     for key in sorted({key[:-1]for key in self.second})]
        endpoint_digest=sha256();count=0
        for projection in product(range(2),range(5),range(5),range(2),range(5),range(2),range(5)):
            endpoint_digest.update(json.dumps(encode({'projection':projection,'PZZ_endpoints':self.endpoints(projection)}),separators=(',',':')).encode());count+=1
        require(count==5000,'Every independent six-projection combination has its complete conditional pair secant')
        self.record={'original_raw_head_count':12500,'raw_endpoint_record_count':n,'raw_objective_evaluations':2*n,
            'original265_components_sha256':digest.hexdigest(),'first_depth_weights':(self.a1,self.b1),
            'second_depth_weights':(self.a2,self.b2),'later_depth_weights':(self.atail,self.btail),
            'complete_later_depth_constant':self.tail,'first_projection_rows':first_rows,'second_projection_rows':second_rows,
            'first_completion_count':25,'second_completion_count':1250,'complete_projection_count':count,
            'conditional_endpoint_count':2*count,'all_conditional_endpoints_sha256':endpoint_digest.hexdigest()}

    @lru_cache(None)
    def endpoints(self,projection):
        r,s,c,rr,ss,r2,s2=projection
        values=tuple(self.first[(r,s,c,rr,ss,ep)]+self.second[(r2,s2,ep)]+self.tail for ep in range(2))
        require(min(values)>0 and max(values)<=F(89,240),'A complete conditional PZZ bound at both common-theta endpoints')
        return values


def square_expansion():
    a,fc,k=F(1),F(2),1;co={1:F(1)}
    polynomial=(a-sum(t*v for t,v in co.items())+fc*F(k*(k-1),2),sum(co.values())+fc*F(1-2*k,2),fc/2)
    finite={n:n*n for n in range(1,9)}
    require(polynomial==(F(0),F(0),F(1))
            and all(a+sum(v*max(n-t,0)for t,v in co.items())+fc*F(max(n-k,0)*max(n-k+1,0),2)==v for n,v in finite.items()),
            'Original square identity at every finite transition and all three coefficients of its entire polynomial')
    return {'factorial_threshold':k,'at_one':a,'hinge_coefficients':co,'factorial_coefficient':fc,
            'finite_transition_values':finite,'polynomial_tail':{'entrance':1,'constant':polynomial[0],'linear':polynomial[1],'leading':polynomial[2]}}


def pure_factorial_expansion():
    return {'factorial_threshold':5,'at_one':F(0),'hinge_coefficients':{},'factorial_coefficient':F(1),
            'finite_transition_values':{n:F(max(n-5,0)*max(n-4,0),2)for n in range(1,7)},
            'polynomial_tail':{'entrance':5,'constant':F(10),'linear':F(-9,2),'leading':F(1,2)}}


def pure_factorial_scan(problem,conditional,seed_branches):
    """Exhaustive pure-Phi5 scan with complete layout and conditional pair pruning."""
    require(problem.k==5 and problem.fc==1 and problem.atone==0,
            'The empty hinge sum represents exactly Phi5 without a synthetic hinge')
    layouts=tuple(problem.j.layouts())
    projections=tuple(product(range(2),range(5),range(5),range(2),range(5),range(2),range(5)))
    require(len(layouts)==12500 and len(projections)==5000,'All original independent containing choices')
    layout_set,projection_set=set(layouts),set(projections)
    require(len(seed_branches)==60 and len({(tuple(r['layout']),tuple(r['projection']))for r in seed_branches})==60,
            'Sixty distinct explicit seed branches, without any optimality assumption')
    used_before=set(problem.used)
    def affine(layout,projection):
        pp=problem.parts(layout);zz=conditional.endpoints(projection)
        line=tuple(part[0]+problem.pair_tail-F(89,240)+pzz for part,pzz in zip(pp,zz))
        require(all(a<=part[0]+problem.pair_tail for a,part in zip(line,pp)),
                'Only the entire conditional PZZ block replaces its assigned old cap in this affine')
        return line
    def branch(layout,projection):
        require(layout in layout_set and projection in projection_set,'Original independent seed or scanned labels')
        value,key,constant=problem.dual_upper({},layout,projection);line=affine(layout,projection)
        return {'layout':layout,'projection':projection,'conditional_affine':line,'dual_upper':value,
                'adopted':min(value,max(line)),'dual_key':key,'constant':constant}
    seeds=[];best=F(-1);witness=None
    for seed in seed_branches:
        record=branch(tuple(seed['layout']),tuple(seed['projection']));seeds.append(record)
        if record['adopted']>best:best=record['adopted'];witness=record
    seed_upper=best;digest=sha256()
    counts={k:0 for k in ('layouts','layout_bounded','conditional_projections','conditional_bounded','joint_dual_branches')}
    maxima={'layout':F(-1),'conditional':F(-1)}
    for layout in layouts:
        counts['layouts']+=1;pp=problem.parts(layout);oldline=tuple(part[0]+problem.pair_tail for part in pp)
        if max(oldline)<=best:
            counts['layout_bounded']+=1;maxima['layout']=max(maxima['layout'],max(oldline))
            digest.update(repr(('layout',layout,oldline)).encode());continue
        for projection in projections:
            counts['conditional_projections']+=1;line=affine(layout,projection)
            if max(line)<=best:
                counts['conditional_bounded']+=1;maxima['conditional']=max(maxima['conditional'],max(line))
                digest.update(repr(('conditional',layout,projection,line)).encode());continue
            record=branch(layout,projection);counts['joint_dual_branches']+=1
            digest.update(repr(('joint',layout,projection,line,record['dual_key'],str(record['dual_upper']),str(record['constant']))).encode())
            if record['adopted']>best:best=record['adopted'];witness=record
    require(counts['layouts']==12500
            and counts['conditional_projections']==5000*(12500-counts['layout_bounded'])
            and counts['conditional_bounded']+counts['joint_dual_branches']==counts['conditional_projections']
            and 5000*counts['layout_bounded']+counts['conditional_bounded']+counts['joint_dual_branches']==62500000
            and max(maxima.values())<=best,'Every original pure-Phi5 choice retains all exponent tails')
    require(branch(witness['layout'],witness['projection'])==witness and witness['adopted']==best,
            'The maximizing certificate bound recomputes exactly, without actual attainment')
    final_branch=dict(witness)
    final_branch['projection21_35_63_105_147_245']=final_branch.pop('projection')
    return {'scanner_kind':'pure-factorial-complete-conditional','coefficients':{},'complete_cost_upper':best,
            'counts':counts,'covered_containing_choices':62500000,'seed_upper':seed_upper,'seed_records':seeds,
            'maximizing_certificate_branch':final_branch,'complete_tail_constant':witness['constant'],
            'independent_affine_checks':0,'maximum_pruned':maxima,'new_distinct_duals':len(problem.used-used_before),
            'all_branch_decisions_sha256':digest.hexdigest()}


def conditional_factorial_scan(problem,j,shift,conditional,co,seed_branches,label):
 require(co and len(seed_branches)==30 and len({(tuple(r['layout']),tuple(r['projection']))for r in seed_branches})==30,
         'Thirty original independent seeds for a nonempty original hinge sum')
 layouts=set(j.layouts())
 projections=set(product(range(2),range(5),range(5),range(2),range(5),range(2),range(5)))
 require(all(tuple(r['layout'])in layouts and tuple(r['projection'])in projections for r in seed_branches),
         'Every supplied seed has original independent containing labels')
 head=problem.head;prepared=head.prepare(co);six=problem.prepare_six(prepared)
 scale=prepared['factor']/j.TOTAL;problem.scale=scale
 require(scale>0,'Positive exact scale for the unchanged complete hinge compiler')
 independent=head.check_compiler(prepared);started=perf_counter();digest=sha256();used_before=set(problem.used)
 def affines(layout,projection):
  B=head.bridge.head_load(layout);correction=head.correction(prepared,B)
  r,s,c,rr,ss,r2,s2=projection
  extra=tuple(int(j.ROOT[a]==r)+int(b==s) for a,b in product(range(5),repeat=2))
  first=tuple(v+int(a==c)+int(j.ROOT[a]==rr and b==ss) for v,(a,b) in zip(extra,product(range(5),repeat=2)))
  second=tuple(int(j.ROOT[a]==r2)+int(b==s2) for a,b in product(range(5),repeat=2))
  return (problem.affine(prepared,B,extra,correction,False,layout),
    problem.affine(prepared,B,first,correction,True,layout),
    problem.affine(six,B,tuple(zip(first,second)),correction,True,layout))
 def refine(lines,projection):
  zz=conditional.endpoints(tuple(projection));delta=tuple(problem.fc*(v-F(89,240))/scale for v in zz)
  require(max(delta)<=0,'Every conditional PZZ endpoint improves the old complete cap')
  return tuple(tuple(a+b for a,b in zip(line,delta)) for line in lines)
 def record(layout,projection,lines):
  original,original_x,_=shift.max_min_affines(lines)
  refined=refine(lines,projection);value,x,_=shift.max_min_affines(refined)
  joint,key,const=problem.dual_upper(co,layout,projection)
  return {'layout':layout,'projection21_35_63_105_147_245':projection,
    'original_affine_complete_upper':scale*original,'original_affine_maximizing_late_coordinate':original_x,
    'conditional_affine_complete_upper':scale*value,'conditional_affine_maximizing_late_coordinate':x,
    'conditional_lines':refined,'joint_complete_upper':joint,'adopted_complete_upper':min(scale*value,joint),
    'dual_key':key,'complete_tail_constant':const}
 best=F(-1);witness=None;seed_records=[]
 for seed in seed_branches:
  lay=tuple(seed['layout']);proj=tuple(seed['projection']);row=record(lay,proj,affines(lay,proj))
  require(row['joint_complete_upper']==F(seed['upper']) and row['dual_key']==seed['key'],'Every exact scoped seed replays')
  seed_records.append(row)
  if row['adopted_complete_upper']>best:best=row['adopted_complete_upper'];witness=row
 initial=best
 for lay in ((0,1,2,0,2,1,2),(1,3,2,1,2,3,2)):
  for proj in ((0,1,2,1,3,0,4),(1,4,4,1,2,1,1)):
   lines=affines(lay,proj)
   for theta,x in ((j.LO,F(0)),(j.HI,F(1))):
    require(problem.rational_six(co,lay,proj,theta)==scale*(lines[2][0]+(lines[2][1]-lines[2][0])*x),'Unchanged whole original-cost affine compiler')
    independent+=1
 counts={k:0 for k in ('two_projection_branches','two_bounded','four_projection_branches','four_bounded','six_projection_branches','six_affine_bounded','conditional_affine_bounded','joint_dual_branches')}
 maxima={k:F(-1) for k in ('two','four','six','conditional')}
 for il,lay in enumerate(j.layouts()):
  B=head.bridge.head_load(lay);correction=head.correction(prepared,B)
  for r,s,extra in head.extras:
   two=problem.affine(prepared,B,extra,correction,False,lay);counts['two_projection_branches']+=1;upper=scale*max(two)
   if upper<=best:
    counts['two_bounded']+=1;maxima['two']=max(maxima['two'],upper);digest.update(repr(('two',lay,r,s,two)).encode());continue
   for c,rr,ss,added in head.added:
    first=tuple(a+b for a,b in zip(extra,added));four=problem.affine(prepared,B,first,correction,True,lay)
    val,_,_=j.max_min_affines(two,four);upper=scale*val;counts['four_projection_branches']+=1
    if upper<=best:
     counts['four_bounded']+=1;maxima['four']=max(maxima['four'],upper);digest.update(repr(('four',lay,r,s,c,rr,ss,two,four)).encode());continue
    for r2,s2,second in head.extras:
     proj=(r,s,c,rr,ss,r2,s2);line=problem.affine(six,B,tuple(zip(first,second)),correction,True,lay)
     lines=(two,four,line);val,_,_=shift.max_min_affines(lines);upper=scale*val;counts['six_projection_branches']+=1
     if upper<=best:
      counts['six_affine_bounded']+=1;maxima['six']=max(maxima['six'],upper);digest.update(repr(('six-affine',lay,proj,lines)).encode());continue
     refined=refine(lines,proj);val,_,_=shift.max_min_affines(refined);upper=scale*val
     if upper<=best:
      counts['conditional_affine_bounded']+=1;maxima['conditional']=max(maxima['conditional'],upper);digest.update(repr(('conditional-affine',lay,proj,lines,refined)).encode());continue
     row=record(lay,proj,lines);counts['joint_dual_branches']+=1
     digest.update(repr(('joint',lay,proj,lines,refined,row['dual_key'],str(row['joint_complete_upper']),str(row['complete_tail_constant']))).encode())
     if row['adopted_complete_upper']>best:best=row['adopted_complete_upper'];witness=row
  if il%2500==0:print('CONDITIONAL_SCAN',label,il,counts['joint_dual_branches'],round(perf_counter()-started,2),flush=True)
 require(counts['two_projection_branches']==125000 and counts['four_projection_branches']==50*(125000-counts['two_bounded'])
  and counts['six_projection_branches']==10*(counts['four_projection_branches']-counts['four_bounded'])
  and counts['joint_dual_branches']+counts['six_affine_bounded']+counts['conditional_affine_bounded']==counts['six_projection_branches']
  and 500*counts['two_bounded']+10*counts['four_bounded']+counts['six_projection_branches']==62500000
  and max(maxima.values())<=best,'Every62500000 independent original choice is covered with complete tails')
 lay=witness['layout'];proj=witness['projection21_35_63_105_147_245'];lines=affines(lay,proj)
 require(record(lay,proj,lines)==witness and witness['adopted_complete_upper']==best,'Exact maximizing containing certificate; no actual attainment')
 for x in (F(0),F(1),witness['conditional_affine_maximizing_late_coordinate']):
  theta=j.LO+(j.HI-j.LO)*x
  require(problem.rational_six(co,lay,proj,theta)==scale*(lines[2][0]+(lines[2][1]-lines[2][0])*x),'Final witness compiler on full late interval')
  independent+=1
 return {'coefficients':co,'complete_cost_upper':best,'counts':counts,'covered_containing_choices':62500000,
  'seed_upper':initial,'seed_records':seed_records,'maximizing_certificate_branch':witness,'maximum_pruned':maxima,
  'independent_affine_checks':independent,'new_distinct_duals':len(problem.used-used_before),'all_branch_decisions_sha256':digest.hexdigest()}


def make_problem(base,j,core,pair,depth,second,moment,shift,generalized,prior244,prior251,
                 complete_pair_tail,threshold,conditional,payments,bank=None,proposer=None):
    """Fresh threshold-specific270 scanner with actual X/Y/V factorial crosses.

    The threshold is fixed before any part or objective cache is populated.
    All pruning lines are recomputed with the same complete original cost.
    """
    require(isinstance(threshold,int) and threshold>=1,'Positive integer factorial threshold, including square at one')
    problem=shift.make_problem(base,j,core,pair,depth,second,moment,prior244,prior251,
                               complete_pair_tail,bank=bank,proposer=proposer)
    require(problem.parts.cache_info().currsize==0,
            'Fresh threshold-specific instance before any cached factorial parts')
    problem.k=threshold
    original_objective=problem.objective
    problem.retain_zero7_cross=True

    @lru_cache(None)
    def cross_parts(self,layout,retain_zero7_cross):
        require(self.k==threshold,'The factorial threshold cannot change after construction')
        h=tuple(F(max(b-threshold+1,0))for b in self.head.bridge.head_load(layout));mom=self.mom
        z=tuple(w*v for w,v in zip(mom.w,h));p,d=mom.pre,mom.descendant
        coefficients=(max(sum(p[5*c+s]*z[5*c+s]for s in range(5))for c in range(5)),
            max(sum(d[5*c+s]*z[5*c+s]for c in range(5))for s in range(5)),
            max(sum(d[5*c+s]*z[5*c+s]for c in range(5)if j.ROOT[c]==r)for r,s in product(range(2),range(5))),
            max(a*b for a,b in zip(d,z)),max(z))
        old=sum(a*b for a,b in zip(coefficients,generalized.OLD_WEIGHTS))
        selected=sum(a*b for a,b in zip(coefficients,generalized.SELECTED_WEIGHTS)) if retain_zero7_cross else F(0)
        remaining=sum(a*b for a,b in zip(coefficients,generalized.REMAINING_WEIGHTS if retain_zero7_cross else generalized.OLD_WEIGHTS))
        require(old==mom.old_tail(z) and old==remaining+selected and min(old,selected,remaining)>=0,
                'Exact same-layout complete zero7 cross partition')
        endpoints=[]
        for theta in(j.LO,j.HI):
            residual=remaining+mom.old_tail(h)/5
            residual+=sum(weight*max(mom.lp(tuple(a*b for a,b in zip(mask,h)),theta)for mask in family)
                          for family,weight in zip(mom.masks[1:],generalized.RAW_MASK_WEIGHTS))
            require(residual>=0,'Nonnegative complete unretained cross endpoint')
            endpoints.append(residual)
        return {'h':h,'zero7_coefficients':coefficients,'old_zero7_cross':old,
                'selected_zero7_payment':selected,'remaining_zero7_cross':remaining,
                'complete_cross_residual_endpoints':tuple(endpoints)}

    def objective(self,co,layout,projection):
        require(self.k==threshold,'One fixed threshold per original-cost instance')
        obj,constant=original_objective(co,layout,projection)
        parts=self.cross_parts(layout,self.retain_zero7_cross);h=parts['h']
        c0,c1=parts['complete_cross_residual_endpoints'];old0,old1=(p[1]for p in self.parts(layout))
        obj[875]+=self.fc*((c1-c0)-(old1-old0));constant+=self.fc*(c0-old0)
        r,s,c63,r105,s105,r147,s245=projection
        for i,value in enumerate(h):
            c,k=divmod(i,5)
            first=int(j.ROOT[c]==r)+int(k==s)+int(c==c63)+int(j.ROOT[c]==r105 and k==s105)
            second_count=int(j.ROOT[c]==r147)+int(k==s245)
            positive7=self.fc*value*(F(1,5)+generalized.U1*first+generalized.U2*second_count)
            for mask in range(16):
                cell=16*i+mask;obj[cell]+=positive7
                if self.retain_zero7_cross:
                    obj[425+cell]+=self.fc*value*mask.bit_count()
                    for state,count in enumerate((1,1,2)):
                        obj[pair.V+400*state+cell]+=self.fc*value*count
        require(len(obj)==3306 and all(v>=0 for k,v in enumerate(obj)if k!=875),
                'Only the original common-theta secant coefficient may be signed')
        return obj,constant

    problem.cross_parts=MethodType(cross_parts,problem)
    problem.objective=MethodType(objective,problem)
    crossed_objective=problem.objective
    def pair_objective(self,co,layout,projection):
        obj,constant=crossed_objective(co,layout,projection)
        p0,p1=conditional.endpoints(tuple(projection))
        obj[875]+=self.fc*(p1-p0)
        constant+=self.fc*(p0-F(89,240)-payments['selected_POO_payment']-payments['selected_POZ_payment'])
        r,s,c63,r105,s105,r147,s245=projection
        for i in range(25):
            c,slot=divmod(i,5)
            first=int(j.ROOT[c]==r)+int(slot==s)+int(c==c63)+int(j.ROOT[c]==r105 and slot==s105)
            second_count=int(j.ROOT[c]==r147)+int(slot==s245)
            weight=F(1,5)+generalized.U1*first+generalized.U2*second_count
            for mask in range(16):
                cell=16*i+mask;count=mask.bit_count()
                obj[425+cell]+=self.fc*F(count*(count-1),2)
                obj[cell]+=self.fc*count*weight
                for state,n in enumerate((1,1,2)):
                    obj[pair.V+400*state+cell]+=self.fc*(count*n+F(n*(n-1),2))
                    obj[pair.U+400*state+cell]+=self.fc*n*weight
        require(len(obj)==3306 and isinstance(constant,F) and all(isinstance(v,F)for v in obj)
                and all(v>=0 for col,v in enumerate(obj)if col!=875),
                'All actual raw/survivor pair coefficients are nonnegative except the common secant coordinate')
        return obj,constant
    problem.objective=MethodType(pair_objective,problem)
    return problem
def inputs(base):
    require(PINS,'Exact final mathematical source pins')
    io=module('joint_pair_io',base/'certificate_io.py');core=module('joint_pair_core',base/'frontier/j_face_joint_selected_heads.py')
    read=lambda name:json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),object_pairs_hook=core.unique)
    prior244,prior251,source258,source265,source274,comparison=(read(name)for name in(
        'j_face_joint_selected_heads','j_face_retained135125_heads','j_face_coherent_positive7_pairs',
        'j_face_raw_prime_path_pairs','j_face_generalized_factorial_heads','j_face_generalized_factorial_complete_moment_cost_comparison'))
    pins=dict(PINS)
    for source in(prior244,prior251,source258,source265,source274,comparison):
        require(source['geometry']==source274['geometry'] and F(source['survivor_mass'])==F(3,20),
                'All source bounds use both identical entire actual saturated J faces')
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent complete mathematical source '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical input '+path)
    j=module('joint_pair_j',base/'frontier/j_face_coupled_seven_heads.py');pair=module('joint_pair_retained',base/'frontier/j_face_retained135125_heads.py')
    depth=module('joint_pair_depth',base/'frontier/second_depth_seven_comparison.py');second=module('joint_pair_second',base/'frontier/j_face_second_depth_retained_heads.py')
    moment=module('joint_pair_moment',base/'frontier/j_face_shared_square_factorial.py');shift=module('joint_pair_shift',base/'frontier/j_face_shifted_factorial_quadratic_heads.py')
    generalized=module('joint_pair_generalized',base/'frontier/j_face_generalized_factorial_heads.py')
    quad=module('joint_pair_quad',base/'frontier/whole_quadratic_same_head.py');inventory=module('joint_pair_inventory',base/'frontier/source_barrier_saturation.py')
    raw_paths=module('joint_pair_raw_paths',base/'frontier/j_face_raw_prime_path_pairs.py')
    joint=module('joint_pair_head',base/'frontier/j_face_joint_retained_square.py')
    coherent=module('joint_pair_coherent',base/'frontier/j_face_coherent_positive7_pairs.py')
    tails=module('joint_pair_tails',base/'frontier/complete_off_face_factorial_tail.py')
    engine=inventory.Experiment(base)
    require(all(path in pins and pins[path]==pin for path,pin in engine.pins.items()),'The full original52-cost function inventory is pinned')
    tags=[row['tag']for row in engine.specs+engine.quadratic_specs]+[('s',F(81,n*n))for n in range(1,7)]
    require(len(tags)==52,'All original cost functions remain')
    tail=moment.complete_tail(tails)
    require(encode(tail)==source258['original_complete_tail_partition'],'The complete original cofactor cap series before any retained-pair replacement')
    payments=pair_partitions(source265,coherent,tail)
    conditional=ConditionalPositiveSeven(j,moment,joint,raw_paths,source265)
    return {'io':io,'core':core,'j':j,'pair':pair,'depth':depth,'second':second,'moment':moment,'shift':shift,
            'generalized':generalized,'quad':quad,'engine':engine,'tags':tags,'pins':pins,'prior244':prior244,
            'prior251':prior251,'source265':source265,'source274':source274,'comparison':comparison,
            'payments':payments,'conditional':conditional}


def calculate(base,bank,seed_rows):
    data=inputs(base)
    require([(row['index'],row['threshold'])for row in seed_rows]==list(TARGETS),
            'Exactly original48/49, square and purePhi5 with explicit independent seeds')
    j,core,pair,depth,second,moment,shift,generalized=(data[k]for k in ('j','core','pair','depth','second','moment','shift','generalized'))
    previous={row['name']:F(row['upper'])for row in data['comparison']['results']}
    previous['factorial5']=next(F(row['upper'])for row in data['comparison']['basis']if row['name']=='factorial5')
    conditional,payments=data['conditional'],data['payments'];digest=sha256();rows=[];used=set();layouts_total=0
    partitions=generalized.check_partitions()
    for (index,k),seed in zip(TARGETS,seed_rows):
        name={-1:'square',-3:'factorial5'}.get(index,'cost-'+str(index))
        expansion=(square_expansion() if index==-1 else pure_factorial_expansion() if index==-3
                   else generalized.shifted_identity(data['engine'].source,data['quad'],data['tags'][index],k))
        require(expansion['factorial_threshold']==k,'The original function retains its own integer factorial threshold')
        split=generalized.all_tail_split(k)
        problem=make_problem(base,j,core,pair,depth,second,moment,shift,generalized,data['prior244'],data['prior251'],
                             F(4879,7200),k,conditional,payments,bank=bank)
        require(problem.specification==data['source274']['model'],'The entire unchanged3306-variable6354-inequality18-equality original source')
        problem.fc=expansion['factorial_coefficient'];problem.atone=expansion['at_one']
        count=0
        for layout in j.layouts():
            row={'name':name,'threshold':k,'layout':layout,'factorial_parts':problem.parts(layout),
                 'cross_components':problem.cross_parts(layout,True)}
            digest.update(json.dumps(encode(row),separators=(',',':')).encode());count+=1
        require(count==12500,'All original heads and complete threshold-specific cross components')
        layouts_total+=count
        if index==-3:
            scan=pure_factorial_scan(problem,conditional,seed['branches'])
        else:
            scan=conditional_factorial_scan(problem,j,shift,conditional,expansion['hinge_coefficients'],seed['branches'],name)
            scan['scanner_kind']='complete-conditional-two-four-six'
        upper=scan['complete_cost_upper']
        require(0<upper<previous[name] and scan['covered_containing_choices']==62500000
                and not problem.prior_used,
                'A strict complete improvement over275 without any hinge-only pruning')
        require(problem.used<=set(bank),'Every full original-cost dual is provided and checked exactly')
        used.update(problem.used);branch=scan['maximizing_certificate_branch']
        rows.append({'name':name,'original_cost_index':index if index>=0 else None,
                     'tag':{'kind':name} if index<0 else data['tags'][index],
                     'factorial_threshold':k,'expansion':expansion,'all_head_tail_split':split,
                     'scan':scan,'complete_cost_upper':upper,'previous_adopted_upper':previous[name],
                     'adopted_upper':upper,'improvement_over_previous':previous[name]-upper,
                     'maximizing_cross_components':problem.cross_parts(tuple(branch['layout']),True),
                     'maximizing_conditional_PZZ_endpoints':conditional.endpoints(tuple(branch['projection21_35_63_105_147_245']))})
        print('Complete joint pair '+name+' <= '+str(float(upper)),flush=True)
    kept={key:bank[key]for key in sorted(used)}
    encoded=problem.codec.encode_dual_bank(kept,inequality_count=6354,equality_count=18)
    require(problem.codec.decode_dual_bank(encoded,inequality_count=6354,equality_count=18)==kept,
            'The canonical exact dual bank retains precisely the consumed witnesses')
    return encode({'schema':'erdos7-j-face-joint-pair-factorial-heads-v1','source_sha256':data['pins'],
        'geometry':data['source274']['geometry'],'source_mass':F(1,4),'survivor_mass':F(3,20),'model':problem.specification,
        'original_cost_indices':[48,49],'outside_targets':['square','factorial5'],'factorial_thresholds':[3,2,1,5],
        'original_affine_pruning_pair_tail':F(4879,7200),'complete_positive7_hinge_tail':second.Z6,
        'cross_partitions':partitions,'pair_partitions':payments,'conditional_positive7':conditional.record,
        'original_head_count':12500,'threshold_layout_record_count':layouts_total,
        'cross_endpoint_record_count':2*layouts_total,'all_factorial_and_cross_components_sha256':digest.hexdigest(),
        'seed_rows':seed_rows,'results':rows,'encoded_rational_duals':encoded,'distinct_dual_count':len(kept),
        'rational_column_checks':3306*len(kept),'total_containing_choices':sum(row['scan']['covered_containing_choices']for row in rows),
        'total_independent_affine_checks':sum(row['scan']['independent_affine_checks']for row in rows),
        'scope':'Complete original costs48/49, original square and purePhi5 on both entire saturated actual J faces, with separate thresholds3/2/1/5 and all62500000 original choices per target. The same3306-variable source carries actual X/Y factorial crosses, the fifteen assigned retained old-old pairs on Y/V and all selected old-positive-seven pairs on X/U. Only their exact known cap payments are replaced; every complementary old-old and old-positive-seven tail remains. Conditional positive-seven pairs retain independent complete original tests at every depth, full265 raw prime paths and one convex common-theta secant; all12500 raw completions and5000 fixed projection combinations are reconstructed. Original full-cost two/four/six affine pruning first retains its entire old pair bound; once all projections are fixed, the three complete lines replace the same old PZZ cap by the conditional secant before exact joint dual checks. PurePhi5 uses no synthetic hinge: complete layout pruning retains the old pair tail, then conditional pruning changes only the complete PZZ bound at both endpoints before exact joint dual checks. No actual attainment, off-face extension, complete52-cost comparison, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
    modes=parser.add_mutually_exclusive_group();modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    parser.add_argument('--proposal',type=Path);args=parser.parse_args()
    require(args.proposal is None or args.write,'Only the writer accepts a proposal')
    require(not args.write or args.proposal is not None,'Writer requires complete canonical duals and original seeds')
    io=module('joint_pair_reader',args.base/'certificate_io.py');core=module('joint_pair_json',args.base/'frontier/j_face_joint_selected_heads.py')
    proposed=json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE),object_pairs_hook=core.unique)
    codec=module('joint_pair_codec',args.base/'frontier/retained135_heavy_comparison.py')
    bank=codec.decode_dual_bank(proposed['encoded_rational_duals'],inequality_count=6354,equality_count=18)
    result=calculate(args.base,bank,proposed['seed_rows'])
    if args.write:io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:require(result==proposed,'Every complete actual-pair factorial certificate field recomputes exactly')
    print('PASS complete original48/49, square and purePhi5;'+str(result['total_containing_choices'])+' original choices;'+str(result['distinct_dual_count'])+' exact3306-column duals; all conditional and retained pair tails.',flush=True)


if __name__=='__main__':
    try:main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError)as error:
        print('FAIL: '+str(error),file=sys.stderr);raise SystemExit(1)
