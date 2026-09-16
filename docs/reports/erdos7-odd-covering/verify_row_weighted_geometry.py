#!/usr/bin/env python3
"""Verify a same-carrier change of row law across the uniform35 profile boundary.

Reconstructs the actual77point original-label family, an affine separator
for its uniform sufficient criterion, a positive shared-row law satisfying
both exact signed35 criteria, and all support-inclusion coverage. Uses only
canonical adjacent modules and certificates. No optimizer is a dependency.
"""
from pathlib import Path
from itertools import product
from fractions import Fraction as F
from math import gcd,lcm
from hashlib import sha256
import argparse
import importlib.util
import json
import numpy as np

SCHEMA='erdos7-row-weighted-geometry-v1'
SHAPE='root1_same_other_column'
GEOMETRY='actual_deletion_profile_certificate.json'
BOX='uniform_profile_box_certificate.json'

def require(ok,why):
    if not ok:raise ArithmeticError(why)

def module(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def weighted_squares(cache,r,w):
    values=np.empty((2,270),dtype=np.int64);roots=cache['roots'];R=r*w;n=len(r)
    cuts=[[None]*270 for _ in range(2)]
    witnesses=[[None]*270 for _ in range(2)]
    bound=64*n*77*77*int(w.max());require(bound<2**53,'exact weighted square binary64 integer range')
    for k,(z3,z5) in enumerate(product(range(9),range(6))):
        A=cache['loads'][k];s=(z3+1)*(z5+1);B=A.reshape(-1,n,n)[:,0,:].copy();B[:,0]-=s
        base=(A*A)@R;dot=(A*w).astype(float)@B.astype(float).T;qn=(B*B)@w
        for z7 in range(5):
            u=z7+1;matrix=2*u*dot+u*u*qn[None,:];inc=np.zeros_like(matrix)
            for j in range(n):
                np.maximum(inc,int(w[j])*(2*u*s*A[:,j,None]+u*u*(2*s*B[None,:,j]+s*s)),out=inc)
            score=base+(matrix+inc).max(axis=1)
            require(np.all(score==np.rint(score)) and float(score.max())<bound,'exact weighted integer scores')
            for j,root in enumerate((1,2)):
                allowed=np.flatnonzero(roots==root);ai=int(allowed[int(score[allowed].argmax())]);bi=int((matrix[ai]+inc[ai]).argmax())
                bj=int((w*(2*u*s*A[ai]+u*u*(2*s*B[bi]+s*s))).argmax());fullB=B[bi].copy();fullB[bj]+=s
                cv=r*A[ai]*A[ai]+2*u*A[ai]*fullB+u*u*fullB*fullB
                values[j,5*k+z7]=int(score[ai]);require(int(cv@w)==int(score[ai]),'weighted active square cut witness')
                cuts[j][5*k+z7]=tuple(map(int,cv))
                witnesses[j][5*k+z7]={"A":A[ai].tolist(),"B":fullB.tolist()}
    return values,bound,witnesses


def layouts(xs):
    n=len(xs);mods=(3,5,9,15)
    choices=list(product(*(sorted({x%d for x in xs}) for d in mods)))
    features=np.array([[[int(x%d==a) for x in xs] for d,a in zip(mods,row)] for row in choices],dtype=np.int64)
    loads=[]
    for z3,z5 in product(range(9),range(6)):
        L=1+np.einsum('ajn,j->an',features,np.array([1,1+z5,1+z3,1+z5],dtype=np.int64))
        s=(z3+1)*(z5+1)
        loads.append((L[:,None,:]+s*np.eye(n,dtype=np.int64)[None,:,:]).reshape(-1,n))
    return {'loads':loads,'roots':np.repeat([row[0] for row in choices],n)}


def measure_result(xs,profile,points,weights,cache,pg,up,geo):
    r=np.array([6-b for b in profile],dtype=np.int64);w=np.array(weights,dtype=np.int64)
    denominator=int(r@w);ri=np.array([xs.index(int(x%45)) for x in points]);point_weights=w[ri]
    require(int(point_weights.sum())==denominator,'same actual-law normalizer')
    divisors,_,_,rho,depths,prob,beta,tail_coeff=pg.coeffs((8,5,4));rho[divisors.index(35)]-=F(1,4)
    require(min(rho)>=0 and min(tail_coeff)>=0 and 0<beta<1,'complete nonnegative remainders')
    effective=prob.copy();effective[0]+=1-beta
    values,bound,witnesses=weighted_squares(cache,r,w)
    factors=[[1]*len(xs)]+[[34-3*int(x%3==root) for x in xs] for root in (1,2)]
    caps=[];groups=[]
    for factor in factors:
        f=np.array(factor,dtype=np.int64)
        caps.append(up.caps(point_weights*f[ri],points,divisors))
        groups.append(up.profile_group_bound_numerator(xs,profile,(w*f).tolist()))
    q=1-F(groups[0]['numerator48'],48*denominator)-sum((F(m,denominator)*e for m,e in zip(caps[0],rho)),F())
    tail=sum((F(m,denominator)*e for m,e in zip(caps[0],tail_coeff)),F());roots=[]
    for j,root in enumerate((1,2)):
        U=sum((p*F(int(v),denominator) for p,v in zip(effective,values[j])),F())+tail
        R=F(groups[j+1]['numerator48'],48*denominator)+sum((F(m,denominator)*e for m,e in zip(caps[j+1],rho)),F())
        roots.append({'root':root,'moment_upper':str(U),'weighted_deletion_upper':str(R),
                      'signed_margin':str(35-U-R),'depth_numerators':values[j].tolist(),
                      'active_layouts_sha256':geo.digest(witnesses[j])})
    result={'normalizer':denominator,'survival_lower':str(q),'square_integer_bound':bound,
            'cap_numerators':caps,'row_count_group_bounds':groups,'roots':roots}
    return result,witnesses,(divisors,rho,depths,effective,tail_coeff)


def separator(xs,profile,uniform,witnesses,coefficients):
    r=[6-b for b in profile];n=len(xs);ds,rho,depths,pw,eo=coefficients
    slope=[F(-35) for _ in xs];constant=F()
    for probability,depth,witness in zip(pw,depths,witnesses[1]):
        A=witness['A'];B=witness['B'];u=depth[2]+1
        for j in range(n):slope[j]+=probability*A[j]*A[j]
        constant+=probability*sum(2*u*a*b+u*u*b*b for a,b in zip(A,B))
    h=[34-3*int(x%3==2) for x in xs]
    def cap_residue(f,d):
        co=d//7 if d%7==0 else d
        vals=[sum((1 if d%7==0 else ri)*fi for x,ri,fi in zip(xs,r,f) if x%co==a) for a in range(co)]
        return max(range(co),key=lambda a:vals[a])
    for d,et,rr in zip(ds,eo,rho):
        for factor,f in ((et,[1]*n),(rr,h)):
            a=cap_residue(f,d);co=d//7 if d%7==0 else d
            for j,x in enumerate(xs):
                if x%co==a:
                    if d%7==0:constant+=factor*f[j]
                    else:slope[j]+=factor*f[j]
    g=uniform['row_count_group_bounds'][2];a9,a45=g['A_residues']
    for j,x in enumerate(xs):
        A=int(x%9==a9)+int(x%45==a45)
        B=sum(x%d==a for d,a in zip((5,15,45),g['B_residues']))
        slope[j]+=F(h[j]*(24*A+6*(2-A)*B),48)
    constant+=F(g['extra']+sum(g['E7_terms']),48)
    value=sum((a*ri for a,ri in zip(slope,r)),constant)
    require(value==-F(uniform['roots'][1]['signed_margin'])*sum(r) and value>0,
            'strict active support separation from the uniform35 criterion')
    den=lcm(*(x.denominator for x in slope+[constant]));ints=[int(x*den) for x in slope+[constant]]
    common=gcd(*map(abs,ints));ints=[x//common for x in ints]
    return {'root':2,'slope':[str(x) for x in slope],'constant':str(constant),
            'integer_slope':ints[:-1],'integer_constant':ints[-1],'value_at_source':str(value)}


def uniform_group_attainment(xs,points,groups):
    results=[]
    for root,g in zip((0,1,2),groups):
        f={x:1 if root==0 else 34-3*int(x%3==root) for x in xs}
        extra=next(a for a in range(35) if a%7==1 and a%5==g['extra_old5_residue'])
        high=[]
        for c,a in zip((1,3,5,9,15,45),g['E7_old_residues']):
            high.append([7*c,next(z for z in range(7*c) if z%c==a and z%7==6)])
        total=0
        for x in points:
            A=sum(x%d==a for d,a in zip((9,45),g['A_residues']))
            B=sum(x%d==a for d,a in zip((5,15,45),g['B_residues']))
            E=int(x%35==extra);C=sum(x%d==a for d,a in high);T=2-A
            total+=f[int(x%45)]*(24*A+6*T*B+6*T*E+T*(4-B-E)*C)
        require(total==g['numerator48'],'actual original-cylinder equality in uniform UP1')
        results.append({'weight_root':root,'extra35_residue':extra,'E7_classes':high,
                        'numerator48':int(total)})
    return results


def evaluate(data,directory):
    require(type(data) is dict and data.get('schema')==SCHEMA and data.get('target')=='35',
            'row-weighted geometry contract')
    require(sha256((directory/GEOMETRY).read_bytes()).hexdigest()==data.get('geometry_sha256'),
            'actual old-shape geometry fingerprint')
    require(sha256((directory/BOX).read_bytes()).hexdigest()==data.get('uniform_box_sha256'),
            'uniform-box coverage baseline fingerprint')
    pg=module('row_law_point',directory/'verify_point_geometry.py')
    up=module('row_law_uniform',directory/'verify_uniform_profile_geometry.py')
    geo=module('row_law_classification',directory/'verify_seven_digit_classification.py')
    dom=module('row_law_dominance',directory/'verify_carrier_dominance.py')
    old_case=next(row for row in geo.read_geometries(directory/GEOMETRY) if row['shape']==SHAPE)
    xs=old_case['old_points'];family=data.get('family');weights=data.get('row_weight_numerators')
    require(type(family) is list and len(family)==11,'all original low labels')
    for pair in family:
        require(type(pair) is list and len(pair)==2 and all(type(x) is int for x in pair)
                and pair[0]>1 and 0<=pair[1]<pair[0],'original low cylinder syntax')
    require({d for d,a in family}=={d for d in range(2,316) if 315%d==0} and [7,0] in family,
            'distinct complete original labels and normalized7 exclusion')
    require([row for row in family if row[0]%7]==old_case['old_classes'],'canonical old classes')
    require(type(weights) is list and len(weights)==len(xs)
            and all(type(w) is int and 0<w<=2**31 for w in weights),'positive old-row integer masses')
    points=np.array([x for x in range(315) if all(x%d!=a for d,a in family)],dtype=np.int64)
    profile=[6-sum(int(y%45)==x for y in points) for x in xs]
    masks=[sum(1<<i for i,x in enumerate(xs) if not any(int(y%45)==x and int(y%7)==digit for y in points))
           for digit in range(1,7)]
    state=tuple(sorted(m for m in masks if m))
    require(len(points)==77 and masks[-1]==0 and state==(1,2081,9225,41604,93629),
            'specified actual77point source carrier')
    widths=[max(sum(x%d==a for x in xs) for a in range(d)) for d in (3,5,9,15,45)]
    require(6*len(xs)-sum(widths)==len(points),'global minimum cardinality gives actual inclusion-minimality')
    cache=layouts(xs)
    uniform,uwitnesses,coeff=measure_result(xs,profile,points,[1]*len(xs),cache,pg,up,geo)
    law,_,_=measure_result(xs,profile,points,weights,cache,pg,up,geo)
    require(F(law['survival_lower'])>0 and all(F(row['signed_margin'])>0 for row in law['roots']),
            'strict35 criterion and positive survival on the same actual row law')
    r=[6-b for b in profile];normalizer=law['normalizer']
    require(all(F(17,20*len(points))<=F(w,normalizer)<=F(23,20*len(points)) for w in weights),
            'all point densities remain within15percent of the source uniform law')
    plane=separator(xs,profile,uniform,uwitnesses,coeff)
    attainment=uniform_group_attainment(xs,points,uniform['row_count_group_bounds'])

    maps=geo.old_maps(xs)
    require(all(xs[p[i]]%3==xs[i]%3 for p in maps for i in range(len(xs))),
            'old transports preserve both named original roots')
    states,_,_=geo.digit_union_states(xs)
    require(len(states)==old_case['digit_union_states'],'all actual carriers reconstructed')
    sources={tuple(sorted(geo.image_mask(u,p) for u in state)) for p in maps}
    require(sources<=states and len(dom.carrier_orbits(sources,maps,geo))==1,'one source orbit')
    used={u for s in states for u in s}
    edges=[{b:sum(1<<j for j,a in enumerate(s) if b&~a==0) for b in used} for s in sorted(sources)]
    covered={s for s in states if any(dom.injection(tuple(sorted(e[b] for b in s))) for e in edges)}
    box_cert=json.loads((directory/BOX).read_text());bc=box_cert['result']
    require(bc['shape']==SHAPE and bc['old_points']==xs,'same old geometry for coverage comparison')
    images={tuple(p) for p in bc['profile_images']}
    box={s for s in states if any(all(a<=b for a,b in zip(geo.deletion_vector(s,len(xs)),p)) for p in images)}
    require(len(box)==bc['actual_geometry']['covered_states']
            and len(dom.carrier_orbits(box,maps,geo))==bc['actual_geometry']['covered_orbits'],
            'independently reconstructed uniform-box coverage')
    require(not (sources&box),'new minimal source lies outside the uniform box')
    overlap=covered&box;additional=covered-box;union=covered|box
    reps=dom.carrier_orbits(covered,maps,geo);extra_reps=dom.carrier_orbits(additional,maps,geo)
    coverage={'source_states':len(sources),'source_orbits':1,'covered_states':len(covered),
              'covered_orbits':len(reps),'overlap_box_states':len(overlap),
              'overlap_box_orbits':len(dom.carrier_orbits(overlap,maps,geo)),
              'additional_states':len(additional),'additional_orbits':len(extra_reps),
              'additional_minimal_orbits':1,'union_states':len(union),
              'union_orbits':len(dom.carrier_orbits(union,maps,geo)),
              'covered_orbits_sha256':geo.digest(reps),'additional_orbits_sha256':geo.digest(extra_reps)}
    return {'shape':SHAPE,'old_points':xs,'actual_points':points.tolist(),'deletion_profile':profile,
            'deletion_masks':list(state),'maximum_mixed_cylinder_sizes':widths,
            'uniform_reference':uniform,'uniform_affine_separator':plane,
            'uniform_group_attainment':attainment,'weighted_law':law,'support_coverage':coverage}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--write',type=Path)
    parser.add_argument('--check',type=Path)
    parser.add_argument('--input',type=Path,help='specified original family and integer row law for writer')
    args=parser.parse_args();require(not(args.write and args.check),'writer or replay')
    if args.write:
        require(args.input is not None,'writer needs the specified family and row law')
        raw=json.loads(args.input.read_text())
        data={'schema':SCHEMA,'target':'35','family':raw['family'],
              'row_weight_numerators':raw['row_weight_numerators'],
              'geometry_sha256':sha256((args.directory/GEOMETRY).read_bytes()).hexdigest(),
              'uniform_box_sha256':sha256((args.directory/BOX).read_bytes()).hexdigest()}
        data['result']=evaluate(data,args.directory)
        args.write.write_text(json.dumps(data,indent=2)+'\n')
    else:
        path=args.check or args.directory/'row_weighted_geometry_certificate.json'
        data=json.loads(path.read_text());require(evaluate(data,args.directory)==data['result'],'complete row-law certificate replay')
    result=data['result']
    print(json.dumps({'schema':SCHEMA,'survival_lower':result['weighted_law']['survival_lower'],
                      'root_margins':[r['signed_margin'] for r in result['weighted_law']['roots']],
                      'support_coverage':result['support_coverage']},sort_keys=True))


if __name__=='__main__':main()
