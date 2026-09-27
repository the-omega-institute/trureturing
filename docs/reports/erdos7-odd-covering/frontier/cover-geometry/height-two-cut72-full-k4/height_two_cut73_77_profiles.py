#!/usr/bin/env python3
"""Necessary normalized-cut inventories73..77 using the complete cut72 conditions.

Full root positions are retained. Shape rows quotient only full-root
permutations with equal active counts; canonical families then quotient all
three full-root positions. This is no actual-source realizability claim.
"""
from importlib.util import module_from_spec,spec_from_file_location
from itertools import combinations, product
from pathlib import Path
import argparse,json


def require(ok,message):
    if not ok:raise ValueError(message)


def load(path):
    spec=spec_from_file_location('_cut72_complete_profile_conditions',path)
    require(spec is not None and spec.loader is not None,'profile base module')
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod


def inventory(base,rawcut):
    profiles=[];shapes={};canonical={}
    for active in product((0,2,3,4),(0,3,4,5),(0,3,4,5),(0,3,4,5)):
        top=sum(3 if a==0 else n-a for a,n in zip(active,base.N))
        for public_cost in range(max(0,rawcut//7-top+1)):
            remainder=rawcut-7*(top+public_cost)
            if remainder<0 or remainder%2:continue
            private_total=remainder//2
            if active==base.N and public_cost+private_total<15:continue
            candidates=base.sorted_shapes(active,public_cost,private_total)
            if not candidates:continue
            key=base.profile_key(active,public_cost,private_total)
            item=dict(key=key,active=active,T=top,k=public_cost,Z=private_total,shape_count=len(candidates))
            profiles.append(item);shapes[key]=candidates
            canonical_active=(active[0],*sorted(active[1:]))
            canonical_key=base.profile_key(canonical_active,public_cost,private_total)
            if canonical_key not in canonical:
                canonical[canonical_key]=dict(key=canonical_key,active=canonical_active,T=top,k=public_cost,
                                              Z=private_total,shape_count=len(candidates),labelled_keys=[])
            require(canonical[canonical_key]['shape_count']==len(candidates),'full-root permutation count')
            canonical[canonical_key]['labelled_keys'].append(key)
    return dict(rawcut=rawcut,labelled_profile_count=len(profiles),canonical_profile_count=len(canonical),
                labelled_shape_count=sum(map(len,shapes.values())),
                canonical_shape_count=sum(v['shape_count'] for v in canonical.values()),
                profiles=profiles,canonical_profiles=list(canonical.values()),shapes=shapes,
                scope='Necessary integer profiles only. Exact canonical cut72 node-minimal child/root bounds, literal selected-pair costs and fully-active standalone bound retained. No actual-source realizability, universal law, Lean or odd-covering result is inferred.')


def support_obstructions(base, inventories):
    result={}
    for raw,inv in inventories.items():
        classifications=[]
        for profile in inv['canonical_profiles']:
            for shape in inv['shapes'][profile['key']]:
                rows=[tuple(map(int,row)) if row!='-' else () for row in shape.split('/')]
                k=profile['k'];z=profile['Z'];reasons=[];witnesses={}
                if tuple(profile['active'])==base.N:
                    n3=sum(row.count(3) for row in rows)
                    cap=k+z+2*(k//3+n3)
                    if cap<25:
                        reasons.append('standalone_tree_capacity')
                        witnesses['standalone_tree_capacity']=dict(upper=cap,required=25,private_cost3_owners=n3)
                if k==5:
                    varying=[r for r,row in enumerate(rows) if row.count(1)>=3 and (r==0 or 0 in row)]
                    fixed={r:[list(cs) for cs in combinations(range(len(row)),base.Q[r])
                              if sum(row[c] for c in cs)==2]
                           for r,row in enumerate(rows)}
                    matches=[(v,r,t) for v in varying for r,t in combinations(range(4),2)
                             if v not in(r,t) and fixed[r] and fixed[t]]
                    if matches:
                        v,r,t=matches[0];reasons.append('public5_triangle')
                        witnesses['public5_triangle']=dict(varying_root=v,fixed_roots=[r,t],
                            fixed_child_indices=[fixed[r][0],fixed[t][0]])
                if k==0 and rows[0].count(2)>=3:
                    full=[r for r in range(1,4) if rows[r].count(1)>=1 and rows[r].count(2)>=3]
                    if full:
                        reasons.append('public0_singleton_double_parity')
                        witnesses['public0_singleton_double_parity']=dict(full_root=full[0])
                if k==1 and rows[0].count(2)>=3:
                    finite4={r:[list(cs) for cs in combinations(range(len(rows[r])),3)
                                 if sum(rows[r][c] for c in cs)==4 and max(rows[r][c] for c in cs)<=2]
                             for r in range(1,4)}
                    full=[r for r in finite4 if finite4[r]]
                    if len(full)>=2:
                        r,t=full[:2];reasons.append('public1_double_triangle')
                        witnesses['public1_double_triangle']=dict(full_roots=[r,t],
                            child_indices=[finite4[r][0],finite4[t][0]])
                if reasons:
                    classifications.append(dict(profile=profile['key'],shape=shape,reasons=reasons,witnesses=witnesses))
        result[raw]=dict(canonical_shape_rows=inv['canonical_shape_count'],
                        excluded_by_named_support_lemmas=len(classifications),rows=classifications,
                        scope='Applications of the separately stated ordinary actual-support impossibility lemmas; these predicates do not establish source realizability or laws for unexcluded rows.')
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-module',type=Path,default=Path(__file__).with_name('height_two_cut72_profiles.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.base_module)
    old=base.verify();repeated=inventory(base,72)
    for key in('labelled_profile_count','canonical_profile_count','labelled_shape_count','canonical_shape_count','shapes'):
        require(old[key]==repeated[key],'exact existing cut72 replay '+key)
    out={'cut72_replay':'all counts and all labelled shape lists agree',
         'inventories':{str(raw):inventory(base,raw) for raw in range(73,78)}}
    out['support_obstructions']=support_obstructions(base,out['inventories'])
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    for raw,rec in out['inventories'].items():
        print(json.dumps({k:rec[k] for k in('rawcut','labelled_profile_count','canonical_profile_count','labelled_shape_count','canonical_shape_count')}))


if __name__=='__main__':main()
