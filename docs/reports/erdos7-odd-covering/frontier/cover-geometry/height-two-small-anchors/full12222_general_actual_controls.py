#!/usr/bin/env python3
"""Five complete nonrobust source controls for the full12222 graph suppliers.

Reads only the named sibling helper and writes only --output. construct(name)
returns the complete original source and all fixed component laws for replay.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
import json
from pathlib import Path
import runpy

HELPER=runpy.run_path(str(Path(__file__).with_name('small_anchor_actual_controls.py')))
N,SELECT,D=(HELPER[k] for k in ('N','SELECT','DIVISORS'))
require,tree_exists,numerical_caps,original_integer=(HELPER[k] for k in
    ('require','tree_exists','numerical_caps','original_integer'))
R=1
P5=tuple(map(Q,('1','1/3','3/5','1/5','1/5','1/5','3/25','1/15','1/25')))
P4=tuple(map(Q,('1','1/3','3/4','1/5','1/4','1/4','3/20','1/12','1/20')))
OUTSIDE={0:(2,3),2:(2,4),3:(3,4)}
CONFIGS={
    'connected_four_edge_path':dict(fibres=({0},{1,2},{2,3},{3,4},{4,5}),
        colors=(0,0,1,0,1,0),anchors=((1,2,3),),mode='normalize5',
        shared=(0,2),eta_labels=(1,2,3,4),eta_owners=(1,2,3,4),weight=Q(495,647),
        owner_cap=Q(1,4),fine_cap=Q(1,4),column_cap=Q(3,4),bound=Q(5795,647)),
    'two_three_vertex_paths':dict(fibres=({0},{1,2},{1,3},{4,5},{4,6}),
        colors=(0,1,0,1,0,1,0),anchors=((0,1,2),(0,3,4)),mode='normalize5',
        shared=(0,1),eta_labels=tuple(range(7)),weight=Q(3,4),
        owner_cap=Q(2,7),fine_cap=Q(1,7),column_cap=Q(1),bound=Q(627,70)),
    'singleton_in_edge_three_disjoint':dict(fibres=({0},{0,1},{2,3},{4,5},{6,7}),
        colors=(0,1,0,1,0,1,0,1),anchors=((0,1,2),(0,1,3),(0,1,4)),mode='normalize5',
        shared=(2,3),eta_labels=tuple(range(8)),weight=Q(3,4),
        owner_cap=Q(1,4),fine_cap=Q(1,8),column_cap=Q(1),bound=Q(44,5)),
    'two_column_punctures_eight_labels':dict(fibres=({0},{1,2},{1,3},{4,5},{6,7}),
        colors=(0,0,1,1,0,0,1,1),anchors=((0,1,3),(1,2,4)),mode='whole_column',
        shared=(0,6),eta_labels=tuple(range(8)),bound=Q(44,5)),
    'four_distinct_owners_in_each_column':dict(fibres=({0},{1,2},{1,3},{4,5},{6,7}),
        colors=(0,0,1,1,0,1,0,1),anchors=((0,1,3),),mode='normalize4',
        shared=(0,3),bound=Q(35,4)),
}


def mixture(terms):
    result=defaultdict(Q)
    for weight,law in terms:
        for p,m in law.items(): result[p]+=weight*m
    return dict(result)


def label_map(colors):
    counts=[0,0];labels={}
    for v,g in enumerate(colors):
        labels[v]=(g,counts[g]);counts[g]+=1
    return labels,counts


def eta_labels(source,labels,owners=None,distinct=False):
    labels=list(labels)
    if owners is None:
        candidates=[[c for c in range(5) if label in source[R,c]] for label in labels]
        owners=next((cs for cs in product(*candidates) if not distinct or len(set(cs))==len(cs)),None)
    require(owners is not None,'actual owner assignment exists')
    return {(R,c,g,h):Q(1,len(labels)) for c,(g,h) in zip(owners,labels)}


def puncture(source,anchor,mode,serial,root_labels,delete_column=None):
    F=frozenset().union(*(source[R,c] for c in anchor))
    n=4 if mode=='normalize4' else 5
    require(len(anchor)==3,'whole original full-root legal restriction')
    if mode.startswith('normalize'):
        require(len(F)==(5 if n==4 else 4),'complete original anchor cardinality')
        require(all(sum(g==c for g,h in F)<=3 for c in range(7)),'normalizable complete anchor')
    else:
        require(delete_column in (0,1),'whole named column puncture')
        require(len([v for v in F if v[0]!=delete_column])<=1,'at most one exterior fine label')
    law=defaultdict(Q);tree_count=0
    for r,outer in OUTSIDE.items():
        restrictions=list(combinations(range(N[r]),SELECT[r]))
        for index,chosen in enumerate(restrictions):
            other=frozenset().union(*(source[r,c] for c in chosen))
            actual=F|other
            columns=(0,1,outer[(index+serial)%2])
            tree=set()
            for col in columns:
                available={v for v in actual if v[0]==col}
                require(len(available)>=3,'three actual leaves in each chosen branch')
                required={v for v in F if v[0]==col} if mode.startswith('normalize') else set()
                # Surviving original-R labels are preferred, then actual numerical labels.
                rest=sorted(available-required,key=lambda v:(v not in root_labels,v))
                branch=required|set(rest[:3-len(required)])
                require(len(branch)==3 and branch<=available,'actual normalized branch')
                tree.update(branch)
            require(len(tree)==9 and tree_exists(tree,3,3),'actual paired ternary tree')
            require(tree<=actual,'tree lies in unchanged original paired union')
            if mode=='whole_column':
                survivors={v for v in tree if v[0]!=delete_column and v not in F}
            else:
                survivors=tree-F
                require(all({v for v in F if v[0]==c}<=tree for c in columns),
                        'every occurring branch contains all its complete-F labels')
            leaves=sorted(survivors,key=lambda v:(v not in root_labels,v))[:n]
            require(len(leaves)==n and set(leaves)<=other,'all retained leaves have original other-root owners')
            owner=chosen[(index+serial)%len(chosen)]
            require(set(leaves)<=source[r,owner],'chosen actual original owner')
            for g,h in leaves: law[r,owner,g,h]+=Q(1,3*len(restrictions)*n)
            tree_count+=1
    law=dict(law)
    require(sum(law.values())==1,'each original-anchor law has mass one')
    require(all(r!=R and (g,h) not in F for r,c,g,h in law),'global complete-F exclusion and root separation')
    for g,h in F:
        require(sum(m for p,m in law.items() if original_integer(p)%49==g+7*h)==0,
                'original numerical49 complete-F exclusion')
    for col in range(7):
        mass=sum(m for (r,c,g,h),m in law.items() if g==col)
        if mode.startswith('normalize'):
            require(mass<=Q(3-sum(g==col for g,h in F),n),'normalized column deletion bound')
        elif col==delete_column:
            require(mass==0,'entire punctured column excluded')
    return {'anchor':anchor,'F':F,'mode':mode,'delete_column':delete_column,
            'law':law,'paired_trees':tree_count}


def construct(name):
    cfg=CONFIGS[name];labels,counts=label_map(cfg['colors'])
    source={(R,c):frozenset(labels[v] for v in f) for c,f in enumerate(cfg['fibres'])}
    for index,(r,cols) in enumerate(OUTSIDE.items()):
        extra={labels[cfg['shared'][0]],labels[cfg['shared'][1]],
               (0,counts[0]+index),(1,counts[1]+index)}
        require(all(0<=h<7 for g,h in extra),'original fine digits within0..6')
        fibre=frozenset({(g,h) for g in cols for h in range(5)}|extra)
        require(len(fibre)==14,'two outside branches and two fine labels in each head column')
        for c in range(N[r]): source[r,c]=fibre
    root_labels=frozenset().union(*(source[R,c] for c in range(5)))
    anchors=[puncture(source,a,cfg['mode'],i,root_labels,i if cfg['mode']=='whole_column' else None)
             for i,a in enumerate(cfg['anchors'])]
    laws={}
    for i,a in enumerate(anchors): laws['anchor_psi_'+str(i)]=a['law']
    if cfg['mode']=='whole_column':
        eta=eta_labels(source,[labels[v] for v in cfg['eta_labels']])
        laws['eta']=eta
        laws['lambda']=mixture([(Q(3,8),a['law']) for a in anchors])
        laws['pi']=mixture([(Q(1,4),eta)])
    elif cfg['mode']=='normalize4':
        psi=anchors[0]['law'];laws['psi']=psi
        laws['eta_H']=eta_labels(source,sorted(v for v in root_labels if v[0]==0),distinct=True)
        laws['eta_J']=eta_labels(source,sorted(v for v in root_labels if v[0]==1),distinct=True)
        laws['lambda']=mixture([(Q(31,50),psi)])
        laws['pi']=mixture([(Q(1,5),laws['eta_H']),(Q(9,50),laws['eta_J'])])
    else:
        psi=mixture([(Q(1,len(anchors)),a['law']) for a in anchors]);laws['psi']=psi
        eta=eta_labels(source,[labels[v] for v in cfg['eta_labels']],cfg.get('eta_owners'))
        laws['eta']=eta
        laws['lambda']=mixture([(cfg['weight'],psi)])
        laws['pi']=mixture([(1-cfg['weight'],eta)])
    laws['nu']=mixture([(Q(1),laws['lambda']),(Q(1),laws['pi'])])
    return {'name':name,'config':cfg,'source':source,'label_map':labels,
            'root_labels':root_labels,'anchors':anchors,'laws':laws}


def conditional_cap(name,d,category,component):
    outside=category==2
    if name=='two_column_punctures_eight_labels':
        if component=='nu':
            return (Q(9,20) if outside else Q(7,20)) if d==7 else (Q(3,20) if outside else Q(17,160))
        if component=='lambda':
            if d==5:return Q(1,4)
            if d==25:return Q(3,20)
            return {35:Q(3,40),175:Q(9,200),245:Q(1,40),1225:Q(3,200)}[d]*(2 if outside else 1)
        if d==5:return Q(1,4)
        if d==25:return Q(1,16)
        return Q(0) if outside else {35:Q(1,8),175:Q(1,16),245:Q(1,32),1225:Q(1,32)}[d]
    w,h,j=Q(31,50),Q(1,5),Q(9,50)
    if component=='nu':
        return (h,w/4+j,3*w/4)[category] if d==7 else (h/4,w/4+j/4,w/4)[category]
    if component=='lambda':
        if d==5:return w/3
        if d==25:return w/5
        if category==0:return Q(0)
        return {35:(w/12,w/4),175:(w/20,3*w/20),245:(w/12,w/12),1225:(w/20,w/20)}[d][outside]
    if d==5:return h+j
    if d==25:return (h+j)/4
    if d==35:return (h,j,Q(0))[category]
    return (h/4,j/4,Q(0))[category]


def validate(rec):
    cfg,source,laws=rec['config'],rec['source'],rec['laws']
    require(len(source)==19 and all(source.values()),'all original19 nonempty fibres')
    projected={r:[frozenset().union(*(source[r,c] for c in cs))
                  for cs in combinations(range(N[r]),SELECT[r])] for r in range(4)}
    pairs=0
    for r,s in combinations(range(4),2):
        for f,g in product(projected[r],projected[s]):
            require(tree_exists(f|g,3,3),'every original complete legal pair')
            pairs+=1
    require(pairs==480,'all480 original pair restrictions')
    require(tree_exists(frozenset().union(*source.values()),5,5),'actual standalone five-tree')
    require(all(not all(tree_exists(f,3,3) for f in projected[r]) for r in range(4)),
            'no individually robust root')
    raw_caps={};cylinders=0
    for name,law in laws.items():
        require(all(m>0 and (g,h) in source[r,c] for (r,c,g,h),m in law.items()),name+' actual original support')
        if name not in ('lambda','pi'):require(sum(law.values())==1,name+' probability')
        caps,count=numerical_caps(law);raw_caps[name]=caps;cylinders+=count
        if name.startswith('anchor_psi_') or name=='psi':
            bound=P4 if cfg['mode']=='normalize4' else P5
            require(all(x<=y for x,y in zip(caps,bound)),name+' original simultaneous puncture caps')
    require(sum(laws['lambda'].values())+sum(laws['pi'].values())==1,'fixed component total')
    table_checks=0
    if cfg['mode']=='normalize5':
        w=cfg['weight'];v=1-w
        require(all(x<=w*y for x,y in zip(raw_caps['lambda'],P5)),'scaled P5 law')
        owner,fine,col=cfg['owner_cap'],cfg['fine_cap'],cfg['column_cap']
        pi_caps=(v,v,v*col,v*owner,v*col,v*fine,v*owner,v*fine,v*fine)
        require(all(x<=y for x,y in zip(raw_caps['pi'],pi_caps)),'same actual eta component caps')
        require(raw_caps['nu'][2]<=3*w/5 and raw_caps['nu'][5]<=w/5,'same-law pure7 and49 caps')
    else:
        for component in ('lambda','pi','nu'):
            for d in (tuple(d for d in D if d%5==0) if component!='nu' else (7,49)):
                values=[Q(0)]*d
                for p,m in laws[component].items():values[original_integer(p)%d]+=m
                for residue,m in enumerate(values):
                    col=residue%7;cat=col if col in (0,1) else 2
                    if component=='lambda' and residue%5==R:require(m==0,'lambda R support exclusion')
                    elif component=='pi' and residue%5!=R:require(m==0,'pi original R support')
                    else:require(m<=conditional_cap(rec['name'],d,cat,component),'root/category numerical cap')
                    table_checks+=1
    overlap=[]
    for g,h in sorted(rec['root_labels']):
        left=sum(m for (r,c,gg,hh),m in laws['lambda'].items() if (gg,hh)==(g,h))
        right=sum(m for (r,c,gg,hh),m in laws['pi'].items() if (gg,hh)==(g,h))
        if left>0 and right>0:overlap.append({'original49_residue':g+7*h,'lambda':str(left),'pi':str(right)})
    if cfg['mode'] in ('whole_column','normalize4'):
        require(overlap,'actual common fine support has positive mass in both lambda and pi')
    if cfg['mode']=='whole_column':
        require(len(overlap)==2,'both named columns exercise shared fine mass')
        require(all(Q(v['lambda'])==Q(3,40) and Q(v['pi'])==Q(1,32) for v in overlap),
                'dual puncture saturates safe shared-fine cap17/160')
    if cfg['mode']=='normalize4':
        marker=rec['label_map'][3]
        require(sum(m for (r,c,g,h),m in laws['psi'].items() if (g,h)==marker)==Q(1,4),
                'original R fine label receives psi1/4 and positive eta mass')
    return {'name':rec['name'],'actual_points':sum(map(len,source.values())),
            'original_owners':len(source),'original_pair_checks':pairs,'standalone':True,
            'no_individually_robust_root':True,'paired_tree_constructions':sum(a['paired_trees'] for a in rec['anchors']),
            'numerical_cylinders':cylinders,'root_category_table_checks':table_checks,
            'raw_caps':{k:list(map(str,v)) for k,v in raw_caps.items()},'shared_fine_support':overlap,
            'query_bound_from_separate_certificate':str(cfg['bound']),
            'source':[{'root':r,'child':c,'whole_fibre':sorted(f)} for (r,c),f in sorted(source.items())],
            'component_laws':{name:[{'point':p,'mass':str(m)} for p,m in sorted(law.items())] for name,law in laws.items()}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    controls=[validate(construct(name)) for name in CONFIGS]
    require(len(controls)==5 and all(c['actual_points']==205 for c in controls),'five complete205-point sources')
    result={'status':'PASS','controls':controls,
            'scope':'Complete-source construction controls. No exhaustive source enumeration, minimum-cut, Lean, arbitrary-height or unrestricted covering claim.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','sources':len(controls),
                      **{k:sum(c[k] for c in controls) for k in
                         ('original_pair_checks','paired_tree_constructions','numerical_cylinders','root_category_table_checks')},
                      'positive_overlap_controls':sum(bool(c['shared_fine_support']) for c in controls)}))


if __name__=='__main__':main()
