#!/usr/bin/env python3
"""Exact separation of all independent original divisors of 5*7**K.

Tree DP state: a subtree, four inherited row loads, and a mask assigning
individual future original divisor labels to that subtree. No phases are
required to have a common prefix. Standard library, arbitrary-size integer
arithmetic. Optional cached-state/subset-candidate limits raise an error,
never return a bound; neither is a total-work or memory limit.
"""
from functools import lru_cache
from fractions import Fraction as F
from itertools import product
from time import monotonic

ROWS=(1,2,3,4)

class ResourceLimitError(RuntimeError):
    pass


def need(ok,message):
    if not ok:raise ValueError(message)


class IndependentLayoutTreeDP:
    def __init__(self,height,points):
        need(type(height) is int and height>=0,'nonnegative literal height required')
        need(type(points) in (tuple,list) and points,'nonempty point sequence required')
        need(all(type(p) in (tuple,list) for p in points),'point pairs required')
        self.height=height
        self.points=tuple(tuple(p) for p in points)
        need(all(len(p)==2 and type(p[0]) is int and p[0] in ROWS and type(p[1]) is int
                 and 0<=p[1]<7**height for p in self.points),'literal four-row carrier points required')
        need(len(set(self.points))==len(self.points),'duplicate source points')

    def separate(self,weights,max_states=None,max_operations=None):
        """Return an exact maximum and one actual attaining original layout.

        max_states counts created memo entries. max_operations counts subset
        convolution candidates, including reconstruction. These limits do not
        bound all arithmetic work or memory; a single-child tree can perform
        substantial state work while evaluating zero subset candidates.
        """
        need(type(weights) in (tuple,list) and len(weights)==len(self.points)
             and all(type(w) is int and w>=0 for w in weights) and sum(weights)>0,
             'nonnegative integer weights with positive sum required')
        for limit in (max_states,max_operations):
            need(limit is None or (type(limit) is int and limit>0),'positive literal resource limit required')
        started=monotonic();K=self.height
        nodes={};state_count=0;operations=0;misses_by_depth=[0]*(K+1)
        for (r,y),w in zip(self.points,weights):
            if not w:continue
            for d in range(K+1):
                key=(d,y%7**d)
                if key not in nodes:nodes[key]=[[],[0]*4]
                nodes[key][1][r-1]+=w
        for d,y in nodes:
            if d:nodes[d-1,y%7**(d-1)][0].append((d,y))
        for children,_ in nodes.values():children.sort()

        def budget(state=False):
            nonlocal state_count,operations
            if state:
                state_count+=1
                if max_states is not None and state_count>max_states:
                    raise ResourceLimitError('state limit exceeded; separation incomplete')
            else:
                operations+=1
                if max_operations is not None and operations>max_operations:
                    raise ResourceLimitError('operation limit exceeded; separation incomplete')

        def convolution(left,right):
            size=len(left);out=[0]*size
            for mask in range(size):
                best=-1;sub=mask
                while True:
                    budget();value=left[mask^sub]+right[sub]
                    if value>best:best=value
                    if sub==0:break
                    sub=(sub-1)&mask
                out[mask]=best
            return tuple(out)

        @lru_cache(None)
        def combine(node,loads):
            budget(state=True)
            children=nodes[node][0]
            need(children,'internal combination requested at leaf')
            result=table(children[0],loads)
            for child in children[1:]:result=convolution(result,table(child,loads))
            return result

        @lru_cache(None)
        def table(node,loads):
            budget(state=True);d,prefix=node;misses_by_depth[d]+=1
            if d==K:
                row_weights=nodes[node][1]
                base=sum(w*v*v for w,v in zip(row_weights,loads))
                pure=sum(w*(v+1)**2 for w,v in zip(row_weights,loads))
                mixed=base+max(w*(2*v+1) for w,v in zip(row_weights,loads))
                both=pure+max(w*(2*v+3) for w,v in zip(row_weights,loads))
                return (base,pure,mixed,both)
            tails=1<<(2*(K-d));result=[-1]*(4*tails)
            for pure in (0,1):
                base_loads=tuple(v+pure for v in loads)
                values=combine(node,base_loads)
                for mask,value in enumerate(values):result[4*mask+pure]=value
                for r in range(4):
                    row_loads=tuple(v+(a==r) for a,v in enumerate(base_loads))
                    values=combine(node,row_loads)
                    for mask,value in enumerate(values):
                        pos=4*mask+pure+2
                        if value>result[pos]:result[pos]=value
            return tuple(result)

        try:
            root=(0,0);fullmask=(1<<(2*K))-1
            if K==0:
                values=table(root,(0,0,0,0));numerator=values[3]
                winning_row=max(range(4),key=lambda r:nodes[root][1][r])
            else:
                numerator=-1;winning_row=None
                for r in range(4):
                    loads=tuple(1+(a==r) for a in range(4))
                    value=combine(root,loads)[fullmask]
                    if value>numerator:numerator,winning_row=value,r
            layout={1:0,5:winning_row+1}

            def recover_combine(node,loads,mask):
                children=nodes[node][0]
                # Recover only submasks of the winning assigned-label mask.
                submasks=[];sub=mask
                while True:
                    submasks.append(sub)
                    if sub==0:break
                    sub=(sub-1)&mask
                prefix_scores=[];choices=[]
                first=table(children[0],loads)
                scores={s:first[s] for s in submasks}
                prefix_scores.append(scores)
                for child in children[1:]:
                    right=table(child,loads);new={};take={}
                    for m in submasks:
                        sub=m;best=-1;chosen=None
                        while True:
                            budget();value=scores[m^sub]+right[sub]
                            if value>best:best,chosen=value,sub
                            if sub==0:break
                            sub=(sub-1)&m
                        new[m],take[m]=best,chosen
                    scores=new;prefix_scores.append(scores);choices.append(take)
                need(scores[mask]==combine(node,loads)[mask],'reconstruction convolution mismatch')
                allocation=[0]*len(children);remaining=mask
                for i in range(len(children)-1,0,-1):
                    allocation[i]=choices[i-1][remaining];remaining^=allocation[i]
                allocation[0]=remaining
                for child,assigned in zip(children,allocation):recover_table(child,loads,assigned)

            def recover_table(node,loads,mask):
                d,prefix=node;pure=mask&1;mixed=(mask>>1)&1;tailmask=mask>>2
                base_loads=tuple(v+pure for v in loads)
                if pure:layout[7**d]=prefix
                if mixed:
                    if d==K:
                        r=max(range(4),key=lambda a:nodes[node][1][a]*(2*base_loads[a]+1))
                    else:
                        r=max(range(4),key=lambda a:combine(node,tuple(v+(b==a) for b,v in enumerate(base_loads)))[tailmask])
                    q=7**d
                    layout[5*q]=prefix+q*((r+1-prefix)*pow(q,-1,5)%5)
                    base_loads=tuple(v+(a==r) for a,v in enumerate(base_loads))
                if d<K:recover_combine(node,base_loads,tailmask)

            if K:recover_combine(root,tuple(1+(a==winning_row) for a in range(4)),fullmask)
            need(set(layout)=={d for j in range(K+1) for d in (7**j,5*7**j)},'missing or repeated original labels')
            costs=self.layout_costs(layout)
            need(sum(w*c for w,c in zip(weights,costs))==numerator,'literal layout witness mismatch')
            output={'height':K,'numerator':numerator,'denominator':sum(weights),'value':F(numerator,sum(weights)),
                    'layout':layout,'point_costs':costs,'nodes':len(nodes),'cached_states':state_count,
                    'table_states_by_depth':misses_by_depth,'subset_operations':operations,
                    'seconds':monotonic()-started}
            return output
        finally:
            table.cache_clear();combine.cache_clear()

    def layout_costs(self,layout):
        need(type(layout) is dict and set(layout)=={d for j in range(self.height+1) for d in (7**j,5*7**j)},
             'one independent phase at every original divisor required')
        need(all(type(a) is int and 0<=a<d for d,a in layout.items()),'canonical literal phases required')
        def cost(r,y):
            load=0
            for d,a in layout.items():
                load+=int(y%d==a) if d%5 else int(r==a%5 and y%(d//5)==a%(d//5))
            return load*load
        return tuple(cost(r,y) for r,y in self.points)

    def brute_force(self,weights,max_layouts=1000000):
        """Independent tiny-support check using every active original phase."""
        need(type(weights) in (tuple,list) and len(weights)==len(self.points)
             and all(type(w) is int and w>=0 for w in weights) and sum(weights)>0,
             'nonnegative integer weights with positive sum required')
        need(type(max_layouts) is int and max_layouts>0,'positive brute-force limit required')
        moduli=tuple(d for j in range(self.height+1) for d in (7**j,5*7**j))
        values=[r+5*((y-r)*pow(5,-1,7**self.height)%7**self.height) for r,y in self.points] if self.height else [r for r,y in self.points]
        residues=[sorted({x%d for x,w in zip(values,weights) if w}) for d in moduli]
        count=1
        for rs in residues:count*=len(rs)
        if count>max_layouts:raise ResourceLimitError('brute-force comparison exceeds its explicit limit')
        best=-1;winner=None
        for phases in product(*residues):
            layout=dict(zip(moduli,phases))
            value=sum(w*c for w,c in zip(weights,self.layout_costs(layout)))
            if value>best:best,winner=value,layout
        return {'value':F(best,sum(weights)),'layout':winner,'layouts':count}
