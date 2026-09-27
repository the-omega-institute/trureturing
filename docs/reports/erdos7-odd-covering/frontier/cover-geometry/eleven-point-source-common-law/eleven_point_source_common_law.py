"""Uniform eleven-point laws for six independent original labels.
A source subconfiguration has at most three points per root, distinct
children and columns inside each root, and at most two points per column.
Then its uniform law has Gamma <= 5. Standard library; -O checks active.
"""
from collections import Counter,deque
from fractions import Fraction as F
from itertools import combinations,product
import json

def require(x,message):
    if not x: raise ValueError(message)

EXAMPLES = [{'source': [(6, 0), (6, 3), (11, 0), (11, 2), (21, 0), (21, 4), (21, 6), (2, 3), (7, 3), (7, 5), (17, 5), (22, 1), (3, 6), (13, 6), (18, 4), (4, 2), (4, 6), (14, 1), (19, 0), (24, 0), (24, 1)], 'selection': [(6, 3), (11, 2), (21, 0), (2, 3), (7, 5), (22, 1), (3, 6), (18, 4), (4, 2), (14, 1), (19, 0)]}, {'source': [(1, 4), (6, 4), (6, 6), (16, 0), (21, 6), (7, 1), (12, 2), (22, 2), (3, 0), (3, 5), (8, 0), (8, 5), (23, 0), (23, 3), (4, 4), (9, 3), (19, 3), (19, 6), (24, 5)], 'selection': [(1, 4), (16, 0), (21, 6), (7, 1), (12, 2), (3, 0), (8, 5), (23, 3), (4, 4), (9, 3), (24, 5)]}]

def crt(x,y):
    value=x+25*((y-x)*2%7)
    require(value%25==x and value%7==y and 0<=value<175,'literal CRT')
    return value

def check_source(source):
    require(len(set(source))==len(source),'distinct source points')
    require(all(0<=x<25 and x%5 and 0<=y<7 for x,y in source),'actual allowed carrier')
    require(len({y for x,y in source})>=5,'standalone seven condition')
    for E in combinations(range(7),2):
        require(sum(len({x for x,y in source if x%5==r and y not in E})>=3
                    for r in range(1,5))>=3,'complete product-tree source condition')

def check_selection(points):
    require(len(points)==len(set(points))==11,'eleven selected points')
    roots=Counter(x%5 for x,y in points);columns=Counter(y for x,y in points)
    require(max(roots.values())<=3 and max(columns.values())<=2,'root and column caps')
    require(len({x for x,y in points})==11,'distinct selected child leaves')
    require(len({(x%5,y) for x,y in points})==11,'matching columns within each root')
    maximum=-1;winner=None;checks=0
    for r,b,(u,v) in product(range(5),range(7),points):
        base=[1+(x%5==r)+(y==b) for x,y in points]
        direct=sum((l+3*((x,y)==(u,v)))**2 for (x,y),l in zip(points,base))
        n_root=roots[r];n_col=columns[b]
        n_intersection=sum(x%5==r and y==b for x,y in points)
        require(n_intersection<=1,'selected root-column intersection cap')
        expected=(11+3*n_root+3*n_col+2*n_intersection
                  +6*(1+(u%5==r)+(v==b))+9)
        require(direct==expected,'literal indicator-square identity')
        # Independent phases at labels 35,25,175 are singleton indicators.
        # Their total multiplicities n_p sum to three, so their increment
        # is at most 6 max(base)+9 and is attained with one common point.
        bound=(11+3*n_root+3*n_col+2*n_intersection+6*max(base)+9)
        require(direct<=bound<=55,'uniform eleven-point complete-layout bound')
        center=crt(u,v)
        phases=(0,r,u,b,center%35,center)
        literal=sum(sum(crt(x,y)%d==phase for d,phase in zip((1,5,25,7,35,175),phases))**2
                    for x,y in points)
        require(literal==direct,'all six original CRT residue indicators')
        if direct>maximum:maximum,winner=direct,phases
        checks+=1
    require(checks==385,'all root-column-center choices')
    return dict(exact_maximum=str(F(maximum,11)),attaining_original_phases=winner,
                root_counts=dict(roots),column_counts=dict(columns),literal_layout_checks=checks)

def select_points(source, stop_at=11):
    """Integral source/root/child/root-column/column/sink cap network."""
    source=tuple(source)
    require(len(set(source))==len(source),'distinct source points in selection input')
    require(all(type(x) is int and type(y) is int and 0<=x<25 and x%5 and 0<=y<7
                for x,y in source),'actual allowed carrier in selection input')
    if not source:return []
    require(stop_at in (11,12),'selection threshold')
    adjacency={};start=('source',);end=('sink',)
    def edge(u,v,cap):
        adjacency.setdefault(u,[]);adjacency.setdefault(v,[])
        adjacency[u].append([v,len(adjacency[v]),cap])
        adjacency[v].append([u,len(adjacency[u])-1,0])
    for r in sorted({x%5 for x,y in source}):edge(start,('root',r),3)
    for x in sorted({x for x,y in source}):edge(('root',x%5),('child',x),1)
    point_edges={}
    for x,y in sorted(source):
        u=('child',x);point_edges[(x,y)]=(u,len(adjacency[u]))
        edge(u,('root-column',x%5,y),1)
    for r,y in sorted({(x%5,y) for x,y in source}):edge(('root-column',r,y),('column',y),1)
    for y in sorted({y for x,y in source}):edge(('column',y),end,2)
    flow=0
    while flow<stop_at:
        previous={start:None};queue=deque([start])
        while queue and end not in previous:
            u=queue.popleft()
            for i,(v,rev,cap) in enumerate(adjacency[u]):
                if cap and v not in previous:previous[v]=(u,i);queue.append(v)
        if end not in previous:break
        v=end
        while v!=start:
            u,i=previous[v];q,rev,cap=adjacency[u][i]
            adjacency[u][i][2]-=1;adjacency[v][rev][2]+=1;v=u
        flow+=1
    selected=[p for p,(u,i) in point_edges.items() if adjacency[u][i][2]==0]
    require(len(selected)==flow,'selected original point edges equal flow')
    return selected

def matching_cut_certificate(source):
    """All 128 shared column cuts with exact per-root matching ranks."""
    rank_tables=[]
    for r in range(1,5):
        possible={0}
        for a in range(5):
            ys={y for x,y in source if x==r+5*a}
            possible |= {mask|(1<<y) for mask in possible for y in ys if not mask>>y&1}
        rank_tables.append([max(mask.bit_count() for mask in possible if mask & ~columns == 0)
                            for columns in range(128)])
    best=min((2*(7-columns.bit_count())+sum(min(3,rank[columns]) for rank in rank_tables),columns)
             for columns in range(128))
    value,columns=best
    return dict(maximum_flow=value,columns=[y for y in range(7) if columns>>y&1],
                root_matching_ranks=[rank[columns] for rank in rank_tables])


def cut_controls():
    # A proper-column-set obstruction: full-carrier truncated ranks sum
    # to twelve, but deleting column zero leaves four matching ranks two.
    triangles=((0,1,2),(0,3,4),(0,5,6))
    source=set()
    for r,triangle in enumerate(triangles,1):
        for a,pair in enumerate(combinations(triangle,2)):
            source.update((r+5*a,y) for y in pair)
    source.update((4+5*a,y) for a in range(3) for y in (0,1,3))
    source=tuple(sorted(source));check_source(source)
    cut=matching_cut_certificate(source)
    selected=select_points(source,12)
    require(len(selected)==cut['maximum_flow']==10,'proper-subset cut rejects an eleven-point selection')
    # The witness D={1,...,6} itself has four restricted ranks two.
    restricted=tuple((x,y) for x,y in source if y!=0)
    for r in range(1,5):
        rows=[{y for x,y in restricted if x==r+5*a} for a in range(5)]
        attainable={0}
        for ys in rows:attainable|={m|(1<<y) for m in attainable for y in ys if not m>>y&1}
        require(max(m.bit_count() for m in attainable)==2,'four proper-subset matching ranks')
    # The source is nevertheless covered by the earlier 24-point law.
    points={(x,y) for x,y in source if x%5!=4 or y in (1,3)}
    require(len(points)==24 and max(Counter(y for x,y in points).values())==6,
            'a successful degree-six selected source despite eleven-flow failure')
    require(select_points(())==[] and matching_cut_certificate(())['maximum_flow']==0,
            'empty source selection and cut agree')
    full=tuple((x,y) for x in range(25) if x%5 for y in range(7))
    require(matching_cut_certificate(full)['maximum_flow']==len(select_points(full,12))==12,
            'full carrier maximum flow is twelve')
    require(len(select_points(full))==11,'default selector stops at the sufficient eleven points')
    return dict(source=source,cut=cut,alternative_twenty_four_point_bound='14/3')


def verify():
    results=[]
    for example in EXAMPLES:
        source=tuple(example['source']);selection=tuple(example['selection'])
        check_source(source)
        require(set(selection)<=set(source),'declared selection lies in actual source')
        value=check_selection(selection)
        require(value['exact_maximum']=='5','attained complete bound for the declared examples')
        found=select_points(source)
        require(len(found)==11,'the cap network obtains eleven actual points')
        check_selection(found)
        cut=matching_cut_certificate(source)
        require(len(select_points(source,12))==cut['maximum_flow']==11,'network and exact shared-column cut agree')
        results.append(dict(source_size=len(source),declared_selection=selection,
                            network_selection=found,**value))
    return dict(common_law_bound='5',uniform_mass='1/11',examples=results,cut_control=cut_controls())

if __name__=='__main__':
    print(json.dumps(verify(),indent=2))
