#!/usr/bin/env python3
"""Exact local-risk and Hunter-tree certificates for one extension of327."""
from fractions import Fraction as F
from itertools import combinations


def require(ok, message):
    if not ok:
        raise ValueError(message)


def kernel(p, bad, delta):
    alpha = F(len(bad), p)
    beta = max(F(0), alpha-delta)/(1-delta)
    row = tuple(beta/len(bad) if y in bad else F(1,p)/(1-min(alpha,delta)) for y in range(p))
    require(sum(row)==1, 'Normalized full-Haar physical row')
    return row, tuple(F(0) if y in bad else row[y] for y in range(p)), beta


def run(family):
    # At the existing327 old19 source delta_0, the two original23 labels
    # 3*23 and5*23 give bad rows0,1. The two original29 labels
    # 7*23*29 and11*23*29 give the active rows below and bad z29=0.
    # The only added label13*29*31 has residue(x13,z29,w31)=(0,0,0).
    old_primes=(3,5,7,11,13,17,19)
    labels=(*old_primes,3*23,5*23,7*23*29,11*23*29,13*29*31)
    require(len(labels)==len(set(labels))==12 and all(d>1 and d%2 for d in labels), 'Twelve distinct original odd labels')
    row23, kill23, b23=kernel(23,{0,1},F(1,23))
    active={0,1} if family=='A' else {2}
    risk23=[]
    physical31=exact=mass29=F(0)
    total=physical_survival=F(0)
    primes=(23,29,31)
    marginals={p:F(0) for p in primes}
    intersections={pair:F(0) for pair in combinations(primes,2)}
    tree=((23,29),(29,31)) if family=='A' else ((23,31),(29,31))
    for y in range(23):
        row29, kill29, beta29=kernel(29,{0} if y in active else set(),F(1,58))
        future=F(0)
        for z in range(29):
            row31, kill31, beta31=kernel(31,{0} if z==0 else set(),F(1,62))
            require(beta31==F(1,61) if z==0 else beta31==0, 'Exact final original-label hazard')
            future+=kill29[z]*beta31
            physical31+=row23[y]*row29[z]*beta31
            for w in range(31):
                exact+=kill23[y]*kill29[z]*kill31[w]
                mass=row23[y]*row29[z]*row31[w]
                event={23:y in {0,1},29:y in active and z==0,31:z==0 and w==0}
                total+=mass
                if not any(event.values()):
                    physical_survival+=mass
                for p in primes:
                    if event[p]:marginals[p]+=mass
                for edge in intersections:
                    if event[edge[0]] and event[edge[1]]:intersections[edge]+=mass
                if mass and any(event.values()):
                    active_edges=sum(event[a] and event[b] for a,b in tree)
                    require(sum(event.values())-active_edges==1, 'Every nonempty active event set is connected in the selected tree')
        risk=beta29+future
        require(0<=risk<=1, 'Local Bellman risk bound')
        risk23.append(risk)
        mass29+=kill23[y]*sum(kill29)
        require(risk==(F(1,57) if y in active else F(1,1769)), 'Two non-circular row certificate values')
    backward=1-b23-sum(kill23[y]*risk23[y] for y in range(23))
    scalar=mass29-physical31
    expected=F(18564,19459) if family=='A' else F(1057292,1109163)
    expected_edges={(23,29):F(1,1254) if family=='A' else F(0),
                    (23,31):F(1,76494) if family=='A' else F(1,38918),
                    (29,31):F(1,76494)}
    require(total==1 and physical_survival==exact==backward==expected, 'Independent physical and killed terminal sums equal the local certificate')
    require(marginals=={23:F(1,22),29:F(1,1254),31:F(613,1109163)}, 'Three exact same-chain marginals')
    require(intersections==expected_edges, 'Three exact same-chain pair intersections')
    # On three vertices every two different edges form a spanning tree.
    maximum=max(sum(intersections[e] for e in edges) for edges in combinations(intersections,2))
    require(maximum==sum(intersections[e] for e in tree), 'Displayed tree is a maximum-weight spanning tree')
    require(1-sum(marginals.values())+maximum==expected, 'Hunter tree certificate equals actual survival')
    gain=F(1,76494) if family=='A' else F(43,1109163)
    require(backward-scalar==gain>0, 'Exact strict gain over through29 plus physical31 charge')
    print(family, 'survival31',backward,'gain',gain,'intersections',intersections,'tree',tree)


if __name__=='__main__':
    run('A')
    run('B')
