#!/usr/bin/env python3
"""Supplementary exact checks for CFMP Sections 126-132.

Python 3, standard library only. Run without -O. This validates one actual
face-pairing packet and finite group identities. Floating checks of a reduced
geometric system are supplementary, not interval or Lean certification.
Local edge order agrees with the theory: (01,02,03,23,13,12).
"""
from __future__ import annotations

import collections
import itertools
import json
import math
import random
from fractions import Fraction

EDGES = ((0, 1), (0, 2), (0, 3), (2, 3), (1, 3), (1, 2))
EDGE_INDEX = {edge: i for i, edge in enumerate(EDGES)}
IDENTITY = tuple(range(4))
PERMUTATIONS = tuple(itertools.permutations(range(4)))
MATCHINGS = (frozenset((0, 3)), frozenset((1, 4)), frozenset((2, 5)))
TETS = ((0, 1, 2, 3), (0, 1, 2, 4)) + tuple(
    tuple(v for v in range(5) if v != missing)
    for missing in range(3) for _ in range(5)
)
ROWS = (
    (0,0,4,3,'3012'), (5,3,3,3,'0123'), (6,3,2,3,'0123'),
    (7,3,0,1,'0231'), (8,3,11,3,'0123'), (9,3,10,3,'0123'),
    (0,2,14,3,'0132'), (15,3,12,3,'0123'), (16,3,13,3,'0123'),
    (1,3,0,3,'0123'), (2,2,5,2,'0123'), (3,2,1,0,'1203'),
    (4,2,6,2,'0123'), (1,1,9,2,'0213'), (10,2,8,2,'0123'),
    (11,2,7,2,'0123'), (12,2,1,2,'0123'), (13,2,15,2,'0123'),
    (14,2,16,2,'0123'), (2,0,9,0,'0123'), (3,0,8,0,'0123'),
    (4,0,5,0,'0123'), (10,0,7,0,'0123'), (11,0,6,0,'0123'),
    (5,1,16,0,'1023'), (6,1,15,0,'1023'), (12,0,4,1,'1023'),
    (13,0,2,1,'1023'), (14,0,3,1,'1023'), (7,1,13,1,'0123'),
    (8,1,12,1,'0123'), (9,1,11,1,'0123'), (15,1,14,1,'0123'),
    (16,1,10,1,'0123'),
)
POSITIVE_TETS = frozenset((0, 2, 3, 4, 10, 11, 12, 13, 14))


def compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(p.index(i) for i in range(len(p)))


def edge_image(p: tuple[int, ...], j: int) -> int:
    a, b = EDGES[j]
    return EDGE_INDEX[tuple(sorted((p[a], p[b])))]


def odd(p: tuple[int, ...]) -> bool:
    return bool(sum(p[i] > p[j] for i in range(4)
                    for j in range(i + 1, 4)) % 2)


def rho(p: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(MATCHINGS.index(frozenset(edge_image(p, j) for j in m))
                 for m in MATCHINGS)


def generated(gens) -> frozenset[tuple[int, ...]]:
    gens = set(gens) | {inverse(g) for g in gens}
    group, todo = {IDENTITY}, [IDENTITY]
    while todo:
        p = todo.pop()
        for q in gens:
            pq = compose(p, q)
            if pq not in group:
                group.add(pq)
                todo.append(pq)
    return frozenset(group)


class DSU:
    def __init__(self, size: int):
        self.parent = list(range(size))

    def find(self, a: int) -> int:
        while a != self.parent[a]:
            self.parent[a] = self.parent[self.parent[a]]
            a = self.parent[a]
        return a

    def union(self, a: int, b: int) -> None:
        self.parent[self.find(a)] = self.find(b)

    def groups(self) -> list[list[int]]:
        groups = collections.defaultdict(list)
        for i in range(len(self.parent)):
            groups[self.find(i)].append(i)
        return sorted(groups.values(), key=lambda g: g[0])


def check_groups() -> dict:
    for p in PERMUTATIONS:
        for q in PERMUTATIONS:
            assert rho(compose(p, q)) == compose(rho(p), rho(q))
    kernel = {p for p in PERMUTATIONS if rho(p) == (0, 1, 2)}
    assert kernel == {IDENTITY, (1,0,3,2), (2,3,0,1), (3,2,1,0)}
    assert len({rho(p) for p in PERMUTATIONS}) == 6
    groups, todo = {frozenset((IDENTITY,))}, [frozenset((IDENTITY,))]
    while todo:
        h = todo.pop()
        for p in PERMUTATIONS:
            if p not in h:
                larger = generated(set(h) | {p})
                if larger not in groups:
                    groups.add(larger)
                    todo.append(larger)
    assert len(groups) == 30
    no_fixed_state = 0
    for h in groups:
        fixed = [i for i in range(3) if all(rho(p)[i] == i for p in h)]
        contains_order_three = any(p != IDENTITY and
            compose(p, compose(p, p)) == IDENTITY for p in h)
        assert (not fixed) == contains_order_three == (len(h) % 3 == 0)
        no_fixed_state += not fixed
    assert no_fixed_state == 10
    # AGL(2,F2), with column vectors encoded (x,y) as x+2*y.
    linear, affine = set(), set()
    for a,b,c,d in itertools.product((0,1), repeat=4):
        if (a*d-b*c) % 2 != 1:
            continue
        p = tuple((a*(v%2)+b*(v//2))%2 +
                  2*((c*(v%2)+d*(v//2))%2) for v in range(4))
        linear.add(p)
        for translation in range(4):
            affine.add(tuple(w ^ translation for w in p))
    assert len(linear) == 6 and affine == set(PERMUTATIONS)
    fibonacci_mod_two = (0,2,3,1)  # matrix [[0,1],[1,1]]
    assert compose(fibonacci_mod_two, compose(fibonacci_mod_two,
                    fibonacci_mod_two)) == IDENTITY
    assert not any(rho(fibonacci_mod_two)[i] == i for i in range(3))
    # A literal Regge angle reflection fails on the full hyperideal angle cone.
    angles = tuple(Fraction(v,10) for v in (1,7,1,1,1,1))
    assert all(sum(angles[j] for j,e in enumerate(EDGES) if v in e) < 1
               for v in range(4))
    cross = (1,2,4,5)
    semisum = sum(angles[j] for j in cross)/2
    reflected = tuple(angles[j] if j in (0,3) else semisum-angles[j]
                      for j in range(6))
    assert min(reflected) == Fraction(-1,5)
    return dict(s4_order=24, quotient_order=6, kernel_order=4,
                checked_subgroups=30, no_fixed_matching_subgroups=no_fixed_state,
                affine_group_order=len(affine), regge_negative_angle=str(min(reflected)))


def verify_topology(rows=ROWS) -> dict:
    n = len(TETS)
    face = {}
    edges, vertices, ends, dual = DSU(6*n), DSU(4*n), DSU(12*n), DSU(n)
    fans = collections.defaultdict(list)
    for t,f,u,g,digits in rows:
        p = tuple(map(int, digits))
        assert sorted(p) == list(range(4)) and p[f] == g
        assert (t,f) != (u,g) and (t,f) not in face and (u,g) not in face
        face[t,f], face[u,g] = (u,g,p), (t,f,inverse(p))
        dual.union(t,u)
        et, eu = (1 if t in POSITIVE_TETS else -1), (1 if u in POSITIVE_TETS else -1)
        assert eu == et * (1 if odd(p) else -1)
        for i in range(4):
            if i != f:
                assert TETS[t][i] == TETS[u][p[i]]
                vertices.union(4*t+i,4*u+p[i])
        for j,(a,b) in enumerate(EDGES):
            if f in (a,b):
                continue
            k = edge_image(p,j)
            edges.union(6*t+j,6*u+k)
            for v in (a,b):
                x = 2*(6*t+j) + int(v == b)
                y = 2*(6*u+k) + int(p[v] == max(p[a],p[b]))
                ends.union(x,y)
                fans[x].append(y)
                fans[y].append(x)
    assert len(face) == 4*n and len(dual.groups()) == 1
    labels = [tuple(sorted((TETS[t][a],TETS[t][b])))
              for t in range(n) for a,b in EDGES]
    groups = edges.groups()
    assert len(groups) == 10
    assert all(len({labels[o] for o in group}) == 1 for group in groups)
    degrees = {labels[group[0]]:len(group) for group in groups}
    assert len(degrees) == 10
    assert sorted(degrees.values()) == [7]*3 + [11]*6 + [15]
    assert all(ends.find(2*o) != ends.find(2*o+1) for o in range(6*n))
    cycles = {}
    for group in groups:
        t,j = divmod(group[0],6)
        a,b = EDGES[j]
        entry = next(i for i in range(4) if i not in (a,b))
        state = start = (t,a,b,entry)
        visited = []
        for step in range(len(group)):
            t,a,b,entry = state
            visited.append(6*t+EDGE_INDEX[tuple(sorted((a,b)))])
            exit_face = next(i for i in range(4) if i not in (a,b,entry))
            u,g,p = face[t,exit_face]
            state = (u,p[a],p[b],g)
            assert state != start or step == len(group)-1
        assert state == start and sorted(visited) == group
        cycles[''.join(map(str, labels[group[0]]))] = visited
    for fan in ends.groups():
        assert all(len(fans[x]) == 2 for x in fan)
        todo, reached = [fan[0]], {fan[0]}
        while todo:
            for y in fans[todo.pop()]:
                if y not in reached:
                    reached.add(y)
                    todo.append(y)
        assert reached == set(fan)
    links = []
    for group in vertices.groups():
        symbols = {TETS[x//4][x%4] for x in group}
        assert len(symbols) == 1
        link_vertices = set()
        for tv in group:
            t,a = divmod(tv,4)
            for b in range(4):
                if b != a:
                    j = EDGE_INDEX[tuple(sorted((a,b)))]
                    link_vertices.add(ends.find(2*(6*t+j)+int(a>b)))
        ff = len(group)
        assert ff % 2 == 0
        ee, vv = 3*ff//2, len(link_vertices)
        chi = vv-ee+ff
        assert chi < 0 and chi % 2 == 0
        links.append(dict(symbol=next(iter(symbols)),V=vv,E=ee,F=ff,
                          chi=chi,genus=1-chi//2))
    links.sort(key=lambda x:x['symbol'])
    assert [v['genus'] for v in links] == [2,2,2,3,3]
    assert len(ends.groups()) == 20
    canonical = lambda t: min(tuple(labels[6*t+edge_image(p,j)] for j in range(6))
                              for p in PERMUTATIONS)
    type_counts = collections.Counter(canonical(t) for t in range(n))
    assert sorted(type_counts.values()) == [1,1,5,5,5]
    assert all(len(set(labels[6*t:6*t+6])) == 6 for t in range(n))
    assert not set.intersection(*(set(labels[6*t:6*t+6]) for t in range(n)))
    alpha = [Fraction(2,degrees[label]) for label in labels]
    for group in groups:
        assert sum(alpha[o] for o in group) == 2
    corners = [sum(alpha[6*t+j] for j,e in enumerate(EDGES) if v in e)
               for t in range(n) for v in range(4)]
    assert max(corners) == Fraction(58,77)
    return dict(face=face,labels=labels,degrees=degrees,links=links,cycles=cycles,
                fan_sizes=sorted(map(len,ends.groups())),type_sizes=sorted(type_counts.values()),
                max_corner=str(max(corners)))


def action_for_symbols(c: tuple[int, ...]):
    destination, local = [], []
    for t,vs in enumerate(TETS):
        missing = next(v for v in range(5) if v not in vs)
        mapped_missing = c[missing]
        if mapped_missing == 4:
            u = 0
        elif mapped_missing == 3:
            u = 1
        else:
            assert t >= 2
            u = 2+5*mapped_missing+(t-2)%5
        p = tuple(TETS[u].index(c[v]) for v in vs)
        destination.append(u)
        local.append(p)
    return destination, local


def verify_action(data: dict, c: tuple[int, ...], action=None) -> None:
    destination, local = action_for_symbols(c) if action is None else action
    assert sorted(destination) == list(range(len(TETS)))
    for t in range(len(TETS)):
        u,p = destination[t],local[t]
        assert sorted(p) == list(range(4))
        for j in range(6):
            lhs = data['labels'][6*u+edge_image(p,j)]
            rhs = tuple(sorted(c[v] for v in data['labels'][6*t+j]))
            assert lhs == rhs


def count_actual_automorphisms(face: dict) -> list:
    n = len(TETS)
    def extend(dst,p):
        tm, pm, backward, todo = {0:dst}, {0:p}, {dst:0}, [0]
        while todo:
            t = todo.pop()
            u,pt = tm[t],pm[t]
            for f in range(4):
                v,g,q = face[t,f]
                w,h,r = face[u,pt[f]]
                proposed = compose(r,compose(pt,inverse(q)))
                if v in tm:
                    if tm[v] != w or pm[v] != proposed:
                        return False
                else:
                    if w in backward:
                        return False
                    tm[v],pm[v],backward[w] = w,proposed,v
                    todo.append(v)
        return len(tm) == n
    return [(dst,p) for dst in range(n) for p in PERMUTATIONS if extend(dst,p)]


def check_packet() -> dict:
    data = verify_topology()
    c = (1,2,0,3,4)
    destination,local = action_for_symbols(c)
    verify_action(data,c)
    for t in range(len(TETS)):
        t1,t2 = destination[t],destination[destination[t]]
        assert destination[t2] == t
        assert compose(local[t2],compose(local[t1],local[t])) == IDENTITY
    assert destination[:2] == [0,1]
    assert all(not any(rho(local[t])[j] == j for j in range(3)) for t in (0,1))
    broken = 0
    for (t,f),(u,g,q) in data['face'].items():
        tt,pt,uu,pu = destination[t],local[t],destination[u],local[u]
        expected = (uu,pu[g],compose(pu,compose(q,inverse(pt))))
        broken += data['face'][tt,pt[f]] != expected
    assert broken == 52
    autos = count_actual_automorphisms(data['face'])
    assert autos == [(0,IDENTITY)]
    # Short, explicitly displayed certificates for the eleven nonidentity
    # degree-compatible initial maps. Digits are source omitted-face indices.
    witnesses = (
        (0,'0213','0','320',4,4,2), (0,'1023','0','320',4,7,8),
        (0,'1203','0','320',4,7,8), (0,'2013','0','320',4,14,11),
        (0,'2103','1','32321',7,7,9), (1,'0123','2','3231',14,12,10),
        (1,'0213','0','320',4,3,10), (1,'1023','0','320',4,9,15),
        (1,'1203','0','320',4,9,5), (1,'2013','0','320',4,12,13),
        (1,'2103','2','3231',14,3,11),
    )
    def transport_word(dst,initial,word):
        source,target,p = 0,dst,tuple(map(int,initial))
        for digit in word:
            f = int(digit)
            v,g,q = data['face'][source,f]
            w,h,r = data['face'][target,p[f]]
            p = compose(r,compose(p,inverse(q)))
            source,target = v,w
        return source,target
    for dst,p,w1,w2,source,target1,target2 in witnesses:
        assert transport_word(dst,p,w1) == (source,target1)
        assert transport_word(dst,p,w2) == (source,target2)
        assert target1 != target2
    # Full S3 x C2 incidence action used in the three-length reduction.
    symbols = [tuple(p)+(3,4) for p in itertools.permutations(range(3))]
    symbols += [tuple(p)+(4,3) for p in itertools.permutations(range(3))]
    for p in symbols:
        verify_action(data,p)
    for p in symbols:
        for q in symbols:
            ap,aq,apq = action_for_symbols(p),action_for_symbols(q),action_for_symbols(compose(p,q))
            for t in range(len(TETS)):
                assert apq[0][t] == ap[0][aq[0][t]]
                assert apq[1][t] == compose(ap[1][aq[0][t]],aq[1][t])
    corrupted = list(ROWS)
    corrupted[0] = (*corrupted[0][:4], '3102')
    rejected = False
    try:
        verify_topology(tuple(corrupted))
    except AssertionError:
        rejected = True
    assert rejected
    wrong = list(local)
    wrong[0] = IDENTITY
    action_rejected = False
    try:
        verify_action(data,c,(destination,wrong))
    except AssertionError:
        action_rejected = True
    assert action_rejected
    return dict(tetrahedra=17,face_pairs=34,
                degrees={''.join(map(str,k)):v for k,v in data['degrees'].items()},
                vertex_links=data['links'],link_fan_sizes=data['fan_sizes'],
                named_type_sizes=data['type_sizes'],maximum_initial_corner_over_pi=data['max_corner'],
                incidence_c3_tetrahedra=destination,incidence_c3_local_maps=local,
                violated_directed_face_equations=broken,actual_automorphism_trials=408,
                actual_automorphism_count=1,short_automorphism_obstruction_checks=11,
                incidence_s3_times_c2_order=12,
                edge_first_return_cycles=data['cycles'],
                corrupted_face_rejected=rejected,corrupted_incidence_action_rejected=action_rejected)


def raw_angles(x) -> list[float]:
    def at(i,j): return x[EDGE_INDEX[tuple(sorted((i,j)))]]
    out = []
    for i,j in EDGES:
        k,h = [v for v in range(4) if v not in (i,j)]
        r,a,b,o,c,d = at(i,j),at(i,k),at(i,h),at(k,h),at(j,h),at(j,k)
        numerator = a*b+c*d+r*a*c+r*b*d-(r*r-1)*o
        denominator = math.sqrt((r*r+a*a+d*d+2*r*a*d-1)*
                                (r*r+b*b+c*c+2*r*b*c-1))
        cosine = numerator/denominator
        assert -1-1e-12 <= cosine <= 1+1e-12
        out.append(math.acos(max(-1,min(1,cosine))))
    return out


def reduced(a: float,b: float):
    q = math.cos(2*math.pi/15)
    d = 1+2*b*b*(1-q)/(a+q)
    assert a>1 and b>1 and d>1 and (a-1)*(d-1)<4*b*b
    alpha = math.acos(b*math.sqrt(a+1)/math.sqrt((2*a-1)*(a-1+2*b*b)))
    beta = math.acos((a+b*b)/(a-1+2*b*b))
    theta = math.acos((2*b*b-(a-1)*d)/(a-1+2*b*b))
    eta = math.acos(b*math.sqrt((a+1)*(d+1))/math.sqrt((a-1+2*b*b)*(d-1+2*b*b)))
    return d,(alpha,beta,theta,eta), (2*alpha+5*theta-2*math.pi,beta+10*eta-2*math.pi)


def check_reduction() -> dict:
    rng = random.Random(9474119)
    error = 0.0
    for _ in range(600):
        a,b = 1+rng.uniform(.04,5),1+rng.uniform(.04,5)
        d,angles,_ = reduced(a,b)
        alpha,beta,theta,eta = angles
        core = raw_angles((a,a,b,b,b,a))
        bridge = raw_angles((a,b,b,d,b,b))
        expected_core = (alpha,alpha,beta,beta,beta,alpha)
        expected_bridge = (theta,eta,eta,2*math.pi/15,eta,eta)
        error = max(error,max(abs(x-y) for x,y in zip(core,expected_core)),
                    max(abs(x-y) for x,y in zip(bridge,expected_bridge)))
        for angle_vector in (core,bridge):
            assert all(0<x<math.pi for x in angle_vector)
            assert all(sum(angle_vector[j] for j,e in enumerate(EDGES) if v in e)<math.pi
                       for v in range(4))
    # Exact S3-fixed and paired-character determinants, using the newly
    # published six-length Gram-sign interface as a credited input.
    def gram_determinant(values):
        matrix = [[Fraction(int(i == j)) for j in range(4)] for i in range(4)]
        for x,(i,j) in zip(values,EDGES):
            matrix[i][j] = matrix[j][i] = -x
        total = Fraction()
        for p in PERMUTATIONS:
            term = Fraction(-1 if odd(p) else 1)
            for i in range(4):
                term *= matrix[i][p[i]]
            total += term
        return total
    for _ in range(100):
        a = 1+Fraction(rng.randrange(1,50),10)
        b = 1+Fraction(rng.randrange(1,50),10)
        d = 1+2*b*b/(a+1)
        central = gram_determinant((a,a,b,b,b,a))
        bridge = gram_determinant((a,b,b,d,b,b))
        assert central == (1+a)**2*(1-2*a-3*b*b) < 0
        assert bridge == -(1+a)*(1+d)*(4*b*b-(a-1)*(d-1)) < 0
    # Float residual at a reference approximation, not an existence proof.
    a,b = 1.7433180903647077,1.2673395905552322
    d,_,residual = reduced(a,b)
    assert max(map(abs,residual)) < 1e-12 and error < 1e-10
    flat = raw_angles((5.,2.,2.,5.,2.,2.))
    assert max(abs(x-y) for x,y in zip(flat,(math.pi,0,0,math.pi,0,0))) < 1e-7
    return dict(reduced_formula_samples=600,exact_character_determinant_checks=200,
                maximum_formula_error=error,
                approximate_cosh_lengths=[a,b,d],maximum_root_residual=max(map(abs,residual)),
                v4_invariant_flat_example_checked=True)


def main() -> None:
    if not __debug__:
        raise RuntimeError('Assertions are required. Run without -O.')
    output = dict(groups=check_groups(),packet=check_packet(),analytic=check_reduction(),
                  status='Finite checks only; written geometry requires its stated external inputs. No Lean or full-CFMP certification.')
    print(json.dumps(output,indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
