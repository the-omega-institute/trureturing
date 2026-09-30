from fractions import Fraction as F
import itertools
# Reuse topology rows/classes from verifier without running its print.
exec(open('verify_degree10_star.py').read().split("# Every degree-ten")[0])
formula_edges=[(0,1),(0,2),(0,3),(2,3),(1,3),(1,2)]
maps={}
for i in range(6):
    arr=[]
    for p in itertools.permutations(range(4)):
        if tuple(sorted(p[v] for v in edges[i])) != formula_edges[0]: continue
        inv={p[k]:k for k in range(4)}
        old=[edge_index[tuple(sorted(inv[v] for v in e))] for e in formula_edges]
        if old[0] == i: arr.append(old)
    maps[i] = arr
class_of={x:c for c in classes for x in c}
deg_of={x:len(c) for c in classes for x in c}
bounds={8:(F(11,8),F(2)),10:(F(11,10),F(71,50)),38:(F(1009,1000),F(21,20))}
def phi_sq(v):
    x1,x2,x3,x4,x5,x6=v
    A=2*x1*x2*x6+x1*x1+x2*x2+x6*x6-1
    B=2*x1*x3*x5+x1*x1+x3*x3+x5*x5-1
    P=x2*x3+x5*x6+x1*x2*x5+x1*x3*x6-(x1*x1-1)*x4
    assert A > 0 and B > 0 and P > 0
    assert P*P < A*B
    return P*P/(A*B)
mins={d:F(2) for d in (8,10,38)}; maxs={d:F(0) for d in (8,10,38)}
for t in range(16):
    for i in range(6):
        d=deg_of[6*t+i]
        for old in maps[i]:
            vl=[];vu=[]
            for j,oi in enumerate(old):
                l,u=bounds[deg_of[6*t+oi]]
                vl.append(l if j != 3 else u)
                vu.append(u if j != 3 else l)
            mins[d]=min(mins[d],phi_sq(vl)); maxs[d]=max(maxs[d],phi_sq(vu))
assert mins[8] == F(476863260165601,927717115485601)
assert maxs[8] == F(5147632009,10379941924)
assert maxs[10] == F(1842240125,2818928432)
assert maxs[38] == F(100755605,105172928)
assert mins[8] > F(1,2) and maxs[8] < F(1,2)
assert phi_sq([F(11,8),F(11,8),F(11,8),F(71,50),F(1),F(1)]) == F(143,200)**2
assert phi_sq([F(2),F(2),F(2),F(1),F(71,50),F(71,50)]) == F(35941,50941)**2
# Universal lower envelope uses neighbors ONE and opposite TWO.
assert phi_sq([F(11,10),F(1),F(1),F(2),F(1),F(1)]) == F(6,7)**2
assert phi_sq([F(1009,1000),F(1),F(1),F(2),F(1),F(1)]) == F(1982,2009)**2
# Degree-10 upper: q^2 < cos(pi/5)^2=(3+sqrt 5)/8, by sqrt(5)>r.
r=F(785141963,352366054)
assert 8*maxs[10]-3 == r and r > 0
assert r*r < 5
assert F(5,6) < F(6,7)
# cos(pi/5)=(1+sqrt 5)/4<5/6, because sqrt 5<7/3.
assert 5 < F(7,3)**2
# Degree-38 upper/lower compare to Taylor bounds at pi/19.
lo_cos=F(17447,17689)
up_cos=1-F(157,950)**2/F(2)+F(157,950)**4/F(24)
assert maxs[38] < lo_cos*lo_cos
assert F(1982,2009) > up_cos
print('PASS: exact endpoint squares and incidence bounds')
print('lower squares =', mins)
print('upper squares =', maxs)
