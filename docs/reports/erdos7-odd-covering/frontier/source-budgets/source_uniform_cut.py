#!/usr/bin/env python3
"""Exact uniform transport for both actual F_N source squares, N>=4.

Report339e supplies the finite-sum identities and the separately affine
coefficient argument. Types select edge coefficients; vertices are never
contracted. Explicit rational checks remain active under Python -O.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from itertools import product
from functools import lru_cache

T = [
    (a,j,k)
    for a in (1,2,3)
    for j in (0,1)
    for k in (0,1)
    if (a,j,k) != (2,0,0)
]

# Upper-triangular rows, including the diagonal.
# Every listed integer has denominator 10000.
TH = [
 [0,-8791,10000,10000,-10000,10000,-5580,-10000,-10000,-10000,-10000],
 [10000,10000,-1116,-5935,10000,9204,-10000,-10000,-10000,-10000],
 [-366,-6867,-10000,-9511,5383,-10000,-10000,-10000,-10000],
 [3109,-10000,-10000,-9884,-10000,-10000,-10000,-10000],
 [10000,10000,-10000,3819,-3408,10000,10000],
 [-2582,-9751,-10000,-10000,6090,6857],
 [6424,-10000,-10000,7075,-1142],
 [4216,-3945,1406,487],
 [6997,-3283,-3645],
 [3110,-1579],
 [1638]
]
TH = {
    (i,i+j): F(n,10000)
    for i,row in enumerate(TH)
    for j,n in enumerate(row)
}

# Subtypes: type order T, then lexicographic offset bits.
# Active coordinates are a>=3, j>0, k>0, in that order.
# Bit 0 fixes the first exponent; bit 1 denotes the full tail.
HA = [
    225,
    7153,6897,
    2401,0,
    11760,11618,0,0,
    6376,6234,
    0,0,
    20000,19859,0,0,
    14121,13979,
    30625,30484,30101,27659,
    19914,19772,18989,15713,
    36945,36803,35401,27500,35921,30697,34215,21958
]
HB = [
    1010,
    9584,9416,
    3449,0,
    15000,14859,2878,0,
    25126,24984,
    13691,0,
    45000,44859,11275,0,
    2447,2305,
    22396,19755,21872,16930,
    925,784,0,0,
    21007,15241,14051,0,19985,9646,12865,0
]

def axes(t):
    return [
        i for i,b in enumerate(
            (t[0] == 3, t[1] == 1, t[2] == 1)
        ) if b
    ]

GROUPS = [
    (t,ss)
    for t in T
    for ss in product((0,1), repeat=len(axes(t)))
]

if len(T) != 11 or len(TH) != 66:
    raise ArithmeticError("invalid motif dimensions")
if not all(abs(theta) <= 1 for theta in TH.values()):
    raise ArithmeticError("edge capacity violation")
if len(GROUPS) != 35 or len(HA) != 35 or len(HB) != 35:
    raise ArithmeticError("invalid allowance dimensions")
if min(HA+HB) < 0:
    raise ArithmeticError("negative allowance")

H = {
    (b,g): F(h,10000)
    for b,arr in enumerate((HA,HB))
    for g,h in zip(GROUPS,arr)
}

@lru_cache(maxsize=None)
def residual(t, indices, e, qn, branch, candidate):
    A,J,K = indices
    E3,E5,E7 = e
    x,y,z = qn
    a,j,k = t
    ti = T.index(t)

    rA,rB = F(11,8),F(5,4)
    eta = F(1,18)+x/2
    q = (1-y)/4
    s = (1-z)/6
    u = 1-s

    # Categories 0,1,2 are A,B,C.
    # Category 3 represents shallow ternary root 1.
    fz = (
        1-q,
        1-q,
        1-2*q,
        1-(F(5,2)-3*x/2)*q
    )
    gz = (u-F(1,7),u-F(2,7),u,u)

    def sf(c,b):
        if b:
            return q if not j else J+1+(1-E5)/4
        return fz[c] if not j else F(1)

    def sg(c,b):
        if b:
            return s if not k else K+1+(1-E7)/6
        return gz[c] if not k else F(1)

    # (source category, normalized ternary factor, binary root)
    def local():
        if a == 1:
            return [
                (0,3*rA*eta,0),
                (1,rB/3,0),
                (3,F(1),1)
            ]
        if a == 2:
            return [(1,rB,0),(2,F(1),1)]
        return [(0,rA,0),(2,F(1),1)]

    # Sum over the partner's ternary exponent type aa.
    def terms(aa):
        if a == aa == 1:
            return local()
        if max(a,aa) == 2:
            f = F(1,3) if a == 1 else F(1)
            return [(1,rB*f,0),(2,f,1)]
        if a < 3 and aa == 3:
            f = 3**a*(F(1,18)-x/2)
        elif a == aa == 3:
            f = A+1+(1-E3)/2
        else:
            f = F(1)
        return [(0,rA*f,0),(2,f,1)]

    rowdiff = F(0)
    div = F(0)

    for ui,(aa,jj,kk) in enumerate(T):
        p = [F(0),F(0)]
        for c,h,root in terms(aa):
            p[root] += h*sf(c,jj)*sg(c,kk)
        rowdiff += p[0]-p[1]

        if ui != ti:
            direction = 1 if ti < ui else -1
            theta = TH[min(ti,ui),max(ti,ui)]
            div += direction*theta*(p[0]+p[1])

    cross = F(0)
    lex = F(0)

    for c,h,root in local():
        direction = 1 if root == 0 else -1
        cross += (
            direction*h
            *(sf(c,0)+sf(c,1))
            *(sg(c,0)+sg(c,1))
        )

        v = F(0)
        if a == 3:
            v += (A-(1-E3)/2)*sf(c,j)*sg(c,k)
        if j:
            v += (J-(1-E5)/4)*sg(c,k)
        if k:
            v += (
                (K-(1-E7)/6)
                *(fz[c] if not j else 1)
            )
        lex += h*v

    div += TH[ti,ti]*lex
    d = 2*cross+rowdiff

    def diag(c):
        return (
            (fz[c] if not j else 1)
            *(gz[c] if not k else 1)
        )

    def unary(c,h):
        return h*(
            diag(c)
            +2*(sf(c,0)+sf(c,1))*(sg(c,0)+sg(c,1))
        )

    if branch == 2:
        d -= 2*(F(1,3) if a == 1 else 1)*diag(2)

    elif a == 1:
        h = 3*rA*eta if branch == 0 else rB/3
        d += 2*h*diag(branch)

    else:
        env = sum(
            unary(c,h)
            for c,h,root in local()
            if root == 0
        )
        if candidate == 0:
            h = 9*rA*eta if a == 2 else rA
        else:
            h = rB
        d += unary(candidate,h)-env
        if candidate == branch:
            d += 2*h*diag(candidate)

    return div-d

def anchor_loss(branch,qn):
    x,y,z = qn
    t = F(1,18)-x/2
    eta = F(1,18)+x/2
    q = (1-y)/4
    u = F(5,6)+z/6
    rH = F(11,8)*eta if branch == 0 else F(5,36)

    return (
        (F(2,3)+2*t)*(1-q)
        -F(1,9)*(1-2*q)*u
        -rH*(
            (1-q)*(u-F(branch+1,7))
            +2*(1-F(branch+1,7))
        )
    )

def verify_coefficients():
    results = []
    for branch in (0,1,2):
        count = zero = 0
        minimum = minconstant = None

        for t in T:
            ax = axes(t)
            if branch < 2:
                offset_cases = product(
                    (0,1), repeat=len(ax)
                )
            else:
                offset_cases = [tuple(0 for _ in ax)]

            for offsets in offset_cases:
                if branch < 2:
                    free = [
                        h for h,b in zip(ax,offsets) if b
                    ]
                else:
                    free = ax

                base = [F(0)]*3
                for h,b in zip(ax,offsets):
                    base[h] = F(b)

                allowance = (
                    H[branch,(t,offsets)]
                    if branch < 2 else F(0)
                )

                for ebits in product(
                    (0,1), repeat=len(ax)
                ):
                    e = [F(0)]*3
                    for h,bit in zip(ax,ebits):
                        bound = (
                            F(1) if h in free
                            else F(1,(3,125,343)[h])
                        )
                        e[h] = bit*bound

                    for qbits in product((0,1),repeat=3):
                        qn = tuple(
                            F(bit,p**4)
                            for bit,p in zip(
                                qbits,(3,5,7)
                            )
                        )

                        candidates = (
                            (0,1) if branch < 2 else (0,)
                        )
                        for candidate in candidates:
                            for dbits in product(
                                (0,1),repeat=len(free)
                            ):
                                deriv = [
                                    h for h,b
                                    in zip(free,dbits) if b
                                ]
                                value = F(0)

                                for ibits in product(
                                    (0,1),repeat=len(deriv)
                                ):
                                    ind = base.copy()
                                    for h,b in zip(
                                        deriv,ibits
                                    ):
                                        ind[h] += b

                                    rr = residual(
                                        t,tuple(ind),
                                        tuple(e),qn,
                                        branch,candidate
                                    ) + allowance

                                    value += (
                                        (-1)**(
                                            len(deriv)
                                            -sum(ibits)
                                        )
                                        *rr
                                    )

                                count += 1
                                if value < 0:
                                    raise ArithmeticError(
                                        (
                                            branch,t,offsets,
                                            e,qn,candidate,
                                            deriv,value
                                        )
                                    )
                                if value == 0:
                                    zero += 1
                                else:
                                    minimum = (
                                        value
                                        if minimum is None
                                        else min(minimum,value)
                                    )
                                if not deriv:
                                    minconstant = (
                                        value
                                        if minconstant is None
                                        else min(
                                            minconstant,value
                                        )
                                    )

        if branch == 2 and minconstant < F(1691,120000):
            raise ArithmeticError("C-anchor strict margin")
        results.append(dict(anchor=("A","B","C")[branch], coefficient_checks=count,
                            zero_coefficients=zero, least_positive=minimum,
                            least_constant=minconstant))
        residual.cache_clear()

    # Full infinite geometric allowance tails.
    tails = []
    for branch in (0,1):
        cost = F(0)

        for t,offsets in GROUPS:
            mass = F(1)
            oi = 0
            active = (
                t[0] == 3,t[1] == 1,t[2] == 1
            )

            for h,on in enumerate(active):
                p = (3,5,7)[h]
                if not on:
                    exponent = t[0] if h == 0 else 0
                    mass *= F(1,p**exponent)
                else:
                    b = offsets[oi]
                    oi += 1
                    start = (3 if h == 0 else 1)+b
                    mass *= F(1,p**start)
                    if b:
                        mass *= F(p,p-1)

            cost += mass*H[branch,(t,offsets)]

        loss = min(
            anchor_loss(
                branch,
                tuple(
                    F(bit,p**4)
                    for bit,p in zip(bits,(3,5,7))
                )
            )
            for bits in product((0,1),repeat=3)
        )

        expected = F(
            350909 if branch == 0 else 282449,
            1037232
        )
        if loss != expected:
            raise ArithmeticError("anchor loss mismatch")
        if not cost < loss:
            raise ArithmeticError(
                ("branch gap",branch,cost,loss)
            )

        tails.append(dict(anchor=("A","B")[branch], allowance_total=cost,
                          anchor_loss_lower=loss, strict_gap=loss-cost))
    return dict(transport_types=len(T), active_transport_coefficients=len(TH)-1,
                allowance_subtypes=len(GROUPS), coefficients=results, allowances=tails)



def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def typ(v):
    a,j,k=v
    return (min(a,3),int(j>0),int(k>0))

def residue(a,c):
    if a==0:return 0
    if a==1:return 0 if c<2 else 1
    if a==2:return (0,3,4)[c]
    return (18,3,4)[c]

def category_vertex(v,c):
    return (*v,residue(v[0],c))

def coordinate_tuple(N,v):
    a,j,k=v
    indices=(F(a-3 if a>=3 else 0),F(j-1 if j else 0),F(k-1 if k else 0))
    ends=(F(1,3**(N-a)) if a>=3 else F(0),F(1,5**(N-j)) if j else F(0),F(1,7**(N-k)) if k else F(0))
    qn=tuple(F(1,p**N) for p in (3,5,7))
    return indices,ends,qn

def verify_source_graph(N, source_type):
    source=source_type(N,True)
    mass=source.haar_normalization
    V=tuple(v for v in product(range(1,N+1),range(N+1),range(N+1)) if v!=(2,0,0))
    Z=tuple((0,j,k) for j,k in product(range(N+1),repeat=2))
    anchor=(2,0,0)
    require(len(V)+len(Z)+1==(N+1)**3,'All numerical labels, including unit and anchor')
    require((0,0,0) in Z,'Unit retained')
    type_index={t:i for i,t in enumerate(T)}

    @lru_cache(None)
    def raw(v,c):
        a,j,k=v
        return source.mass(a,residue(a,c),j,k)*mass

    @lru_cache(None)
    def pair(v,c,w,b):
        return source.pair_mass(category_vertex(v,c),category_vertex(w,b))*mass

    @lru_cache(None)
    def capacities(v,w):
        K0=max(pair(v,c,w,b) for c,b in product((0,1),repeat=2))
        K1=pair(v,2,w,2)
        joined=tuple(max(a,b) for a,b in zip(v,w))
        winner=0 if joined[0]>=3 else 1
        expected=raw(joined,winner) if joined[0]>1 else raw(joined,0)
        require(K0==expected,'Actual root0 envelope '+str((N,v,w)))
        require(K1==raw(joined,2),'Actual compatible root1 intersection')
        return K0,K1

    @lru_cache(None)
    def U(v,c,branch):
        # Diagonal once, each distinct pair twice, anchor inside unary before max.
        return raw(v,c)+2*sum(pair(v,c,z,2) for z in Z)+2*pair(v,c,anchor,branch)

    @lru_cache(None)
    def flow(v,w):
        if v==w:return F(0)
        i,j=type_index[typ(v)],type_index[typ(w)]
        K0,K1=capacities(v,w)
        if i==j:
            sign=1 if v>w else -1
            theta=TH[i,i]
        else:
            sign=1 if i<j else -1
            theta=TH[min(i,j),max(i,j)]
        ans=sign*theta*(K0+K1)
        require(abs(ans)<=K0+K1,'Each original edge obeys capacity')
        return ans

    if N==4:
        selected=V
    else:
        chosen=set()
        for t in T:
            a,b,e=t
            options=((1,) if a==1 else (2,) if a==2 else (3,N), (0,) if b==0 else (1,N), (0,) if e==0 else (1,N))
            chosen.update(product(*options))
            chosen.add((a if a<3 else N//2,0 if not b else N//2,0 if not e else N//2))
        selected=tuple(sorted(chosen))
        require(all(v in V for v in selected),'Every sampled vertex is an actual variable label')
        require({typ(v) for v in selected}==set(T),'Every transport type sampled')

    comparisons=0
    edge_checks=0
    least_actual=None
    for v in selected:
        g=F(1,3**v[0]*5**v[1]*7**v[2])
        difference=F(0)
        divergence=F(0)
        for w in V:
            if v==w:continue
            K0,K1=capacities(v,w)
            difference+=K0-K1
            divergence+=flow(v,w)
            require(flow(v,w)==-flow(w,v),'Full-edge antisymmetry')
            edge_checks+=1
        indices,ends,qn=coordinate_tuple(N,v)
        for branch in (0,1,2):
            candidates=(0,1) if branch<2 else (0,)
            best=max(U(v,c,branch) for c in (0,1))
            if branch==2:
                envelope=(0 if v[0]>=3 else 1) if v[0]>1 else 0
                require(U(v,envelope,branch)==best,'C-anchor root0 unary maximizer')
            for candidate in candidates:
                unary=best if branch==2 else U(v,candidate,branch)
                d=unary-U(v,2,branch)+difference
                actual=(divergence-d)/g
                symbolic=residual(typ(v),indices,ends,qn,branch,candidate)
                require(actual==symbolic,'Source-to-residual identity '+str((N,v,branch,candidate,actual,symbolic)))
                comparisons+=1
                if branch==2:
                    least_actual=actual if least_actual is None else min(least_actual,actual)
                else:
                    active_axes=axes(typ(v))
                    offsets=tuple(int(v[h] > (3 if h==0 else 1)) for h in active_axes)
                    allowance=H[branch,(typ(v),offsets)]
                    require(actual+allowance>=0,'Same actual vertex satisfies branch allowance')
            # Explicitly verify max is taken after adding each candidate anchor interaction.
            require(min((divergence-(U(v,c,branch)-U(v,2,branch)+difference))/g for c in (0,1))==(divergence-(best-U(v,2,branch)+difference))/g,'Correct unary maximum')
    require(least_actual>=F(1691,120000),'C-anchor strict actual-row margin')

    # Anchor-only objective loss from the actual pair API, preserving its diagonal.
    losses=[]
    old_anchor=raw(anchor,2)
    for branch in (0,1):
        actual=old_anchor-raw(anchor,branch)
        actual+=2*sum(pair(anchor,2,z,2)-pair(anchor,branch,z,2) for z in Z)
        actual+=2*sum(pair(anchor,2,v,2)-pair(anchor,branch,v,2) for v in V)
        qn=tuple(F(1,p**N) for p in (3,5,7))
        require(actual==anchor_loss(branch,qn),'Actual anchor-only loss agrees with symbolic loss')
        losses.append(str(actual))

    return dict(N=N,variable_vertices=len(V),fixed_zero_depth_labels=len(Z),complete_labels=(N+1)**3,checked_vertices=len(selected),source_residual_equalities=comparisons,full_edge_comparisons=edge_checks,least_C_actual_margin=str(least_actual),anchor_losses=losses)


def square_value(qn, sums, weighted):
    """Return the complete centered square and its raw Haar normalization."""
    x, y, z = qn
    T3, T5, T7 = sums
    eta, q, u = F(1,18)+x/2, (1-y)/4, F(5,6)+z/6
    rA, rB = (F(11,8), F(5,4)) if weighted else (F(1), F(1))
    R1 = F(1,3)-(F(5,6)-x/2)*q
    normalization = rA*eta*(1-q)*(u-F(1,7))+(rB/9)*(1-q)*(u-F(2,7))+R1*u
    numerator = (rA*eta*(1-q+T5)*(u-F(1,7)+T7)
                 +(rB/9)*(1-q+T5)*(u-F(2,7)+T7)
                 +4*(R1+T5/3)*(u+T7)
                 +(T3-1)*(1-2*q+T5)*(u+T7))
    require(normalization > 0, 'Positive actual source normalization')
    return numerator/normalization, normalization


def centered_value(N, weighted=False):
    require(type(N) is int and N >= 4 and type(weighted) is bool,
            'Uniform source value requires N>=4 and a specified law')
    x, y, z = (F(1,p**N) for p in (3,5,7))
    sums = (2-(N+2)*x, F(7,8)-F(4*N+7,8)*y, F(5,9)-F(3*N+5,9)*z)
    return square_value((x,y,z), sums, weighted)[0]


def verify_values(source_type):
    values = []
    for N in (4,5,12,24):
        x, y, z = (F(1,p**N) for p in (3,5,7))
        sums = (2-(N+2)*x, F(7,8)-F(4*N+7,8)*y, F(5,9)-F(3*N+5,9)*z)
        require(all(total == sum(F(2*h+1,p**h) for h in range(1,N+1))
                    for p,total in zip((3,5,7),sums)), 'Exact finite pair-multiplicity sums')
        for weighted in (False,True):
            result = centered_value(N,weighted)
            require(result == source_type(N,weighted).centered_square(),
                    f'Complete actual centered square N={N}, weighted={weighted}')
            values.append(dict(N=N,weighted=weighted,value=result))
    limits = []
    for weighted, expected in ((False,F(1829,72)),(True,F(671791,29142))):
        result, normalization = square_value((F(0),)*3,(F(2),F(7,8),F(5,9)),weighted)
        require(result == expected, 'Exact limiting square')
        limits.append(dict(weighted=weighted,value=result,normalization=normalization))
    return dict(finite=values,limits=limits)


def verify_all(source_type):
    return dict(scope='Both specified actual F_N laws, every N>=4: complete centered4 maximum and uniqueness after source-preserving compression. No weighted pair-LP, pre-compression uniqueness, arbitrary-source, later-prime or unrestricted covering conclusion.',
                transport=verify_coefficients(),
                actual_source_graph=[verify_source_graph(N,source_type) for N in (4,12)],
                centered_values=verify_values(source_type))


def verify_degrees():
    """Independent optional SymPy audit of the unbounded coefficient step."""
    import sympy
    variables = sympy.symbols('A J K E3 E5 E7 x y z')
    cases = 0
    for t in T:
        for branch in (0,1,2):
            for candidate in ((0,1) if branch < 2 else (0,)):
                expression = residual(t,variables[:3],variables[3:6],variables[6:],branch,candidate)
                degrees = sympy.Poly(sympy.expand(expression),*variables).degree_list()
                require(all(degree <= 1 for degree in degrees),
                        f'Residual is separately affine: {(t,branch,candidate,degrees)}')
                cases += 1
        residual.cache_clear()
    for branch in (0,1):
        expression = anchor_loss(branch,variables[6:])
        degrees = sympy.Poly(sympy.expand(expression),*variables[6:]).degree_list()
        require(all(degree <= 1 for degree in degrees), 'Separately affine anchor loss')
    return dict(sympy_version=sympy.__version__,residual_cases=cases,
                anchor_cases=2,degree_bound_in_each_variable=1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--check-degrees', action='store_true', help='Optional independent SymPy degree audit')
    args = parser.parse_args()
    if args.check_degrees:
        print(json.dumps(verify_degrees(),indent=2))
        return
    path = Path(__file__).resolve().with_name('source_full_square.py')
    spec = importlib.util.spec_from_file_location('uniform_cut_source',path)
    require(spec is not None and spec.loader is not None, 'Readable source API')
    source = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(source)
    print(json.dumps(verify_all(source.CompressedSource),default=str,indent=2))


if __name__ == '__main__':
    main()
