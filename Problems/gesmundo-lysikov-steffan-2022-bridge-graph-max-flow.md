---
slug: gesmundo-lysikov-steffan-2022-bridge-graph-max-flow
bibkey: gesmundo2025bridge
doi: 10.1007/s00031-024-09863-2
url: https://arxiv.org/abs/2212.09794v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowMinCut.result
---

# Quantum max-flow equals min-cut in the symmetric bridge regions

## Problem

F. Gesmundo, V. Lysikov and V. Steffan, *Quantum max-flow in the bridge graph*,
arXiv:2212.09794v2, Conjecture 1.4 (also Conjecture 3.14), state:
“Let $(a,b),(a',b')\in U_w\cup V_w\cup W_w$. Then”
$\operatorname{QMaxFlow}=\operatorname{QMinCut}=\min\{ab',a'b\}$.
Conjecture 3.15 is the width-three case. The
[literature note](../Library/QuantumBounds/gesmundo2025bridge.md) gives the
verbatim source clauses and locators. [#14652](https://github.com/the-omega-institute/trureturing/issues/14652)
records the complete target and literature scope.

## Motivation

`QuantumMaxFlowMinCut.result` proves both equalities at width three, for every
positive natural dimension quadruple in the two symmetric regions. The matrices
are over $\mathbb C$. The source letters $(a,b,a',b')$ correspond to Lean's
$(a,b,c,d)$, and the delivered flattening is the transpose of the source's;
rank is invariant under transpose. The attained supremum definition represents
the source's maximum, by `QuantumMaxFlowBound.QMaxFlow_attained`.

## Gap

The preregistration records the source, MathDB and citing-work searches; no
settlement was found in that searched scope. This is a bounded literature
reading, not an exhaustive originality claim. The width-three Lean conclusion
supplies the hypothesis of source Proposition 3.18. That general-width
implication remains a literature theorem rather than a formalized Lean bridge.

## Route

For $a>0$ and $t=b/a\ge1$, the smaller root of $t^2-3t+1$ is below $1$.
Consequently $a\le b\le(3+\sqrt5)a/2$ is equivalent to
$a\le b$ and $a^2+b^2\le3ab$. Apply the same calculation to $(c,d)$.
On this domain the source's cut formula $\min(3ac,ad,bc)$ equals
$\min(ad,bc)$; `QuantumMaxFlowBound.cone_QMinCut` proves this integer equality.

The construction uses rational three-slice matrices. A backward cyclic shift
and a forward cyclic shift with closing weight $1/2$ interact through floor
selectors. Its strictly positive shift is $\kappa=p$. The exact higher-order
Schur equations reduce full rank to the shifted cyclic resolvent, and a balanced
interval count forces its relevant periodic recurrence to vanish. Short and
long reservoirs give every strict base. Rational-to-complex transfer preserves
rank. Castling preserves the deficit, and strong induction on $b+d$ reaches
all cone pairs, including square, mixed and descended cases.

## Falsifier

A positive quadruple satisfying both cone inequalities and whose maximum
complex three-slice rank is below $\min(ad,bc)$ would falsify the width-three
claim. Failures of a particular construction outside its stated conditions
are method boundaries, not counterexamples to the proved conjecture.

## Evidence

The seven supporting modules have admission basis `escape-witness`, with
content theorems `QuantumMaxFlowBound.widthTwo_proved`,
`CastlingDeficit.castling_proved`, `FloorSelectorCycles.balanced_cycle_zero`,
`CyclicResolvent.schur_rank`, `ShiftPencilBlocks.pencil_rank_of_le`,
`ReservoirSchur.short_short_witness` and `LongReservoir.base_witness`.
The settling `QuantumMaxFlowMinCut.result` has admission basis
`open-problem-resolution` (#14652; Proved). Their axiom closures are contained
in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The escape audit of the 68 public theorems is unfinished:
[#14762](https://github.com/the-omega-institute/trureturing/issues/14762).
The result is a proof, so the designated-refutation exemption does not apply.
Missing source-family reconstruction and variation/sensitivity/dependence
proofs are audit obligations; they do not replace or weaken the mathematical
statements.

## Triage

### What the settlement shows

- **Proved — rational width-three construction.** The symbolic slices use backward
  and forward cyclic permutations, closing weight $1/2$, floor selectors and
  $\kappa=p>0$. `ReservoirSchur.short_short_witness` and
  `LongReservoir.base_witness` give the rank witnesses. These are arbitrary-dimension
  constructions, not a bounded enumeration of matrix certificates.
- **Proved — exact Schur complement and balance.**
  `CyclicResolvent.schur_rank` obtains $\min(AD,BG)$ for every positive shift
  under $0<B\le A$ and $0<D\le G$.
  `FloorSelectorCycles.balanced_cycle_zero` provides the balanced periodic
  recurrence step; the short and long reservoir equations yield full rank on
  every strict same-depth base in `LongReservoir.base_witness`.
- **Proved — castling transport.** `CastlingDeficit.castling_proved` preserves the
  deficit, and `QuantumMaxFlowMinCut.result` uses simultaneous cone descent
  to reach the entire cone. Rational witnesses transfer to complex matrices
  through `QuantumMaxFlowBound.rationalWitness_full_rank`.
- **Proved via literature — general width.** Source Proposition 3.18, page 20,
  derives Conjecture 1.4 for every $w\ge3$ from the delivered width-three
  conclusion. The implication is a literature reading with the source's
  hypotheses; the implication is not formalized in this delivery. The source results that take the
  symmetric-region equality as a premise can use this conclusion at width
  three and Proposition 3.18 for the general-width premise.
- **Computed — $\kappa=0$ core boundary.** For multiplicities $(3,2,4,3)$ the
  unshifted cyclic core has exact rational rank $7$, against target $8$.
- **Computed — $p=0$ extension boundary.** With $1\le a,c\le14$, both computed
  depths zero, ordered positive cone pairs and positive width-two defect,
  the literal extension is deficient on $261/3364$ pairs over
  $\mathbb F_{1000003}$. This finite-field statistic is not an exact rational
  count. The specific dimension pair $(5,13),(7,18)$ has exact rational rank
  $88$ against target $90$, so the literal extension fails over $\mathbb Q$.
- **Proved in the source — strict gaps outside the symmetric region; not formalized here.**
  Corollaries 1.2–1.3 and Theorem 3.8(2) establish
  $\operatorname{QMaxFlow}<\operatorname{QMinCut}$ outside the symmetric region.
  For $w=3$, $z=(1,3,8)$, $p=1$ and $\alpha=\beta=1$, the two pairs
  $(a,b)=(a',b')=(4,11)$ lie in $X_3$, outside the cone:
  $4^2+11^2=137>132=3\cdot4\cdot11$.
  The source formula gives $\operatorname{QMaxFlow}=43<44=\operatorname{QMinCut}$.
- **Proved — the symmetric conjecture in source §1.3(1).**
  `QuantumMaxFlowMinCut.result` settles its width-three case; source Proposition 3.18
  supplies general width as literature evidence.
- **Open — other graphs and periodic translation-invariant matrix product states.**
  The questions in source §1.3(2) are outside the scope of these declarations.

Source §1.3 states exactly (arXiv:2212.09794v2, page 7):

> 1.3. Open questions. We identify some open ends of this work.
>
> (1) One open task is Conjecture 1.4. The reduction discussed in Section 3.4 guarantees
> that the case w = 3 is equivalent to the full conjecture.
>
> (2) We believe that methods similar to ours can be applied to graphs that are not
> bridge graphs. For example, it would be interesting to see if one can calculate
> the quantum max-flow in translation-invariant matrix product states with periodic
> boundary conditions – which is the main example in prior work on the quantum
> max-flow where it was used to show separations between quantum min-cut and
> quantum max-flow [GLW18].
- **Proved — independence from source Theorem 3.1.**
  `CastlingDeficit.castling_proved` is derived from the module's field-linear
  algebra construction. It does not assume the source's castling theorem.

### Reproducible boundary computation

Both computed bullets use the following Python program (dependencies: NumPy
and SymPy). The measured command is
`python3 /tmp/op-gls/rework/boundary-check.py`,
exit $0$; source SHA-256 `9df34d66155c6e0c369f70e756f688dac611e7b0d6e3d8297631d329a1d22f9a`. The complete source below can be saved
under any filename and run with Python 3.

```python
import json, numpy as np, sympy as sp
P = 1_000_003

def rank_mod(a):
    a = np.array(a, dtype=np.int64, copy=True) % P
    nr, nc = a.shape
    r = 0
    for c in range(nc):
        piv = np.flatnonzero(a[r:, c])
        if piv.size == 0:
            continue
        s = r + int(piv[0])
        if s != r:
            a[[r, s]] = a[[s, r]]
        inv = pow(int(a[r, c]), P - 2, P)
        a[r, c:] = (a[r, c:] * inv) % P
        if r + 1 < nr:
            f = a[r + 1:, c].copy()
            nz = f != 0
            if np.any(nz):
                a[r + 1:, c:] = (a[r + 1:, c:] - f[:, None] * a[r, c:]) % P
        r += 1
        if r == nr:
            break
    return r

def rectangular(rows, cols):
    z = np.zeros((rows, cols), dtype=np.int64)
    for i in range(min(rows, cols)):
        z[i, i] = 1
    return z

def shift_block(x):
    s1 = np.zeros((x, x + 1), dtype=np.int64)
    s2 = np.zeros_like(s1)
    for i in range(x):
        s1[i, i] = 1
        s2[i, i + 1] = 1
    return s1, s2

def transposed_shift_block(x):
    a, b = shift_block(x)
    return a.T.copy(), b.T.copy()

def cyclic_data(A, B, G, D):
    """Return X,Y,B,D over F_P for the normalized short-short orientation."""
    U = np.zeros((A, A), dtype=np.int64)
    V = np.zeros((G, G), dtype=np.int64)
    for i in range(A):
        U[(i - 1) % A, i] = 1
    for j in range(G - 1):
        V[j + 1, j] = 1
    V[0, G - 1] = (P + 1) // 2
    Bm = np.zeros((B, A), dtype=np.int64)
    Dm = np.zeros((G, D), dtype=np.int64)
    for k in range(B):
        Bm[k, (k * A) // B] = 1
    for h in range(D):
        Dm[(h * G) // D, h] = 1
    return (-U) % P, V, Bm, Dm

def base_slices(p, alpha, beta, gamma, delta):
    a = p * alpha + (p + 1) * beta
    b = (p + 1) * alpha + (p + 2) * beta
    c = p * gamma + (p + 1) * delta
    d = (p + 1) * gamma + (p + 2) * delta
    M1 = np.zeros((a, b), dtype=np.int64)
    M2 = np.zeros((a, b), dtype=np.int64)
    N1 = np.zeros((d, c), dtype=np.int64)
    N2 = np.zeros((d, c), dtype=np.int64)
    row_m = [i * p for i in range(alpha)] + [alpha * p + i * (p + 1) for i in range(beta)]
    col_m = [i * (p + 1) for i in range(alpha)] + [alpha * (p + 1) + i * (p + 2) for i in range(beta)]
    row_n = [i * (p + 1) for i in range(gamma)] + [gamma * (p + 1) + i * (p + 2) for i in range(delta)]
    col_n = [i * p for i in range(gamma)] + [gamma * p + i * (p + 1) for i in range(delta)]
    for i in range(alpha):
        r1, r2 = shift_block(p)
        M1[np.ix_(range(row_m[i], row_m[i] + p), range(col_m[i], col_m[i] + p + 1))] = r1
        M2[np.ix_(range(row_m[i], row_m[i] + p), range(col_m[i], col_m[i] + p + 1))] = r2
    for i in range(beta):
        r1, r2 = shift_block(p + 1)
        rr = range(row_m[alpha + i], row_m[alpha + i] + p + 1)
        cc = range(col_m[alpha + i], col_m[alpha + i] + p + 2)
        M1[np.ix_(rr, cc)] = r1
        M2[np.ix_(rr, cc)] = r2
    for j in range(gamma):
        r1, r2 = transposed_shift_block(p)
        rr = range(row_n[j], row_n[j] + p + 1)
        cc = range(col_n[j], col_n[j] + p)
        N1[np.ix_(rr, cc)] = r1
        N2[np.ix_(rr, cc)] = r2
    for j in range(delta):
        r1, r2 = transposed_shift_block(p + 1)
        rr = range(row_n[gamma + j], row_n[gamma + j] + p + 2)
        cc = range(col_n[gamma + j], col_n[gamma + j] + p + 1)
        N1[np.ix_(rr, cc)] = r1
        N2[np.ix_(rr, cc)] = r2
    M3 = np.zeros((a, b), dtype=np.int64)
    N3 = np.zeros((d, c), dtype=np.int64)
    def put_m(U, r, s):
        for i in range(U.shape[0]):
            for j in range(U.shape[1]):
                M3[row_m[alpha + i] + r, col_m[j] + s] = U[i, j]
    def put_n(V, r, s):
        for i in range(V.shape[0]):
            for j in range(V.shape[1]):
                N3[row_n[i] + r, col_n[gamma + j] + s] = V[i, j]
    if alpha >= beta and gamma >= delta:
        X, Y, Bm, Dm = cyclic_data(alpha, beta, gamma, delta)
        for i in range(alpha):
            for j in range(alpha):
                M3[row_m[i], col_m[j]] = X[i, j]
        for i in range(gamma):
            for j in range(gamma):
                N3[row_n[i], col_n[j]] = Y[i, j]
        for r in range(p + 1):
            put_m(Bm, r, p - r)
            put_n(Dm, p - r, r)
        reason = 'short-short cyclic'
    elif alpha <= beta and gamma <= delta:
        X, Y, Bm, Dm = cyclic_data(beta, alpha, delta, gamma)
        X, Y, Bm, Dm = X.T.copy(), Y.T.copy(), Bm.T.copy(), Dm.T.copy()
        for i in range(beta):
            for j in range(beta):
                M3[row_m[alpha + i], col_m[alpha + j]] = X[i, j]
        for i in range(delta):
            for j in range(delta):
                N3[row_n[gamma + i], col_n[gamma + j]] = Y[i, j]
        for r in range(p + 1):
            put_m(Bm, r, p - r)
            put_n(Dm, p - r, r)
        reason = 'long-long cyclic'
    elif (alpha <= beta and delta <= gamma) or (alpha >= beta and gamma <= delta):
        put_m(rectangular(beta, alpha), p, 0)
        put_n(rectangular(gamma, delta), 0, p)
        reason = 'single'
    else:
        raise AssertionError((alpha, beta, gamma, delta))
    return (M1, M2, N1, N2, M3, N3, (a, b, c, d), reason)

def flow_rank(slices, dims):
    M1, M2, N1, N2, M3, N3 = slices
    a, b, c, d = dims
    F = (np.kron(M1, N1) + np.kron(M2, N2) + np.kron(M3, N3)) % P
    return rank_mod(F)


A,B,G,D = 3,2,4,3
X,Y,Bm,Dm = cyclic_data(A,B,G,D)
def rational(m):
    return sp.Matrix([[sp.Rational(1,2) if int(v)==(P+1)//2 else -1 if int(v)==P-1 else int(v) for v in row] for row in m])
X,Y,Bm,Dm=map(rational,[X,Y,Bm,Dm])
core=sp.kronecker_product(Bm,sp.eye(G))*(sp.eye(A*G)+sp.kronecker_product(X,Y)).inv()*sp.kronecker_product(sp.eye(A),Dm)
assert core.rank()==7 and min(B*G,A*D)==8
pairs=[(a,b) for a in range(1,15) for b in range(a+1,3*a) if a*a+b*b<=3*a*b]
count=failures=0
for a,b in pairs:
    m=b-a;p=(a-1)//m;beta=a-p*m;alpha=m-beta
    if p!=0:continue
    for c,d in pairs:
        n=d-c;q=(c-1)//n;delta=c-q*n;gamma=n-delta
        if q!=0 or min(alpha*delta,beta*gamma)==0:continue
        slices=base_slices(0,alpha,beta,gamma,delta)
        rank=flow_rank(slices[:6],(a,b,c,d))
        count+=1;failures+=rank!=min(a*d,b*c)
assert (failures,count)==(261,3364),(failures,count)
print(json.dumps({"kappa0":{"multiplicities":[A,B,G,D],"field":"Q","rank":core.rank(),"target":8},"p0":{"max_a_c":14,"scope":"positive ordered cone pairs with both depths zero and positive width-two defect","field_prime":P,"pairs":count,"deficient":failures}}))

exact_slices=base_slices(0,3,5,4,7)
assert exact_slices[6]==(5,13,7,18)
qM1,qM2,qN1,qN2,qM3,qN3=map(rational,exact_slices[:6])
exact_p0=sp.kronecker_product(qM1,qN1)+sp.kronecker_product(qM2,qN2)+sp.kronecker_product(qM3,qN3)
assert exact_p0.rank()==88
print(json.dumps({"p0_exact":{"dimensions":[5,13,7,18],"field":"Q","rank":88,"target":90}}))
```

## ASSUMED-UNVERIFIED

The literature search is bounded to the scope in #14652. Proposition 3.18 is
not part of the delivered Lean proof. Successful kernel checks do not establish
that every source-family audit target is `DTR-Declared`; #14762 states the
missing registration evidence. No uniform extension of the boundary experiment
is claimed.
