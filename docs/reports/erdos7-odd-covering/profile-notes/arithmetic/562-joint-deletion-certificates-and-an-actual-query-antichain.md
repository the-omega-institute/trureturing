# Joint deletion certificates and an actual occupied-query antichain

Weighted original/query intersections give an exact improvement of the
complete-query hinge estimate. The improvement must be certified for
queries maximizing under the same final survivor law. Ordinary pairwise
original intersections do not supply those weighted data.

A concrete irredundant family of twenty distinct odd numerical moduli
shows why an occupied-query substitute is insufficient: its jointly
maximizing occupied queries have a positive hinge, but the actual
original union deletes none of that hinge. The same family also exceeds
a proposed raw exponential-moment budget. These are counterexamples to
the two specified criteria, not to the complete-query target or Erdős #7.
The family belongs to the positive class in
[report561](561-all-three-rooted-supports-have-a-common-query-law.md).

All statements below are ordinary mathematics and exact finite
computation. No Lean declaration or new Lean verification is claimed.

## 1. The weighted deletion projection

Fix a probability space with reference law mu, actual original events
A_1,...,A_m, W=union_i A_i and U=W^c. Let nu be one probability law
supported on U with dnu/dmu<=kappa. Choose one finite collection of
nonunit numerical query labels and their phases simultaneously; write

    N=sum_d 1_Cd, h=(N-tau)_+, tau>=0.

Assume E_mu h<=B. Define

    b_i=E_mu[h*1_Ai],
    Q_ij=E_mu[h*1_Ai*1_Aj].                         (JD1)

Q is a positive semidefinite Gram matrix for the measure h dmu.
If t belongs to its kernel, sum_i t_i 1_Ai vanishes h dmu-almost
everywhere, and t.b=0. Hence b lies in range(Q). With Q^dagger denoting
the Moore-Penrose inverse, set

    Delta=b^T Q^dagger b
         =sup_(t: t^T Q t>0) (t.b)^2/(t^T Q t),     (JD2)

where Delta=0 if Q=0. Because every A_i lies in W,

    t.b=<1_W,sum_i t_i 1_Ai>_(h dmu).

Cauchy-Schwarz gives

    0<=Delta<=E_mu[h*1_W].                         (JD3)

The support and density conditions therefore imply

    E_nu N<=tau+kappa*(B-Delta).                   (JD4)

Indeed E_nu N<=tau+E_nu h and
E_nu h<=kappa*E_mu[h*1_U]. For an inexpensive certificate, put
J1=sum_i b_i and J2=sum_(i,j)Q_ij. If J2>0 then
Delta>=J1^2/J2; if J2=0 the Gram structure gives J1=0.

This requires intersections weighted by the actual query hinge. Knowing
mu(A_i) and mu(A_i intersect A_j) alone is not the input in JD1: h
depends on the jointly selected query phases and can vanish precisely
where the original events lie.

## 2. The complete-query quantifier

For the fixed final law nu, let

    q_d(nu)=max_a nu([a]_d),
    R_D(nu)=sum_(d in D)q_d(nu)

for a finite nonunit label box D. There are simultaneous maximizing
phase selections, since each residue alphabet is finite and phases may
be selected independently after nu is fixed. Every such selection has
E_nu N=R_D(nu).

To use JD4 for this R_D, it suffices to find one maximizing selection
whose Delta is at least a certified delta. It is unnecessary to prove
the same debit for every tie-breaking selection. A favorable selection
that does not maximize under nu, however, controls its own expectation
and does not bound R_D.

For the complete all-height R_P, use increasing cofinal finite boxes
and the same nu throughout. A uniform B and delta on their chosen
maximizing selections give

    R_P(nu)<=tau+kappa*(B-delta)                    (JD5)

by monotone convergence of the nonnegative sums. To obtain a strict
target bound this right side must be strictly below the target, or an
equivalent uniform gap must be supplied. Separate strict finite-box
bounds approaching the target only give a non-strict limit.

Assuming the same B bounds the extended query layouts, there is a
finite certificate for uniformity of the debit. Fix a finite subfamily
D0 and one maximizing phase for each of its labels under nu.
Compute Delta0 by JD1--JD3 with h0=(sum_(d in D0)1_Cd-tau)_+.
For every larger box, retain those phases and maximize the new labels.
Its full hinge is at least h0 pointwise, and hence its actual deleted
hinge is at least Delta0. Thus JD5 holds with delta=Delta0. There is no
need to recompute the projection at every larger box.

More generally, phases in D0 need not maximize if their exact regret

    r0=sum_(d in D0)(q_d(nu)-nu(C_d))

is certified. The extended layout then has expectation R_D(nu)-r0.
Provided B bounds the complete hinge for these layouts, the same proof
gives R_P(nu)<=tau+kappa*(B-Delta0)+r0. The original/query weighted
data, the one final law, and either maximization or regret remain
essential parts of this finite certificate.

In the pure-source conditioning of
[report557](557-complete-query-comparison-allows-three-more-old-pair-towers.md),
nu=mu(.|U), s=mu(U)>0, kappa=1/s and the NONUNIT hinge threshold is5.
Its query-only comparison gives

    B5=19132074022251234990036997833948759259
         /18473247078046657922374787501704265625.

A uniform debit delta in the sense just stated would yield

    R_P(nu)<=5+(B5-delta)/s<565/51
    whenever delta>B5-(310/51)*s.                  (JD6)

Equivalently the permitted loss ell=1-s is
ell<1-(51/310)*B5+(51/310)*delta. This is a conditional improvement,
not a proof that every original family has a positive uniform debit.
The unit cylinder is absent from N; adding it changes the hinge
threshold to6.

## 3. Twenty actual originals with no occupied-hinge debit

Let Q0={5,7,11,13,17,19}, P={3} union Q0, and
M=product_(p in P)p=4849845. For each three-element subset S of Q0,
take the original and query

    d_S=3*product_(q in S)q,
    A_S=[0]_(d_S), C_S=[1]_(d_S).                  (JD7)

There are twenty distinct odd squarefree labels, all greater than one.
For each S, the CRT point with zero coordinates precisely on {3} union S
and one coordinates elsewhere lies in A_S and no other original.
Thus the family is actually irredundant, with explicit private points.

Use Haar H on Z/MZ, W=union_S A_S, U=W^c and nu=H(.|U).
Every original has ternary coordinate0, whereas every C_S has ternary
coordinate1. Therefore C_S is wholly contained in U. Since any residue
class of d_S has H mass1/d_S,

    nu(C_S)=1/(d_S*H(U))=q_(d_S)(nu).              (JD8)

These query phases simultaneously maximize all twenty occupied labels
under the same law. Let L_F=sum_S1_C_S. On W, L_F=0. In contrast, at
the all-one CRT point L_F=20. Exact counts are

| Quantity | Count over the period M |
| --- | ---: |
| Original union W |25127|
| Survivor U |4824718|
| Sum of (L_F-5)_+ |345|
| Sum of 1_W*(L_F-5)_+ |0|
| Sum of L_F, also its sum on U |30960|

For direct derivation, when x_3=1 and exactly j of the six other
coordinates equal1, L_F=choose(j,3). The numbers of points with loads
1,4,10,20 are respectively23320,1740,66,1. In particular the hinge
count is

    5*sum_(q in Q0)(q-1)+15=345.

Replacing the symbol1 by0 gives the same union count25127. Thus

    E_H(L_F-5)_+=23/323323>0,
    E_H[1_W*(L_F-5)_+]=0,
    sum_S q_(d_S)(nu)=15480/2412359.               (JD9)

Consequently no universal c>0 can satisfy

    E_H[1_W*(L_F-5)_+]>=c*E_H(L_F-5)_+

for all actual irredundant families and their simultaneously maximizing
occupied-query layouts. In JD1 with this h, every b_i and Q_ij is zero.
This does not imply that the debit for the COMPLETE nonunit query load
is zero. This occupied subset supplies no positive finite debit, even
though such a subset can supply one in other families as explained above.

The SAME family supplies a positive certificate when the query inventory
is enlarged to all127 nonunit squarefree divisors of M. Choose residue1
for every such divisor and write N0 for their total load. These phases
again all maximize under nu: in each residue fibre, changing a fixed
zero coordinate to a nonzero value can only remove original violations.
All nonzero values give the same survivor fibre size. Thus fixing all
query coordinates to1 attains the largest possible surviving fibre.

If j coordinates equal1, N0=2^j-1. On W, the ternary coordinate is0
and at least three other coordinates are0, so j<=3. The hinge
(N0-5)_+ is positive there exactly at the twenty points with three
Q0-coordinates zero and the other three one. Its value is2 and each
point belongs to exactly one original. Consequently JD1 gives

    b=(2/M)*1, Q=(2/M)*I_20,
    Delta=40/M=8/969969>0.                         (JD9a)

Here the projection equals the full actual deleted hinge. The enlarged
finite query sum and raw hinge are, respectively,

    R_D0(nu)=3377162/2412359,
    E_H(N0-5)_+=14646/95095.

Thus the vanished occupied-only debit is an omission of query relations,
not a vanished debit for every larger test family. These calculations
are on Z/MZ. For all-height use, explicitly lift H and nu with independent
Haar higher digits at every prime. The originals and finite queries
depend only on first digits, so the masses, maximizing phases and debit
persist. Applying the finite-certificate result then also requires a
uniform full-query hinge bound B for the lifted reference law. No
all-height numerical R_P value is inferred from the finite sum above.

## 4. The same family defeats a raw exponential budget

The all-one CRT point lies in U and has Haar mass1/M. Hence

    log E_H[1_U*exp(L_F)]>=20-log M>4
                         >51863873/25500000.       (JD10)

The middle inequality has a rational certificate: e>8/3 and

    8^16-M*3^16=72705052102411>0,

so e^16>M. Therefore the universal raw-moment upper bound by
51863873/25500000 is false even for this small actual family. Its
occupied-query expectation in JD9 is nevertheless small; a large raw
exponential moment does not imply failure of the desired survivor law.

There is also a separate accounting constraint on any entropy route.
[Report534](534-one-entropy-budget-controls-every-pure-prime-chain.md)
supplies R_unused+D_H<=log Lambda. The occupied pure-chain estimate
has the opposite entropy sign, R_pure,shallow-D_H<=sum_p log M_p.
Their sum spends and cancels that one D_H. After the tail allowance,
the conclusion is R_other<C, C=4522277/500000; it does not retain an
additional +D_H on its left side. A new bound
R_mixed,shallow-D_H<=F can therefore give only
R_total<C+D_H+F by this combination. Using F alone against the
remaining target budget requires another joint estimate or a separate
entropy bound. JD10 addresses the specified raw joint-moment shortcut;
it is not a claim that all entropy methods fail.

## 5. Reproduction and remaining scope

The [producer](../../frontier/cover-geometry/occupied_query_antichain.py)
and [result](../../frontier/cover-geometry/occupied_query_antichain.json)
enumerate2187 zero/one/other support patterns, weighted by their exact
CRT cardinalities. Independent zero-set and one-set formulas reproduce
the union, hinge and query counts. The private points, maximizing-query
mass bounds and rational exponential certificate are all checked.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/occupied_query_antichain.py
```

All85 explicit checks pass; `--output` selects another result path.
The [squarefree certificate producer](../../frontier/cover-geometry/full_squarefree_query_certificate.py)
and [result](../../frontier/cover-geometry/full_squarefree_query_certificate.json)
add691 checks of JD9a, including all2186 fixed zero/nonzero phase patterns
over the127 labels. They also reconstruct the load histogram independently
from the coefficients of product_(p in P)(p-1+t). Run it with the same
Python flags and optional `--output`.

The projection inequality and its complete-query quantifiers use the
proofs above, not these finite enumerations. What remains is an actual
arithmetic lower bound on the full weighted debit, or another joint
source/query construction, strong enough for unrestricted supports.
