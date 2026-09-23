[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Incidence forests with arbitrary original heights and support sizes

**Incidence-forest theorem.** Let a finite family have pairwise distinct
odd numerical moduli greater than one. Form the bipartite graph with one
vertex for each occurring prime, one vertex for each distinct original
prime support of cardinality at least two, and an edge for membership.
If this graph is a forest, the family does not cover the integers.
There is a probability supported on its actual full survivor set whose
density relative to full CRT Haar is at most

    K_F = 4^{c+h} product_{q not a root}(q-1),

where c counts incidence components, h counts nonsingleton support
vertices, and each component is rooted at 3 if it contains 3, or at any
prime otherwise. Thus full uncovered Haar mass is at least 1/K_F,
uniformly in the original exponents and residues. The empty family has
survival one. The constant is allowed to depend on the fixed forest and
its actual primes; it is not uniform as the forest grows.

**Large-prime continuation.** For each fixed head forest and prime set,
a computable cutoff permits arbitrary additional distinct original
classes whose largest prime is beyond that cutoff, without coverage.
Only head-only labels must obey the forest hypothesis; the tail can have
arbitrary support geometry and small-prime cofactors. Section 6 gives
the quantitative restart argument and an eventually terminating rational
cutoff search. No small numerical cutoff is asserted.

A support vertex may contain arbitrarily many primes. Many numerical
moduli may share one support vertex; all original exponent vectors and
residues remain separate throughout. This incidence graph differs from
the ordinary prime co-occurrence graph: a single support of size n makes
a star in the former and a clique on n vertices in the latter.

The rank-two argument extends the original-exponent inventory and
single-prime separators of
[Chapter 06](06-block-saturation-and-the-actual-crossing-budget.md).
The ordinary cactus theorem in
[Chapter 06b](06b-arbitrary-odd-cactus-graphs-are-noncovering.md),
the bounded-block full-density theorem in
[Chapter 34](34-uniform-head-density-from-thick-block-domains.md), and the
common-spine books of
[Chapters 36](36-common-spine-books-of-four-prime-pages.md) and
[37](37-full-density-and-large-prime-continuation-for-spine-books.md)
cover different geometries. Height-independent density and its
large-prime continuation are existing techniques; the additional input
here is an arbitrary-rank incidence-forest construction with actual
simultaneous extension volume. The source-independent attachment formula
in Section 5 can also be used on an already constructed head.

These are ordinary mathematical deductions and exact finite regression
calculations. They are not Lean theorems or a resolution of unrestricted
Erdős #7; public-literature priority has not been established.

## 1. Local original-exponent inventory

Let q be an odd prime and let T be a nonempty finite set of other
primes, each at least 5. Keep any finite family of distinct original
moduli with prime support exactly E={q} union T. Write each original as

    d_i=q^{a_i} product_{r in T} r^{b_(i,r)},  a_i,b_(i,r)>=1.

All coordinates have finite heights resolving every original exponent.
Let A_i be the actual parent q-cylinder, and define

    w_i=product_{r in T}r^{-b_(i,r)},
    c_T=product_{r in T}1/(r-1),
    D_T=product_{r in T}(r-3),
    L_E(x)=sum_i w_i 1_{A_i}(x).

For each fixed parent exponent a, numerical distinctness gives at most
one original class for every complete child exponent vector. Therefore

    sum_{i:a_i=a} w_i <= c_T.                         (I1)

This is a geometric upper bound for the finite original inventory; it
adds no classes. The same child exponent vector at different a remains
allowed and is charged separately in its original layer.

D_T is an integer at least 2. Set

    theta_E=(D_T-1/4)c_T,
    B_E={x:L_E(x)>=theta_E}.

The layers a=1,...,D_T-1 contribute at most (D_T-1)c_T pointwise.
Thus on B_E,

    sum_{i:a_i>=D_T} w_i 1_{A_i}(x) >= 3c_T/4.       (I2)

For ANY finite positive measure sigma on the parent coordinate, or a
larger old carrier containing that coordinate, integrating gives

    sigma(B_E) <= 4/(3c_T)
                   sum_{i:a_i>=D_T}w_i sigma(A_i).  (I3)

No independence, uniformity or old-source reweighting was used.
For parent Haar H_q, combine (I1) with H_q(A_i)=q^{-a_i}:

    H_q(B_E) <= 4/[3(q-1)] q^{-(D_T-1)}.            (I4)

## 2. Success gives a quantitative real extension

Suppose actual acceptable child domains S_r satisfy

    H_r(S_r)>=(r-3)/(r-1), r in T.

Their product has original child Haar mass at least D_T c_T. At a
fixed parent value x, the union of active ORIGINAL child rectangles
has Haar mass at most L_E(x). Therefore if x is outside B_E, the set

    A_E(x)=(product_{r in T}S_r)
              minus union_{i:x in A_i}(original child rectangle_i)

satisfies

    H_T(A_E(x)) > c_T/4.                            (I5)

This is an actual allowed tuple set, not independent marginal witnesses.
Uniform choice from it has density less than 4/c_T relative to the
unconditioned product Haar on all child coordinates.

The threshold pays a uniform positive extension volume. Merely proving
that the tuple set is nonempty would not suffice for the height-uniform
density theorem below.

## 3. Global incidence-forest construction

Let P be the primes of a finite distinct-odd original family. Form the
set of all distinct original supports E with cardinality at least two,
and join p to E exactly when p is in E. Suppose this bipartite graph
is a forest. Pure-power labels are kept at their prime vertices.

Root each component at 3 if it contains 3, and at an arbitrary prime
otherwise. A support vertex E has exactly one parent prime q and a
nonempty set T_E of child primes. All child primes are at least 5.
The descendants of different child support vertices are disjoint.

Work upward. At each prime q define S_q by deleting its original pure
classes and the B_E sets of its immediate child support vertices.
For each child r, assume inductively H_r(S_r)>=(r-3)/(r-1).
Then (I5) proves extension on every retained parent value for each
immediate support group. Different groups' choices can be made jointly
because their full descendant prime sets are disjoint.

To close the density induction, select one representative r_E from
each T_E. They are distinct actual primes. Since r-3>=2 at every child,
D_(T_E)>=r_E-3. Equation (I4) therefore gives

    sum_{E child of q} H_q(B_E)
      <= 4/[3(q-1)] sum_{E}q^{-(D_(T_E)-1)}
      <= 4/[3(q-1)] sum_{r>=5 odd}q^{-(r-4)}
      = 4q/[3(q-1)(q^2-1)].                         (I6)

Actual pure q-powers have total mass at most 1/(q-1). Hence

    H_q(S_q)>=1-1/(q-1)-4q/[3(q-1)(q^2-1)].         (I7)

At q=3 this lower bound is exactly 1/4. For q>=5 it is at least
(q-3)/(q-1): equivalently 4q<=3(q^2-1), which holds for q>=5.
This proves the nonroot induction. Every root also has acceptable
mass at least 1/4. Finite upward induction followed by (I5) gives
at least one complete avoiding tuple, and finite CRT gives an integer.

This proves noncoverage for arbitrary exponents, residues, support
sizes, component counts and numbers of original primes in this class.

## 4. Height-independent original Haar density

Let c be the number of incidence components, including isolated prime
vertices, and let h be the number of distinct nonsingleton supports.
Let H be original full CRT Haar. Construct a probability nu as follows:
choose each root uniformly on S_q; for every support vertex, conditional
on its already fixed parent value x, choose its whole child tuple
uniformly on A_E(x); continue downward.

Each root density is at most 4. By (I5), each conditional support-kernel
density is at most 4 product_{r in T_E}(r-1). Each nonroot coordinate is
introduced exactly once. Thus the resulting joint density satisfies

    nu <= K_F H,
    K_F=4^{c+h} product_{q not a root}(q-1).         (I8)

This product follows from the actual full-history conditional kernel
bounds, not from multiplying marginal caps. All samples avoid every
original class. If R_full denotes its actual full survivor set,

    H(R_full)>=1/K_F.                              (I9)

K_F depends on the finite prime-support forest and root choices but
not on any original exponent or residue. It need not stay bounded as
the prime forest grows. Empty families have survival one separately.

## 5. Attaching forests to an arbitrary existing source

Let an existing original family use prime set P0 and have survivor set
R. Let sigma be ANY probability supported on R, on old heights that
also resolve the parent exponents of all proposed new labels.

The added mixed-support incidence components must each meet P0 at
exactly one root prime. Their introduced interiors are pairwise disjoint
and have no other cross-edges or labels. Every introduced prime is at
least 5. All old-only original classes must already be among those
avoided by R; a newly added pure old-root class would require a separate
charge and is not silently included. Pure introduced-prime labels are
included in the upward S_r construction.

Construct interior S_r as above. For each boundary support E at its
old parent q, retain its original A_i,w_i,c_(T_E),D_(T_E). Let

    G=R minus union_{boundary E}B_E.

The unchanged-source inequality (I3) gives

    sigma(R minus G) <= sum_{boundary E} 4/(3c_(T_E))
                       sum_{i in E:a_i>=D_(T_E)}w_i sigma(A_i). (I10)

Every x in G has a simultaneous extension avoiding the entire old and
added original family. A probability kernel into 'new-coordinate tuple
or failure' preserves the old marginal exactly if the output includes
the unchanged old x: sample legal tuples on G and output (x,failure)
otherwise. Its failure probability is sigma(R minus G). Conditioning
on success would replace sigma by sigma(.|G) and is a different law.

For a whole cover consisting exactly of this old family and these
attachments, G is empty. Thus the right side of (I10) must be at least
one for every actual survivor probability sigma. The existence of such
a sigma presupposes R nonempty; no assertion is made if R is empty.

If sigma's marginal actual q-cylinder caps obey

    sigma(x_q=b mod q^a)<=K_q q^{-a},

then (I1) changes the corresponding boundary fee to at most

    4K_q/[3(q-1)] q^{-(D_(T_E)-1)}.                 (I11)

The K_q are supplied properties of this actual source, not universal
constants inferred from numerical-modulus distinctness.

## 6. A computable unrestricted large-prime tail

Fix the forest head's prime-support structure and roots, hence K_F.
There is a prime cutoff P_* depending only on that data such that no
family obtained by adding distinct original classes with largest prime
P^+(d)>P_* can cover. These additional labels may contain arbitrary
small-prime cofactors and unbounded support sizes; their incidence graph
is unrestricted. Head and tail numerical moduli remain globally distinct.

For a global prime index k>=10, with p_k at least every head prime,
put a(p)=(3p-1)/(p-1)^2. A sufficient finite test is

    K_F product_{odd p<=p_k}(1+a(p))
         <= k(log k+loglog k-3)^2.                  (I12)

Including the p=2 factor also suffices and is only weaker. Uniformly
lift nu to any newly needed head heights and to all
unused odd primes at most p_k. Its density is still at most K_F, and
it avoids every old class. Every added original class ends beyond p_k,
so there are no unpaid new exclusions in this initial carrier.

For two compatible old congruence cylinders modulo m,n, the joint
probability under this same lifted law is at most K_F/lcm(m,n).
Every complete-layout square therefore has bound

    Gamma <= K_F sum_{m,n|Q_old}1/lcm(m,n)
          <= K_F product_{odd p<=p_k}(1+a(p)),

because sum_{a,b>=0}p^{-max(a,b)}=1+sum_{e>=1}(2e+1)p^{-e}=1+a(p).
For each fixed layout this sum keeps the actual test residues;
incompatible cylinders only lower it.

To check the analytic consumer beyond its name, start the standard
full-Haar clipped kernels at p_k from this actual law. For any later
coordinate, conditional density is bounded by 1/(1-delta_p), and prefix
probabilities are preserved. Expanding the original next-fibre second
moment as in BBMST Lemmas 3.6--3.7 yields its hypothesis (20) with

    kappa=K_F product_{odd p<=p_k}(1+a(p)),  initial mass=1,
    M_j^(2) <= kappa/(p_j-1)^2
                  product_{k<i<j}(1+a(p_i)/(1-delta_i)).

For this moment expansion sum first over original labels (m,a),(n,b),
where a,b are the exponents of the new prime p_j. The old residues may
depend on a,b. Apply the same joint-cylinder cap to each original pair,
then sum p_j^{-a} and p_j^{-b} separately. This gives (p_j-1)^{-2}
without identifying residues belonging to different new exponents.
Subsequent distorted coordinates multiply the factors
1+a(p)/(1-delta_p) exactly as required by (20). The actual starting
joint density supplies K_F only once. Lemma 6.2 and Theorem 6.1 then
apply under (I12) and give noncoverage. This arbitrary-source restart
is an application of the moment argument, not a claim that nu came
from a prior canonical sequence of BBMST kernels.

Such a finite k exists and can be found using rational arithmetic.
The prime lower bound quoted and used in BBMST's own Theorem 6.1
implies p_j>=j log j eventually. For p>=7, a(p)<=4/p. Hence the
product in (I12) is O((log k)^4), whereas the right side is asymptotic
to k(log k)^2. No height appears in this comparison.

One can even avoid numerical logarithms when searching: at k>=256 put
m=floor(log_2 k), computed by integer bit length. The elementary
log2>=1/2 and loglog k>=0 show that

    k(m/2-3)^2 <= k(log k+loglog k-3)^2.

Its bracket is positive and it still grows as a fixed positive constant
times k(log k)^2. Enumerating primes and checking the product against
this rational lower bound must eventually succeed, giving a computable
P_*. No useful numerical magnitude of that cutoff is claimed here.

## Verification boundary

The analytic supplier is
[BBMST, *On the Erdős Covering Problem: the density of the uncovered set*](../../../../Library/Arith/balister2018covering.md),
[primary v1](https://arxiv.org/pdf/1811.03547v1), Lemmas 3.6--3.7 and
Section 6, especially hypothesis (20), Lemma 6.2 and Theorem 6.1.
The global prime index includes 2 and absent primes. The density restart
above verifies its moment hypothesis for the actual constructed source;
it does not identify that source with a canonical earlier distortion law.

The forest theorem alone makes no assertion about cyclic incidence
components: two branches may require incompatible values of a shared
child coordinate. The adjacent
[incidence-pseudoforest theorem](49-incidence-pseudoforests-with-arbitrary-original-heights.md)
handles one cycle per component by paying all cyclic constraints under
one common joint source.

The companion
[incidence_forest.py](../frontier/cover-geometry/incidence_forest.py)
uses only the Python standard library and exact rational arithmetic.
Its finite regressions pass with optimization enabled, using explicit
exceptions rather than removable assertions. It independently
reconstructs every local exceptional set, every actual child tuple set,
and the full resulting joint probability from original CRT labels. A
nine-label edge fixture at period 675 has a nonempty parent exceptional
set of three residues, full Haar survival 11/25, and generated law of
total mass one and maximum density 45/14<=64. A deliberately nonuniform
old source in that fixture has actual failure 1/2 and original deep-layer
fee 32/25, verifying the same-source inequality without substituting Haar.

An eight-label rank-four support with a child edge at period 45045 has
full Haar survival 380/1001. Its generated joint law again has mass one
and maximum density 1365/478<=184320. The first fixture checks genuine
pruning; the second checks multi-coordinate simultaneous extension and
subsequent descendant gluing. Their finite verification does not certify
the arbitrary-rank or all-height assertions; the preceding inequalities
and induction supply those conclusions.

The retained exact output is
[incidence_forest.json](../certificates/source_norms/cover-geometry/incidence_forest.json).
From the repository root, replay it with

```sh
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/incidence_forest.py --check
```
