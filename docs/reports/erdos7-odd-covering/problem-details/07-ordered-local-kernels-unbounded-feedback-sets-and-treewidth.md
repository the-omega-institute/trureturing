[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](18-four-vertex-blocks-and-cycle-breaking-vertices.md) · [Next](08-arbitrary-head-transfer-by-the-joint-load-invariant.md)

<a id="ordered-local-kernels-unbounded-feedback-sets-and-treewidth"></a>
#### Ordered local kernels: unbounded feedback sets and treewidth

A tail graph is `d`-degenerate when it admits an ordering in which every
vertex has at most `d` earlier neighbours. This allows unbounded maximum
degree, feedback vertex number, treewidth and component size. The actual
modulus labels and the conditional caps of the BBMST kernel yield:

| Head | Tail primes | Tail graph | Saturated-head mass upper bound |
|---|---|---|---:|
| Arbitrary `{3,5,7}` head | `q>=17` | any forest | `<0.955226` |
| Arbitrary `{3,5,7}` head | `q>=19` | `2`-degenerate | `<0.885762` |
| Arbitrary `{3,5,7}` head | `q>=23` | `5`-degenerate, including every planar graph | `<0.945592` |
| Complete star head | `q>73` | `20`-degenerate | `<0.990060` |

Every finite simple planar graph is `5`-degenerate, by its edge bound on
every subgraph. Thus the third row permits arbitrarily large grids and
arbitrarily many cycles; there is no bound on exponents or total prime
support. The last row means that any full star completion must have a
nonempty subgraph of minimum degree at least 21, equivalently a nonempty
21-core in its actual tail graph.

**Local class assignment and kernels.** Fix an ordering of the tail primes,
write `P_v` for the earlier neighbours of `v`, and assign every actual
class with nontrivial tail part to its latest tail prime `v`. Every other
tail prime in that modulus belongs to `P_v`. The assigned moduli have form
`m v^e product_(p in P_v) p^(f_p)`, where `m|Q`, `e>=1`, and `f_p>=0`.
Distinct original moduli mean at most one class for each full tuple; no
projected-modulus distinctness is presumed. Moduli containing all primes
of any allowed clique are included.

Fix `0<delta<=1/2` and put `K=1/(1-delta)`. Given the head `x` and the
entire earlier tail history, let `F_v` be the actual forbidden union in
`Y_v` from the classes assigned to `v`, and let `alpha_v=U_v(F_v)`. Choose
the new coordinate with the existing BBMST capped kernel (T4). Its density
relative to the uniform coordinate is `0` on `F_v` and `1/(1-alpha_v)`
off `F_v` when `alpha_v<=delta`; otherwise its density is
`(alpha_v-delta)/(alpha_v(1-delta))` on `F_v` and `K` off `F_v`.
This is normalized for every history, including completely forbidden
fibres, and everywhere bounded by `K`. Thus the original head marginal
stays `mu`, and every conditional cylinder obeys

\[
 \Pr(y_v=b\bmod v^e\mid x,\text{entire earlier history})
 \le K v^{-e}\quad(e\ge1).                            \tag{DG1}
\]

Conditional on a fixed `x`, an arbitrary set `J` of queried earlier
coordinates therefore satisfies the simultaneous-cylinder cap

\[
 \Pr\left(\bigcap_{p\in J}\{y_p=b_p\bmod p^{e_p}\}\mid x\right)
 \le\prod_{p\in J}Kp^{-e_p}.                          \tag{DG2}
\]

Remove the latest queried coordinate using (DG1) and the tower law, then
repeat. Unqueried intermediate coordinates integrate out without another
factor. No independence of the sequentially chosen coordinates, and no
conditioning on complete survival, is used.

The selected-coordinate passage in (DG2) now has a Lean proof in
[SequentialKernelCylinder.selected_cylinder_bound](../../../../D5/S3/Arith/Congruence/SequentialKernelCylinder.lean).
For arbitrary measurable alphabets, let `κ_n` be a Markov kernel from the
complete history through `n` to coordinate `n+1`. Fix `a<=b` and a selected
set `S` contained in `{a+1,...,b}`. If, at every complete history, each
selected coordinate event `E_i` has conditional kernel probability at most
`c_i`, then its joint probability under Mathlib's actual partial trajectory
kernel, conditioned on any fixed history through `a`, is at most
`prod_(i in S) c_i`. No independence, joint-cylinder estimate or
prefix-preservation premise is assumed. Induction removes the last
coordinate; selected coordinates use their one-step bound and unselected
coordinates use Mathlib's existing Markov prefix-preservation theorem.
This proves the probability-theoretic passage from the local caps to the
joint selected-cylinder bound. Instantiating the capped residue kernels,
retaining original modulus labels in the second-moment expansion, and the
prime-tail estimates remain separate formalization obligations.

**Only the actual earlier neighbours enter the moment bound.** Put
`s_v=sum_(e=1..H_v) v^(-e)` and `h_p=sum_(j=1..H_p)(2j+1)p^(-j)`.
Bound `alpha_v` by its raw uniform-fibre cylinder load and expand its
square. Group by the two full tail exponent tuples. If parent cylinders
are incompatible the intersection is empty. Otherwise (DG2) contributes
`K p^(-max(f_p,f'_p))` for each positive maximum, and `1` for two zero
exponents. These bounds hold separately at every `x`. What remains for
fixed exponent tuples is the cross moment of two partial head layouts;
completing missing head labels and Cauchy--Schwarz bound it by `G`.
There are exactly `2j+1` nonnegative exponent pairs with maximum `j`, so

\[
 \mathbb E\alpha_v^2
 \le Gs_v^2\prod_{p\in P_v}(1+Kh_p).                  \tag{DG3}
\]

The expectation is under the full sequential prefix law. This estimate
includes no factor for earlier vertices outside `P_v`; it does not bound
the Gamma of the entire accumulated head.

Let `V_v` be the event that the chosen `v` coordinate violates at least one
class assigned to `v`. The already-established capped-kernel bound (T4) gives

\[
 \Pr(V_v)=\frac{\mathbb E(\alpha_v-\delta)_+}{1-\delta}
 \le\frac{Gs_v^2}{4\delta(1-\delta)}
                         \prod_{p\in P_v}(1+Kh_p).    \tag{DG4}
\]

Later normalized kernels preserve the complete prefix marginal, so this
is also the probability of `V_v` in the final joint law. Outside the union
of these events every original tail class is avoided at its assigned
coordinate, and `mu` already avoids every head-only class. CRT supplies
an uncovered integer. A saturated head forces some `V_v` under every tail
sample, so preservation of the head marginal gives
`mu(saturated heads)<=Pr(union_v V_v)`. Consequently the head mass with no
avoiding lift is at most

\[
 \frac{G}{4\delta(1-\delta)}
       \sum_v s_v^2\prod_{p\in P_v}(1+Kh_p).          \tag{DG5}
\]

This formula also applies without any uniform bound on predecessor count,
whenever its actual weighted sum can be controlled.

**Distinct parents sharpen the uniform certificate.** For a lower cutoff
`q0`, list the allowed primes as `p_1<p_2<...`, and write

\[
 a_p=\frac1{p-1},\quad
 T_p=1+\frac{3a_p+2a_p^2}{1-\delta},\quad
 R_d=\prod_{i=1}^dT_{p_i}.
\]

The factors decrease with `p`. A vertex outside the first `d` primes has
parent product at most `R_d`; for `v=p_i` with `i<=d`, the vertex cannot
be its own parent, giving the smaller bound `R_d T_(p_(d+1))/T_(p_i)`.
Completing absent vertices by their nonnegative contributions proves

\[
 \sum_v a_v^2\prod_{p\in P_v}T_p
 \le R_d\left[S_{q0}+\sum_{i=1}^d a_{p_i}^2
                   \left(\frac{T_{p_{d+1}}}{T_{p_i}}-1\right)\right].
 \tag{DG6}
\]

Here `S_q0` is the independently checked prime-square upper bound from
(GS1), with the omitted smaller primes added exactly. Inserting (DG6) in
(DG5) yields the displayed table with, respectively,
`(q0,d,delta)=(17,1,11/25),(19,2,41/100),(23,5,37/100),(79,20,9/25)`.
The head constants are `1889/48` in the first three rows and `177` in the
last. The adjacent certificate recomputes the distinct-prime products,
the negative self-parent corrections and every strict rational comparison.
It also checks eight actual CRT instances modulo 1155, retaining all
15 distinct nonunit divisor labels and a nonuniform law on the two actual
surviving head residues modulo 3. Across 6160 complete assignments and
9200 conditional cylinder queries, the regression checks normalization,
selective-coordinate caps, the actual-load second moment, preservation
of assigned violation probabilities by later kernels, and the final
union bound. This exercises (DG2)--(DG4) with actual arithmetic classes.
The results are ordinary proofs and exact arithmetic, not a complete Lean
formalization of the kernel construction or its graph application.

The capped kernel itself is reused from (T4) and
[BBMST](../../../../Library/Arith/balister2018covering.md); the new point is retaining
only the actual earlier-neighbour coordinates in (DG2)--(DG5). The forest
and feedback-vertex arguments do not imply this bound when treewidth or
feedback vertex number is unbounded. For unrestricted tail support, (DG5)'s weighted predecessor products
still need control without a fixed degeneracy hypothesis. The next
criterion instead bounds the support of each original modulus.

<a id="bounded-tail-support-permits-arbitrary-co-occurrence-graphs"></a>
#### Bounded tail support permits arbitrary co-occurrence graphs

A restriction on each **original modulus**, rather than the degree of its
co-occurrence graph, gives a different noncoverage theorem. Suppose the
actual head survivors support a law with `Gamma<=G`, all tail primes are
at least `q0`, and each original modulus contains at most `s` distinct tail
primes. Its head part may be any divisor of the head period. All prime
exponents and the total number of primes are unrestricted. The following
strict bounds exclude coverage:

| Head | Tail primes | Maximum tail primes per original modulus | Threshold `delta` | Saturated-head mass upper bound |
|---|---|---:|---:|---:|
| Complete star through 73 | `q>73` | 2 | `2/5` | `<0.861` |
| Arbitrary `{3,5,7}` head | `q>=23` | 2 | `3/8` | `<0.947` |
| Head period divides 315 | `q>=17` | 3 | `3/10` | `<0.981` |
| Head period divides 945 | `q>=19` | 3 | `7/20` | `<0.989` |

There is **no graph restriction**: complete graphs with arbitrarily many
vertices are allowed. In particular, a covering completion of the full
star head must contain an original modulus with at least three tail prime
factors. For either finite-head row, a covering completion must contain a
modulus with at least four tail prime factors. These conclusions apply to
the named heads and cutoffs, not to an arbitrary odd covering family.

Order tail primes increasingly and use exactly the kernels, latest-prime
assignment and prefix-marginal preservation from (DG1)--(DG4). Put

\[
 a_p=\frac1{p-1},\qquad b_p=a_p+2a_p^2,\qquad
 K=\frac1{1-\delta},\qquad r=s-1,
\]
\[
 B_r(v)=\sum_{i,j=0}^r[x^iy^j]
       \prod_{q_0\le p<v}\bigl(1+Ka_p(x+y)+Kb_pxy\bigr),
 \quad\text{with the product over primes}.             \tag{RK1}
\]

For the two preceding exponent tuples in a squared load, a prime occurring
only on the left or only on the right contributes `K sum_(e>=1) p^-e=Ka_p`.
A prime occurring on both sides contributes
`K sum_(e,f>=1) p^-max(e,f)=Kb_p`: exactly `2j-1` positive exponent pairs
have maximum `j`. Its cap is `K`, not `K^2`, because the two cylinders
intersect in one cylinder. Each exponent tuple has at most `r` positive
entries, which is precisely the coefficient truncation in (RK1).

Distinct original moduli give at most one class per full tuple including
the head divisor. For each pair of tail tuples, complete the two partial
head layouts and apply Cauchy--Schwarz to their cross moment, giving `G`.
Thus (DG2) and the nonnegative exponent-pair expansion prove

\[
 \mathbb E\alpha_v^2\le Ga_v^2B_r(v),\qquad
 \mu(\text{saturated heads})
 \le\frac{G}{4\delta(1-\delta)}
             \sum_{v\ge q_0\atop v\text{ prime}}a_v^2B_r(v).\tag{RK2}
\]

Completing the preceding prime set and all exponent ranges only enlarges
this nonnegative upper bound. No projected-modulus distinctness is used.
For `r=1`, writing `A_v=sum_(q0<=p<v) a_p` and
`C_v=sum_(q0<=p<v) a_p^2`, the coefficient sum is exactly

\[
 B_1(v)=1+K(3A_v+2C_v)+K^2(A_v^2-C_v).                 \tag{RK3}
\]

The first two rows follow by a rational sum through `N=2^20` and an
all-integer dyadic remainder. Let `A_N,C_N` bound the corresponding prefix
sums. In block `(N2^j,N2^(j+1)]`, their bounds are `A_N+j+1` and
`C_N+2/N`, and the sum of `a_v^2` is at most `1/(N2^j)`.
Dropping the negative term in (RK3) yields the explicit tail bound

\[
 \frac1N\left[2+K(6A_N+12+4C_N+8/N)
                  +K^2(2A_N^2+8A_N+12)\right].       \tag{RK3a}
\]

For the finite sum, compute `A_v^2-C_v` as the nonnegative polynomial
`2 sum_(p<q<v) a_p a_q`, so rounding the individual `a_p` upward preserves
every inequality. The certificate retains the prime count, rounding
scale, finite sum and exact infinite-tail bound.

For the two `r=2` rows, a `3 by 3` positive coefficient recurrence computes
(RK1) through `N=2^20`; every arithmetic rounding is upward to the grid
`10^-12`. Let `A_N` and `B_N` be the certified upper bounds for the finite
sums of `a_p` and `b_p`. In the block `(N2^j,N2^(j+1)]`, even summing over
all integers gives

\[
 \sum a_v^2\le\frac1{N2^j},\qquad
 \sum_{q_0\le p<v}a_p\le A_N+j+1,\qquad
 \sum_{q_0\le p<v}b_p\le B_N+j+1+\frac2{N-1}.          \tag{RK4}
\]

The first inequality uses at most `N2^j` terms, each at most
`(N2^j)^-2`. Each earlier dyadic block adds at most one to the `a` sum;
the additional square sum is at most `1/(N-1)` by integral comparison.
Coefficientwise domination of the product in (RK1) by
`exp(A(x+y)+Bxy)` gives

\[
 B_2(v)\le E_2(A,B):=
       (1+A+A^2/2)^2+B(1+A)^2+B^2/2,                 \tag{RK5}
\]

where in block `j` one takes
`A=K(A_N+j+1)` and `B=K(B_N+j+1+2/(N-1))`.
Consequently the infinite remainder is at most
`N^-1 sum_(j>=0) 2^-j E_2(A,B)`. This is an exact degree-four polynomial
sum: `sum_(j>=0) j^k/2^j` equals `2,2,6,26,150` for `k=0,1,2,3,4`.
The resulting loss bounds are `0.9805125417500644...` and
`0.9883284628019068...`. The verifier checks the moment recurrence and
independently compares finite coefficient truncations with direct
exponent-tuple pair enumeration. The arbitrary-prime argument remains
an ordinary proof; the exact computation certifies its numerical premises.

This uses the actual-label pair-moment framework of
[BBMST](../../../../Library/Arith/balister2018covering.md), Theorem 3.2 and Lemma 3.6,
and its charge criterion in Theorem 3.1. The additional deductions here
are the supported-head estimates and explicit support-restricted tail
bounds. [Schroeder's three-prime theorem](../../../../Library/Arith/schroeder2026noncoverage.md)
restricts the total distinct prime factors of each modulus. It does not
directly cover these head-plus-tail hypotheses: the finite-head rows allow
six total factors in one modulus, while the arbitrary-star row permits
more. BBMST's square-free-head theorem covers the subcase where all primes
through 73 have exponent at most one, not arbitrary head heights. No exact
dominating statement was found in the searched sources; no literature
priority is asserted. The complete-star case now has unrestricted tail
support by (US1)--(US12); arbitrary tail support for the other displayed
heads and arbitrary head geometry remain unresolved.

<a id="the-support-restriction-is-needed-only-below-a-finite-largest-prime"></a>
#### The support restriction is needed only below a finite largest prime

The support bounds above can be removed entirely for every modulus with
sufficiently large **largest prime factor**. In the following table, impose
the tail-support bound only on original moduli whose largest prime factor
is at most `B`. Every original modulus with largest prime factor greater
than `B` may contain arbitrarily many tail prime factors. Under each row,
the original distinct odd family cannot cover the integers.

| Head | Allowed tail primes | Tail-support bound when `P+(d)<=B` | `B` | Certified continuation seed upper bound |
|---|---|---:|---:|---:|
| Complete star through 73 | `q>73` | 2 | 8192 | `<34474` |
| Arbitrary `{3,5,7}` head | `q>=23` | 2 | 32768 | `<160112` |
| Head period divides 315 | `q>=17` | 3 | 8192 | `<28830` |
| Head period divides 945 | `q>=19` | 3 | 8192 | `<34675` |

No graph, tail-exponent-height or total-prime-count restriction is imposed;
the two finite-head rows retain their stated head-period bounds.
Thus any hypothetical covering completion of the full star head must
contain a modulus with at least three tail prime factors **and largest
prime factor at most 8192**. For the 315 and 945 rows, the required
obstruction has at least four tail prime factors and largest prime at
most 8192. The head and allowed-prime conditions remain essential.

**Finite prefix and actual survivor mass.** Use the same increasing-prime
kernels as in (RK1)--(RK2), stopping after all primes at most `B`. Each
coordinate height is taken from the entire original family, including
exponents that occur only in moduli with a later largest prime. At this
stage delete only the classes whose latest tail prime has been processed.
This retains the exact earlier-prime factors needed by every later class.

Let `r` be one less than the support bound in the table and let

\[
 L_B=\frac{G}{4\delta(1-\delta)}
       \sum_{q_0\le v\le B\atop v\text{ prime}}a_v^2 B_r(v),
 \qquad
 P_B=\prod_{q_0\le p\le B\atop p\text{ prime}}
           \left(1+\frac{3p-1}{(1-\delta)(p-1)^2}\right).
 \tag{RK6}
\]

The product accounts for the **full** layout moment, without a support
truncation. The prefix law `nu_B` is normalized; (RK2) gives mass at least
`1-L_B` to points avoiding every processed class, while repeated (T1)
gives `Gamma(nu_B)<=G P_B`. The certificate proves `L_B<1` in each row.
Restricting once to the actual prefix survivors and normalizing is
therefore legitimate and gives a survivor law with

\[
 \Gamma\le F_B:=\frac{G P_B}{1-L_B}.                  \tag{RK7}
\]

Equivalently, one can keep the unconditioned prefix law and start (T6)
with the separate bounds `G P_B` and `1-L_B`. No independence is asserted
after conditioning. T1--T3 apply to arbitrary old laws, and every later
modulus keeps its complete expanded-head divisor. In particular, the
future step does not identify moduli whose tail projections coincide.

**Unrestricted continuation.** Put `k=pi(B)`, counting all primes including
2. Omitted primes have unused coordinates and may be padded with exponent
zero. The supplied seed satisfies the exact sufficient condition

\[
 F_B<k(\log k+\log\log k-3)^2,\qquad k\ge10.           \tag{RK8}
\]

At `B=8192`, `k=1028`, and the certificate's rational lower bound for
the right-hand side is greater than `35445`. At `B=32768`, `k=3512`,
and that lower bound is greater than `185296`. These strictly exceed all
corresponding seed bounds in the table. Starting here,
[BBMST](../../../../Library/Arith/balister2018covering.md), Theorem 6.1 and its
Lemma 6.2, continue the same recurrence (T6) with `delta=1/2` for every
later prime. Their proof uses only positive survivor mass, (RK8), the
recurrence and the published lower bound for the indexed primes. Every
finite continuation therefore has positive survivor mass, with no
restriction on the number of prime factors of a later modulus.
If the family has no later primes, the already positive prefix mass
suffices directly.

The [existing exact verifier](../verify_star_block_obstruction.py)
recomputes the finite coefficient sums, full-moment products, all four
positive survivor margins and the strict stopping comparisons. It reuses
`verify_finite_continuation.py:stopping_threshold` for the rational lower
logarithm bounds, so no new analytic estimate is assumed. All rounding of
prefix costs and moment products is upward. This is an ordinary proof
using a published continuation theorem with exact numerical premises;
it is not an end-to-end Lean proof or a resolution of unrestricted #7.
The unrestricted remainder is now localized to the stated small-prime
support conditions and the head geometry, not to large-prime support.

<a id="why-scalar-deletion-and-unrestricted-message-energy-do-not-suffice"></a>
#### Why scalar deletion and unrestricted message energy do not suffice

If root elimination keeps only `E alpha^2<=w`, with `0<=w<=1`, and the remaining connected
component's saturation probability `E beta<=L`, its best possible scalar
bound on `Pr(alpha+beta>=1)` is `min(1,F(w,L))`, where

\[
 F(w,L)=L+\frac w2+\sqrt{wL+\frac{w^2}{4}},\qquad
 \sqrt{F(w,L)}\ge\sqrt L+\frac{\sqrt w}{2}.           \tag{DG7}
\]

Minimizing `Aw+BL` subject to [(FV3)](18-four-vertex-blocks-and-cycle-breaking-vertices.md#a-bounded-number-of-cycle-breaking-vertices-in-each-component) gives this expression. It is sharp:
if `0<t=F(w,L)<=1`, an event of mass `t` carrying
`alpha=sqrt(w/t), beta=1-alpha`, with both zero outside, attains all three
values; the zero case is immediate. If `F>=1`, constant `alpha=sqrt(w), beta=1-sqrt(w)`
attains saturation within the budgets. This is a relaxed moment extremizer,
not a purported distinct-modulus covering family.

There is also an actual distinct congruence family showing why even exact
scalar root moments cannot give a universal deletion certificate. For any
finite odd-prime set `P`, prescribe `0 mod p` for every `p in P`, and
`1 mod pq` for every pair. Its tail graph is complete. Each class has a
private point in this union: use only the named zero for a prime class,
or only the two named ones for a pair class, and set every other coordinate
to two. All coordinates equal to two avoid the whole family. After any
sequence of uniform root absorptions, each next root still forbids zero,
so its actual squared moment is at least `1/p^2`. A clique requires all
but two vertices to be deleted before becoming a forest. By (DG7), even
with zero terminal loss and all distortion factors replaced by one, the
resulting scalar budget is at least `(sum_deleted 1/p)^2/4`. Euler's
divergence of the sum of prime reciprocals provides a finite `P` above any
fixed cutoff for which this exceeds one in every order. The finite set is
asserted by divergence, not by an unevaluated numerical enumeration.
The obstruction is to this scalar compression; pointwise caps and actual
coordinate correlations, as retained in (DG1)--(DG5), are additional data.

Nor does the forest energy inequality hold on arbitrary abstract constraint
systems. On uniform variables `x_1,...,x_n,y` of cardinality `q`, forbid
`x_i=0` at each `x_i`, and forbid every `y` value exactly when all `x_i`
are nonzero. Every assignment is forbidden, but the sum of uniform-parent
square energies is `n/q^2+(1-1/q)^n`. At `q=n=3` it is `17/27<2/3`, verified
against all 81 assignments. Taking `n=ceil(2q log q)` makes the energy tend
to zero. The final union repeats full-point modulus labels, so this is
**not** an odd distinct covering counterexample. It shows why the original
modulus injectivity and the arithmetic parent caps must stay inside a
general-graph proof; neither boundary refutes the kernel theorem above.

<a id="a-degree-two-core-with-arbitrarily-many-pendant-leaves"></a>
#### A degree-two core with arbitrarily many pendant leaves

For an arbitrary `{3,5,7}` head, tail primes at least 37 also permit the
following larger graph class. Let `K` be a set of tail vertices whose induced
graph has maximum degree two. Require that the remaining vertices are
independent and each has at most one neighbour in `K`. Paths and cycles
of unbounded length with arbitrarily many leaves attached at each vertex
are included. Equivalently, one may take the vertices of original degree
at least two as the core when their induced graph has maximum degree two,
then add one endpoint from each isolated edge. Isolated vertices may remain
outside the core.

For each core vertex remove its actual pure-coordinate local union and
retain head points where every such union fraction is at most `delta=2/3`.
Their discarded mass is at most `(9G/4) sum_(r in K) a_r^2`. At retained
head points take the core coordinates independently and uniformly on their
local complements. Extend each kernel by the uniform law at discarded head
points; this defines a probability with the original old marginal everywhere,
while the argument uses its restriction to retained heads without normalizing.
Each core kernel has cylinder caps at most `3r^(-e)`. Core-core crossing
classes therefore have exactly the edge and triangle bounds used in (BS11).

An outside leaf `q` with neighbour `r` uses only the enlarged head `Qr^H`.
The transfer (T1) for the extended kernel bounds its Gamma by
`G(1+3(3a_r+2a_r^2))`. The original-label moment bound consequently charges
leaf saturation at most this constant times `a_q^2`, even after restriction
to retained head points. A vertex with no neighbour has the smaller constant
`G`. Once core crossing classes and all saturated leaf fibres are avoided,
choose one uncovered point in each leaf coordinate and use CRT.

The two coefficients are

\[
 K_{\rm core}=\frac{403681}{2880},\qquad
 K_{\rm leaf}=G\left(1+3\left(\frac3{36}+\frac2{36^2}\right)\right)
             =\frac{511919}{10368}<K_{\rm core}.
\]

Thus the total bad mass is at most
`K_core sum_(r in K) a_r^2 + K_leaf sum_(q outside K) a_q^2`, and hence
strictly below **0.898149** by the exact prime-square bound below. This proves
noncoverage for the stated graph class. The preceding forest theorem handles
arbitrary trees from prime 19; this degree-two-core result additionally
allows cycle components with attached leaves from prime 37. Such components
are also included in the stronger one-feedback-vertex result from prime 23.

<a id="absorbing-a-finite-set-of-hub-primes"></a>
#### Absorbing a finite set of hub primes

A complementary criterion allows arbitrary interactions among a small set
of hubs. Let `R` be any set of tail primes, and let the remaining tail primes
be partitioned into blocks `B`, with no actual modulus meeting two different
blocks outside `R`. Write

\[
 P_R=\prod_{r\in R}(1+a_r),\qquad
 D_R=\prod_{r\in R}(1+3a_r+2a_r^2).
\]

Suppose the same old head law has Gamma at most `G` and complete cylinder
sum at most `C`. Enlarge the head by the full prime powers at `R`, using
`nu=mu` times uniform hub coordinates. The union of the actual classes
whose tail support lies wholly in `R` has `nu` mass at most `C(P_R-1)`.
This follows by grouping distinct original moduli by their hub divisor and
summing the original head cylinder caps. Iterating the unconditioned transfer
(T1) bounds the enlarged Gamma by `G D_R`.

All remaining classes are local to one residual block. Applying (BS4) and
charging its saturation under `nu` gives the sufficient condition

\[
 C(P_R-1)+G D_R\sum_B W_B^2<1,                         \tag{HB1}
\]

where `W_B` is bounded by (BS5). The hub-forbidden union and all block
saturations together then have mass less than one. A remaining enlarged
head point and one uncovered point in each block give an uncovered integer.
The enlarged law is never conditioned on hub survival; no unproved control
of its normalized Gamma is used.

In particular, when `R` is a vertex cover of the tail graph, the residual
blocks are singletons. If `S` bounds the prime-square sum over all allowed
tail primes, (HB1)'s loss is at most

\[
 F_R=C(P_R-1)+G D_R\left(S-\sum_{r\in R}a_r^2\right).
 \tag{HB2}
\]

Uniform cardinality bounds need a comparison over all possible hub primes.
Pad their weights with zeros to `k` coordinates, let `a0=1/(q0-1)`, and
suppose `k a0^2<=S`. On the cube `[0,a0]^k`, differentiating the expression
in (HB2), with `P_(−i)=prod_(j!=i)(1+a_j)`, gives

\[
 \partial_iF\ge P_{(-i)}
       \left[C-2G a_0(1+a_0)(1+2a_0)^k\right].
\]

When the bracket is positive, the maximum is bounded by substituting the
first `k` allowed primes in increasing order: the `i`th actual hub prime
is at least the `i`th allowed prime. Both cube and derivative conditions
are checked exactly in the certificate. If deleting the hubs leaves a
matching instead, use `sum_B W_B^2<=2(1+a0/2)^2 S` in (HB1); this coarser
expression is increasing in every hub weight without subtracting hub squares.
The resulting sufficient cases are:

| Head and tail cutoff | Deleted hubs | Remaining graph | Loss upper bound |
|---|---:|---|---:|
| Complete star head, `q>73` | at most 8 | independent | `<0.983593` |
| Complete star head, `q>73` | at most 1 | matching | `<0.987571` |
| Arbitrary `{3,5,7}` head, `q>=37` | at most 6 | independent | `<0.988959` |
| Arbitrary `{3,5,7}` head, `q>=37` | at most 2 | matching | `<0.903742` |

The hubs can have arbitrarily many neighbours. Internal edges among hubs
are allowed; for example, the first case permits every residual prime to
be adjacent to all eight hubs. These are structural exclusions with no
bound on exponents or total prime support.

**Sharper prime-square certificate.** The same verifier additionally sieves
to 40000 and independently checks the prime list by trial division. The
4182 primes in `(73,40000]` have
`sum ceil(10^12/(q-1)^2)=2387697612`. Bounding the remaining primes by all
odd integers gives

\[
 \sum_{q>73,\ q\text{ prime}}\frac1{(q-1)^2}
 \le\frac{2387697612}{10^{12}}+\frac1{1600000000}+\frac1{80000}
 =\frac{2400198237}{10^{12}}.                           \tag{GS1}
\]

For cutoffs below 73 add the finitely many omitted prime squares exactly.
The earlier 4000 certificate is retained. All new graph comparisons are
ordinary proofs with exact rational constants; they are not new Lean
formalizations. Project search and arXiv searches combining covering systems
with forest, graph, and odd distinct covering found no exact dominating
star-forest or hub result in the searched scope; no literature priority is
claimed. The unrestricted problem still requires arbitrary head geometry and
arbitrary tail interactions.

<a id="every-full-star-completion-needs-positive-mixed-tail-capacity"></a>
#### Every full star completion needs positive mixed-tail capacity

Use singleton blocks for arbitrary tails, and choose every threshold to be
`3/4`. By (BS4) and (BS6), `E<59/75`. Hence a full cover must satisfy

\[
 \sum_{\omega(t_d)\ge2}4^{\omega(t_d)}
      \mathbb E_{\mu_b}\left[h_d\prod_{q\mid t_d}r_{q,d}\right]
       >\frac{16}{75}.                                 \tag{BS8}
\]

Replacing each remaining cylinder fraction by `q^(-v_q(t_d))` gives the
weaker necessary inequality
`sum_(omega(t_d)>=2)4^(omega(t_d))mu_b(h_d=1)/t_d > 16/75`.
When every tail part has at most two distinct prime factors, this requires
`sum_(omega(t_d)=2)mu_b(h_d=1)/t_d > 1/75`. Grouping by tail part and
using (BS7) then gives the graph-only necessary condition

\[
 \sum_{\{q,r\}\in\mathcal E}\frac1{(q-1)(r-1)}
       >\frac{2}{1095}.                                \tag{BS9}
\]

These are actual-residue constraints, with single-prime tail classes already
accounted for. They impose no unjustified survival requirement on the
exceptional ternary branch. In particular, any full star completion must
have a tail prime with at least two distinct graph neighbours.

<a id="exact-constants-and-the-remaining-unrestricted-obligation"></a>
#### Exact constants and the remaining unrestricted obligation

The [standard-library verifier](../verify_star_block_obstruction.py)
reconstructs the [fixed rational certificate](../certificates/star_block_obstruction_certificate.json),
including `176.921<K_0<176.922`, `C_0<73/10`, and all budget comparisons.
For the prime tail it sieves to 4000: the 529 primes in `(73,4000]` give
`sum ceil(10^9/(q-1)^2)=2363054`. Above 4000, overcount by odd integers
`q=2j+1`, `j>=2000`, and use the decreasing integral bound to obtain

\[
 \sum_{q>73,\ q\text{ prime}}\frac1{(q-1)^2}
 \le\frac{2363054}{10^9}+\frac1{16000000}+\frac1{8000}
 =\frac{4976233}{2000000000}<\frac1{400}.
\]

The small crossing-budget condition does not follow from star geometry
alone. Add the 210 classes `0 mod qr` for the 21 primes `79<=q<r<=181`.
This remains a noncover: use any star head survivor and tail coordinates
all equal to one. Yet exact arithmetic gives `sum 1/(qr)>14/1000>1/75`.
There are no single-prime tail classes in this example, so even the actual
singleton-block crossing budget exceeds the sufficient threshold.

Here the exceeded threshold is the uniform simplified bound `16/75`.
The full criterion itself still certifies this example: its actual `E=0`
and `J=16 sum 1/(qr)<1`. The example only excludes imposing the simplified
small-budget condition on every extension.

For unrestricted #7, one must still handle arbitrary heads and interactions
between tail blocks. A minimal hypothetical cover with `T>1` has nonempty
actual head survivors, but this fact supplies neither a controlled head law
nor small `E+J`. When `T=1`, arbitrary 73-smooth covers must separately be
excluded. The present block and star results have ordinary mathematical
proofs and exact numerical certificates; they are not complete Lean theorems.
