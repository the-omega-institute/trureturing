---
bibkey: mishraraundal2021weaving
authors: Rama Mishra; Hitesh Raundal
year: 2021
title: Hecke algebra trace algorithm and some conjectures on weaving knots
doi: null
url: https://arxiv.org/abs/1908.04152v3
claim: "Conjecture 5.2 asks for the fixed-n, fixed-k large-m twist-number asymptotic for W(n+1,m); for n>=2 and m>=3 the checked mathematical checkpoint proves actual colored surgery, the arbitrary-subset mixed-circle identity, exact graph-to-mixed-state reindexing and uniform signed/two-parity unsigned coefficient estimates. Source Jones identification and the original twist-number asymptotic remain unproved here."
strata_touched:
  - D5/S3/Topology/WeavingDiagramPorts
  - D5/S3/Topology/WeavingMixedComponents
  - D5/S3/Topology/ColoredMatchingSwitch
  - D5/S3/Topology/ColoredMatchingSwitchConsumer
  - D5/S3/Topology/WeavingEulerDefect
  - D5/S3/Topology/WeavingReferenceIncidence
  - D5/S3/Topology/WeavingReferenceDegree
  - D5/S3/Topology/WeavingStateGraphBridge
  - D5/S3/Topology/WeavingCoefficientConsumer
  - D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate
  - D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics
license: citation-only
triage: anchor
---

# Weaving-knot twist-number conjecture

The primary source is arXiv:1908.04152v3. Definition 5.1 (printed p. 21)
defines the higher twist numbers from the Jones coefficients, and Conjecture 5.2
(printed p. 23), together with equation (5.5), asks for every fixed $n,k$
in the source's range for the large- $m$ asymptotic

$$
T_k(W(n+1,m))\sim\frac{(r+d)^k+r^k}{k!}\,m^k,
$$

where

$$
d=n\bmod 2,\qquad r=(n-d)/2,
$$

with links included and no coprimality condition on $m$. The literal $n=1$
boundary is not silently included in the formalization target; the full
geometric/Jones route must preserve the source's width and link conventions.
Definition 5.1 takes one coefficient from each end:
$T_k(L)=|\lambda_{l+k}|+|\lambda_{h-k}|$ for
$V_L(t)=\sum_{j=l}^h\lambda_jt^j$. The stated relevant range is
$1\le k<nm/2$, which holds eventually for each fixed positive $k$; the
link exponents may be half-integral, with integer coefficient offsets.

The conjecture box says only “For a fixed n”; it does not explicitly impose
n>=2. The repository's auxiliary geometry covers n>=2 and m>=3, without
coprimality, and supplies no result for the box's literal n=1 reading.

The graph layer in
`D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate` defines the finite
signed rank-state polynomial using actual connected-component ranks, including
isolated vertices. It derives nonnegative state exponents, at most $2j$
nonisolated vertices in a rank-$j$ state, a uniform fixed-rank cyclic-subset
count under a bounded-forward-degree ordering, and the
$O_k((e+1)^{k-j})$ bound for an individual rank-$j$ coefficient term.
The counting proof uses a finite injection into source images and forward
neighbor slots, followed by an injection of edge subsets into support patterns.

The forest contribution does **not** equal the negative-binomial comparison
series. For the triangle, $v=e=3$ and $b=1$: its forest polynomial is
$1-z+z^2$, so its cubic coefficient is zero, while
$[z^3](1+z)^{-1}=-1$. The companion
`TutteCoefficientAsymptotics` module instead sums integer-binomial comparison
terms over all subsets. Their total is the ideal coefficient, and their forest
part agrees with the actual forest coefficient. The forest error is therefore
minus a comparison sum over cyclic states. Grouping this sum and the actual
cyclic contribution by graph rank proves, uniformly for every connected simple
graph with forward degree at most $D$ and every $k\ge1$,

$$
\left|[z^k]H_G(z)-(-1)^k\binom{b+k-1}{k}\right|
\le C(D,k)(e+1)^{k-1},\qquad b=e+1-v.
$$

The constant depends only on $D,k$. Integer binomial coefficients retain
negative comparison exponents, so the theorem includes small graphs, trees,
and the one-vertex case without truncating the comparison series. The first
coefficient is proved exactly equal to $-b$.

WeavingDiagramPorts derives the finite chronological matching from the
repeated generator sequence and proves the two uniform-smoothing component
classifications, exact circle counts and actual crossing endpoint formulas.
These are repository derivations motivated by the source, not theorems
attributed to it. They do not identify the normalized integral Jones
invariant, establish a forest-coefficient equality or prove Conjecture 5.2.
No priority, originality, uniqueness or original-problem credit follows.
The existing Aharonov–Jones–Landau Library note concerns a separate algebraic
Artin/trace bridge and also leaves geometric Jones identification unpaid.

The eight-module extension proves the following transfer for $n\ge2$,
$m\ge3$, either reference smoothing parity $p\in\{0,1\}$, and every
subset $S$ of the actual $nm$ crossings. These are repository-derived
auxiliary results, not results attributed to Mishra and Raundal.
[WeavingMixedComponents](../../D5/S3/Topology/WeavingMixedComponents.lean),
`distinct_reference_components_force_distinct_mixed_circles`, descends the
actual dart-to-spanning-component map to mixed circles, retaining all uniform
circles as graph vertices. In
[ColoredMatchingSwitch](../../D5/S3/Topology/ColoredMatchingSwitch.lean),
`colored_switch_circle_count` proves that replacing two local matching edges
on four distinct darts changes the circle count by at most one, and merges
two distinct old circles exactly. External and local edges retain their
colors even when they have the same endpoints.
[ColoredMatchingSwitchConsumer](../../D5/S3/Topology/ColoredMatchingSwitchConsumer.lean),
`mixed_insert_circle_count`, applies this surgery at every actual crossing
outside $S$; distinct old spanning components force the exact merge case.

Write $v_p$ for the uniform-circle count, $c_p(S)$ for the actual mixed-circle
count, and $q_p(S)=v_p-\kappa_p(S)$, where $\kappa_p(S)$ counts all
components of the spanning reference graph, including isolated vertices.
[WeavingEulerDefect](../../D5/S3/Topology/WeavingEulerDefect.lean),
`mixed_circle_count_nat`, proves

$$
c_p(S)+2q_p(S)=v_p+|S|.
$$

Its Euler defect is monotone under insertion and is zero at both the empty
and full states, hence at every intermediate subset. Empty, full and
disconnected states and crossings at the cyclic closing seam are included;
the colored matching argument retains parallel edges of different colors.
The companion `mixed_circle_exponent` identifies the nonnegative exponent
$v_p-1+|S|-2q_p(S)=c_p(S)-1$.

[WeavingReferenceIncidence](../../D5/S3/Topology/WeavingReferenceIncidence.lean),
`crossingEdgeEquiv`, bijects actual crossings with the simple reference graph
edges, giving exactly $nm$ edges.
[WeavingReferenceDegree](../../D5/S3/Topology/WeavingReferenceDegree.lean),
`orderedGraph_forward_degree`, orders interval vertices before hubs and proves
forward degree at most four; it asserts no bound of four on full hub degree.
[WeavingStateGraphBridge](../../D5/S3/Topology/WeavingStateGraphBridge.lean),
`graphStatePolynomial_eq_mixed`, reindexes the finite state sum through this
actual crossing-edge bijection to prove the literal polynomial equality

$$
\operatorname{graphStatePolynomial}(G_p)=H_p(z)
=\sum_{S\subseteq\mathrm{Crossings}}(-1)^{|S|}z^{q_p(S)}
  (1+z)^{c_p(S)-1}.
$$

Here $H_p$ is the actual mixed-circle state polynomial, without a Jones
identification assumption. In
[WeavingCoefficientConsumer](../../D5/S3/Topology/WeavingCoefficientConsumer.lean),
`actual_signed_estimate` transfers the uniform graph bound: for every
$k\ge1$ and $p\in\{0,1\}$,

$$
\left|[z^k]H_p-(-1)^k\binom{b_p+k-1}{k}\right|
\le C(4,k)(nm+1)^{k-1},\qquad b_p=nm+1-v_p.
$$

The constant is `uniformCoefficientConstant 4 k`, independent of $n,m,p$.
The same module's `exact_cycle_ranks` gives
$b_1=(r+d)m-d$ and $b_0=rm+d$. Its `two_reference_unsigned_error` proves

$$
\left|\,|[z^k]H_1|+|[z^k]H_0|
-\binom{b_1+k-1}{k}-\binom{b_0+k-1}{k}\right|
\le2C(4,k)(nm+1)^{k-1}.
$$

This uses one coefficient from each parity and the reverse triangle
inequality, without assuming eventual coefficient signs. The quantitative
`binomial_leading_error` also bounds
$|\binom{b+k-1}{k}-b^k/k!|$ by
$\operatorname{risingErrorConstant}(k)(b+1)^{k-1}/k!$ for all natural
$b,k$. These are checked mathematical statements, not formal acceptance of
the original conjecture or of the conditional ordinary proof.

The actual normalized source Jones/closure identity remains unpaid:

$$
V_{W(n+1,m)}(t)=(-1)^{rm+d-dm}
  t^{-rm+d(m-1)/2}H_1(t).
$$

Its formal route still requires integral Hecke coset spanning, restriction
of the trace to $\mathbb Z[q,q^{-1},z]$, honest ring base change,
localization at $z$ and $\eta=1-q+z$, and adjoining a root
$u^2=q/(z\eta)$ mapped to the compatible link root $\lambda$.
Specialization from the generic rational function field does not supply
this bridge. Complement-state reciprocity
$H_1(z)=(-1)^{nm}z^{nm}H_0(z^{-1})$, the constant and leading coefficient
endpoints, and the identification
$T_k=|[z^k]H_1|+|[z^k]H_0|$ also remain formal obligations. Combining these
with the proved coefficient and binomial bounds into the original fixed-$n$,
fixed-$k$, sufficiently-large-$m$ twist asymptotic is still unfinished.
Conjecture 5.2 is not recorded as resolved, and no priority is claimed.

The four-slot escape audit for the 74 public theorem targets is unfinished
(`declared_unresolved`/missing); its existing linked issue is
[25506](https://github.com/the-omega-institute/trureturing/issues/25506).
The recorded obstruction is `IE-C050`, `source.selection_missing`, for
`Reg.D5.S3.Topology.ColoredMatchingSwitch` at `colored_switch_circle_count`.
No `declared_validated` audit completion is claimed.

The inspected source audit also records later width-three coefficient results and
a 2026 JIMS paper whose full body was unavailable in the public access route.
Consequently this note records the source and formalization boundary only; it
makes no priority, uniqueness, or open-problem claim.

The related paper is Rama Mishra and Hitesh Raundal, *Asymptotics of
Normalized Khovanov Ranks of Weaving Knots*, The Journal of Indian
Mathematical Society 93(3) (2026), 376–394,
DOI 10.18311/jims/2026/48582. The retained publisher metadata, abstract and
access response were inspected; the full body was not available through
that public access route. Its solution scope, including whether it proves
the exact all-width, all-k leading constant, remains unverified. The
abstract's order statement settles neither solution nor non-solution of
Conjecture 5.2, and the bounded search does not establish global novelty.

## Verified locator

- Primary source: https://arxiv.org/abs/1908.04152v3
- TeX/PDF locator: Definition 5.1, equation (5.5), and Conjecture 5.2.
- Related Jones--Tutte source used for the eventual classical bridge: Dasbach and
  Lin, *A volumish theorem for the Jones polynomial of alternating knots*,
  Pacific Journal of Mathematics 231 (2007), 279–291.
