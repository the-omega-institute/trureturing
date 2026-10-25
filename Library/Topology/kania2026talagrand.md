---
bibkey: kania2026talagrand
authors: Tomasz Kania and Jerzy Kakol
year: 2026
title: Talagrand compacta, 2DCP, and pointwise quotients
doi: null
url: https://arxiv.org/abs/2607.06808v2
claim: Problem 8.2 asks whether the prediction principle in Theorem A can be weakened from diamond on a stationary co-stationary set to CH; the project suppliers prove common-stage clopen reflection, regular signed-measure lifting, exact eventual point-pair equality and uniform strong-dual norm separation of compact Stonean weak-star embeddings, without the CH induction.
strata_touched:
  - D5/S3/Topology/InverseLimit
  - D5/S3/Topology/Measures
  - D5/S3/Topology/ExtremallyDisconnected
license: citation-only
triage: anchor
---

# Talagrand scheme and local construction suppliers

The inspected source is the complete 20-page arXiv version 2607.06808v2,
updated 10 July 2026. Problem 8.2 appears on PDF page 19:

> Can the prediction principle in Theorem A be weakened from ♢(S) to CH?

Theorem A on PDF page 2 assumes diamond on a stationary co-stationary
subset of omega-one. It constructs a realization of Talagrand's scheme
with no two disjoint non-metrizable closed homeomorphic subspaces. The
construction retains the signed-measure induction conditions (A)-(G).
Theorem B retains the Grothendieck property of C(T), no weak-star copy
of beta-omega in its dual unit ball, and no nontrivial convergent
sequence in T. A proof of only a weaker topological statement would
not answer the original question.

The project module CountableClopenReflection is known inverse-limit
background. For an actual profinite inverse system indexed by all
proper stages below omega-one, with nonempty components and surjective
bonding maps, it reflects any countable family of final clopens into
one proper stage above an arbitrary base. Empty indexing types and
empty clopens are included. The exact inverse-image equalities preserve
nonemptiness and disjointness in both directions.

Mathlib's Profinite.exists_isClopen_of_cofiltered reflects an individual
clopen. The supplier synchronizes these stage choices by a countable
ordinal supremum; adding the base as the none index of Option(I)
also handles the empty family. The existing project theorem
D5.S1.Dynamics.Shadowing.compact_projection_image supplies actual
compatible-thread lifts, making the final projections surjective.

One may place a final separating clopen among the same countable
family when applying the supplier. This locates all actual supports
at a single stage. It supplies neither CH bookkeeping nor the
transfinite splitting construction, signed-measure (A)-(G), or the
retrospective paired-Dirac capture argument. Problem 8.2 remains
unresolved by this module. The result is not claimed as new mathematics.

## Regular signed-measure lift supplier

`D5.S3.Topology.Measures.RegularSignedLift` supplies an ordinary
Hahn–Banach / positive Riesz–Markov–Kakutani / Jordan construction.
For arbitrary compact Hausdorff Borel spaces K and L in independent
universes, a continuous surjection p : K → L and an actual finite
signed measure mu on L with explicitly regular total variation, it
constructs an actual signed measure nu on K with regular total
variation, nu.map p = mu, and nu.totalVariation(univ) =
mu.totalVariation(univ). Empty spaces, zero measures and both signs
remain in scope. Regularity is a premise: it is not inferred for an
arbitrary Borel measure on a nonmetric compact Hausdorff space.

For a finite regular positive measure, pullback is a unital isometry
C(L, ℝ) → C(K, ℝ). Real Hahn–Banach extends the integration functional
from its range with unchanged norm. The norm bound and value on one
imply positivity, so positive RealRMK represents the extension by a
finite regular measure. Integral uniqueness identifies its pushforward
with the input, and evaluating one gives exact mass. Each Jordan part
of mu is a restriction of its regular total variation, hence regular.
Lifting the two parts and pulling back their measurable separator
preserves mutual singularity. Their Jordan difference gives the signed
lift and exact total variation mass.

The analytic inputs are standard results supplied by the pinned Mathlib:
`exists_extension_norm_eq`, `RealRMK.rieszMeasure`,
`RealRMK.integral_rieszMeasure`,
`Measure.ext_of_integral_eq_on_compactlySupported`,
`Measure.Regular.restrict_of_measure_ne_top`, and the signed-measure
Jordan decomposition API. The local proof composes these APIs; it does
not attribute this general construction as a new theorem of Kania and
Kąkol or claim global mathematical novelty.

The supplier can provide the map and mass hypotheses of
`NormPreservingLifts.arbitrary_lifts_tendsto`. That consumer still
requires clopen concentration, a uniform variation bound, eventual
fibre constancy for each locally constant test, and a reference
weak-star limit. Existence of lifts alone proves none of these
additional hypotheses. Neither supplier constructs the CH recursion,
the signed-measure induction (A)–(G), or the retrospective paired-Dirac
capture argument. Problem 8.2 remains unresolved here; no official
acceptance is asserted.

## Nonmetric clopen disjointization

The local selection statement concerns arbitrary compact Hausdorff
zero-dimensional Borel spaces. For regular probabilities mu_n carried by
pairwise disjoint Borel E_n and 0 < eta < 1, its conclusion is an increasing
subsequence and pairwise disjoint nonempty clopens retaining probability
greater than 1-eta/2. The ordinary argument is a classical selection proof,
not a novelty claim or a claim that this theorem originates in the cited
Problem 8.2 article.

The construction uses the pinned Mathlib general Prokhorov forward compactness
instance for ProbabilityMeasure K. A cluster nu is regularized by applying
positive RealRMK to its continuous integral functional; nu is not assumed
regular. The representing lambda is finite on compact K before its integral
of one proves probability mass. Continuous clopen indicators supply precisely
the fixed-clopen convergence needed by the finite-history induction. They do
not supply convergence on moving Borel carriers. Summability of lambda(E_n),
regular compact cores, outer open approximations and a finite clopen sandwich
complete the ordinary construction without a metric or countable base.

For a real finite regular signed input, carrying means zero total variation
on the complement of the carrier. Normalization uses
q=totalVariation(u)(W), never the cancelling signed value u(W). Restriction
and positive rescaling give t=q inverse times u restricted to W, total
variation norm one, and exact error 2(1-q). On a further increasing
subsequence a single sign makes positive Jordan mass at least one half.
That sign acts on both t and the corresponding original u. A fixed positive
error bound does not imply weak-star convergence of the approximants.

The canonical implementation source is
`D5.S3.Topology.Measures.ClopenDisjointization`; its corresponding Scribe
states the full positive and paired-sign signed telescopes. Source presence
is not kernel acceptance. Neither this selection statement nor its signed
normalization establishes KPR, the signed (A)-(G) recursion, final capture,
the Grothendieck endpoint or exclusion in the whole signed dual unit ball.

The local source is kernel-checked under the pinned project toolchain. It
contains the two public suppliers
`D5.S3.Topology.Measures.ClopenDisjointization.exists_clopen_disjointization`
and
`D5.S3.Topology.Measures.ClopenDisjointization.exists_signed_clopen_disjointization`.
The scoped report records statement identities
`sha256:7d793bb2985eff9fa64f7451af62ac5c451f2692ecfce37248db61ac4ec3b867`
and
`sha256:db82e144a84a7e6ceb423a536d401f0006f2a0ac37c94eb7ab7ea23c50b8518f`,
with type identities
`sha256:5d83d13afbefa6152a937e5a6eacfcc6658b937475f2aa4b1e4a7b38defd9b74`
and
`sha256:931f69e143389d4d4e9147855d510b47b2ad4844f3ef31d908cd44bad809b542`.
The accepted target axiom closure is `Classical.choice`, `Quot.sound` and
`propext`; this is a local supplier record, not an attribution of the
construction to Kania and Kąkol and not a novelty or solved-problem claim.
The positive theorem has the arbitrary nonmetric compact Hausdorff
zero-dimensional Borel hypotheses stated above. The signed theorem carries
and normalizes by total variation, has exact error `2 * (1 - q)`, and uses one
common sign on both sequences. No weak-star convergence is inferred.

The information registration remains unfinished for both public suppliers.
Issue https://github.com/the-omega-institute/trureturing/issues/20708 records
the missing whole-family variation, sensitivity, observational dependence,
enrolled readout binding and complete raw `sourceSelection` evidence; the
broader reconstruction context is issue 16293. The issue is an unfinished
audit disclosure, not a `declared_validated` registration, and no retry is
claimed here.

## Eventual point-pair equality supplier

The repository theorem
`D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation.eventually_eq_of_eventually_mem_isClopen_iff`
applies to every Hausdorff extremally disconnected space E and arbitrary
sequences p, q : ℕ → E. Its exact implication is

$$
\left[\forall U\subseteq E,\quad U\text{ clopen}\ \Longrightarrow
\exists N_U\in\mathbb N\ \forall n\ge N_U,\quad
(p(n)\in U\ \Longleftrightarrow\ q(n)\in U)\right]
\ \Longrightarrow
\exists N\in\mathbb N\ \forall n\ge N,\quad p(n)=q(n).
$$

The hypothesis ranges over all ambient clopens, each with its own
cutoff. Compactness and a common cutoff are not premises. No
Grothendieck, Schur, KPR or equivalent no-pairs property is assumed.

The proof starts from an infinite pool of unequal original pairs.
Successive clopen splits retain an infinite tail on one side and
discard one endpoint of a selected pair. This constructs disjoint
clopen shells D(i), strictly increasing original indices k(i), and
oriented endpoints x(i), y(i), with x(i) in D(i) and y(i) able to
enter only a later shell. Pairwise disjointness gives a unique shell
index r(i) for each companion that enters a shell; set r(i)=i when
there is none. The sparse recursion b(0)=0 and
b(n+1)=max(b(n),r(b(n)))+1 makes y(b(n)) avoid D(b(m)) for every n,m.

For an index set A, let Q(A) be the closure of the union of D(i)
over i in A. These sets are clopen, and disjoint index sets have
disjoint Q-sets. An infinite nested-pool construction chooses a half
whose Q-set excludes each successive companion. An infinite diagonal
S ⊆ range b has S ∖ A finite for every fixed pool A. The proof establishes the
finite-error containment
Q(S) ⊆ Q(A) ∪ ⋃ {D(i) : i ∈ S ∖ A}.
Rectangular avoidance removes the error shells, so Q(S) excludes
every companion y(b(n)) and contains x(i) for all i in S. This one
ambient clopen separates infinitely many original pairs, contradicting
its own eventual membership agreement, regardless of orientation.

Pinned Mathlib supplies the Hausdorff extremally disconnected
`TotallySeparatedSpace` instance,
`exists_isClopen_of_totally_separated`,
`ExtremallyDisconnected.open_closure`,
`ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen`,
`closure_minimal`, and the elementary infinite-set and monotone
subsequence tools. The repository module assembles the shell,
sparse avoidance, finite-error and diagonal argument from these
inputs and a supplied unpublished ordinary argument. That ordinary
argument is fallible prior research, not kernel evidence. The
assembled proof is repository-derived; this note does not attribute
it to Kania–Kąkol or claim mathematical novelty.

This supplier provides the eventual-equality conclusion once a
consumer establishes the exact per-clopen premise on the same
Hausdorff extremally disconnected space. It does not establish that
premise for a proposed CH construction or prove the required
continuous-dual norm transfer, compact lower-semicontinuous minimum
argument, or full signed dual-ball endpoint. It supplies neither
the CH recursion and signed-measure conditions (A)–(G), nor the
retrospective paired-Dirac capture and Theorem A closed-copy
prohibition. Problem 8.2 and the complete analytic endpoints remain
unresolved by this local supplier; no official acceptance is asserted.

## Uniform strong-dual norm separation

`D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation.exists_pos_le_norm_sub`
states that for every real normed space X, compact Hausdorff extremally
disconnected space K, and weak-star continuous injective h : K → WeakDual ℝ X,
there exists a real c > 0 such that

$$
  p\ne q\quad\Longrightarrow\quad
  c\le \|\operatorname{WeakDual.toStrongDual}(h(p)-h(q))\|
  \qquad(p,q\in K).
$$

There is no nonempty, nontrivial, completeness, positivity-of-functionals
or global norm-bound premise. The argument uses the weak-star topology
on `WeakDual` and the operator norm on `StrongDual` separately; it
establishes lower semicontinuity and does not use continuity of
`WeakDual.toStrongDual`.

The consumed private general lemma applies to every lower semicontinuous
F : K × K → ℝ positive away from the diagonal. If no uniform lower bound
exists, choose unequal pairs with F(p(n),q(n)) < 1/(n+1). For any clopen U,
the symmetric cross (U × Uᶜ) ∪ (Uᶜ × U) is compact and disjoint from the
diagonal. If nonempty, lower semicontinuity gives an attained strictly
positive minimum. The chosen pair eventually lies outside this cross;
an empty cross is always missed. Thus every clopen membership test
agrees eventually. The point-pair theorem gives eventual equality,
contradicting the chosen unequal pairs. Symmetry and triangle
inequalities are not used.

In the dual application subtraction is weak-star continuous. Pinned
Mathlib's `WeakDual.isClosed_closedBall` makes the norm sublevel sets
of the difference closed, hence the norm function is lower
semicontinuous. Injectivity and the linear equivalence to the strong
dual give positivity off the diagonal. `LowerSemicontinuousOn.exists_isMinOn`
and `tendsto_one_div_add_atTop_nhds_zero_nat` provide the minimum and
reciprocal-limit steps. These are ordinary library inputs; the compact
cross composition is derived here from the supplied ordinary proof
plan and the point-pair theorem, with no literature novelty claim.

The consequence applies in particular to βℕ using the extremal
disconnectedness obtained from `StoneCech.projective` and
`CompactT2.Projective.extremallyDisconnected`. It supplies the local
norm-gap implication. It does not construct the full signed dual ball,
the CH recursion or conditions (A)–(G), the retrospective paired-Dirac
capture, or the Theorem A closed-copy prohibition. Problem 8.2 and
the complete CH/Talagrand endpoint remain unresolved here, and no
official acceptance is asserted.

## Literal successor-coordinate constructor

`D5.S3.Topology.InverseLimit.SignedSuccessorCoordinates.exists_successor_coordinates`
takes every `a : Ordinal.{0}`, `H : SignedProperLimit.Prefix (succ a)` and
closed cover `Y ∪ Z = univ` of `K := H.Space ⟨a, lt_succ a⟩`, including
`a = 0`, overlapping sides and either empty side. Its
`Nonempty (Result H Y Z)` supplies a closed nonempty literal carrier
`C ⊆ SignedProperLimit.Cube (succ a)` and a homeomorphism
`e : SignedSplitSuccessor.splitCarrier Y Z ≃ₜ C`. The carrier is exactly
the insertion range: `e(k,b)` reads `k(i)` at every `i < a` and `b` at
coordinate `a`; its inverse reads the literal restriction to `a` and
coordinate `a`. The output `Prefix (succ (succ a))` retains every old
carrier exactly and has top carrier `C`. Its compatibility and onto
fields cover every pair of stages. For every `c ≤ a`, the proved
restriction equation identifies restriction from `C` to `c` with
restriction of the inverse's old component. Old pairs reuse `H`; onto
from the new stage to any old stage uses `H.onto` to lift to `K`, then
the actual cover projection to choose a sheet and insert it.

The construction reuses the original `SignedProperLimit` coordinate
core and `SignedSplitSuccessor.splitCarrier`. Pinned Mathlib's
`Homeomorph.funSplitAt` and `Homeomorph.piCongrLeft` supply splitting and
reindexing; compactness of the closed split and the Hausdorff cube give
the closed range and range homeomorphism via
`Continuous.isClosedEmbedding` and `Topology.IsEmbedding.toHomeomorph`.
This repository-derived local topology supplier is not attributed to
Kania–Kąkol as a new theorem. It leaves full-history assembly, the signed
measure system and (A)–(G), CH bookkeeping and the final CH/Talagrand
endpoints open. Its information registration remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/21448; no
`declared_validated` registration or solved-problem claim is made.

## Verified locator

Canonical arXiv record: https://arxiv.org/abs/2607.06808v2.
Verified full PDF: https://arxiv.org/pdf/2607.06808v2.
PDF SHA256: b99499c33606ed02448c329e848c4fcbc38f5f0521326b1b017ec36895f7b1b4.
Extracted-text SHA256: 501eafa8e27fdcdca8769c8068ac5013d2afeac838a1598df60e1907634cef23.
The entire source was read; PDF pages 10, 11 and 14 were additionally
checked visually for the induction clauses and split formulas. The
original 1980 Talagrand article was not available as full body text,
so this note does not claim a line-by-line audit of that article.
Same-day bounded arXiv metadata searches found no CH answer within
their stated Talagrand/Grothendieck scopes; this is not a global
uniqueness or novelty certificate. No official solved receipt is
asserted by this background formalization.

## Classical subsequence splitting and weak extraction

`D5.S3.Topology.Measures.L1RawSplitting.exists_raw_restriction_splitting`
is the complete real L1 supplier. Its literal restriction operation is
`L1Restriction.restrict`; `L1TailSelection`, `L1TailConcentration`,
`L1Biting` and `L1Disjointization` construct the disjoint carriers.
`L1WeakExtraction` and `L1UniformIntegrableWeak` supply genuine weak
subsequence extraction, with every helper consumed by the full splitting.

The real L1 subsequence splitting used in the signed-measure construction is
classical Kadec–Pełczyński–Rosenthal mathematics. The required form uses literal
restrictions to measurable, pairwise disjoint sets, a complementary remainder
converging against every continuous real linear functional, and convergence
of the disjoint-part norms. Uniform integrability alone is an intermediate
property, not that weak convergence conclusion.

A concrete disjointization construction appears in Dacunha-Castelle and
Schreiber, Annales de l'Institut Henri Poincaré B 10 (1974), pp. 229–277,
Definition 3.3.2 and Lemmas 3.3.3–3.3.4, pp. 263–266:
https://www.numdam.org/item/AIHPB_1974__10_2_229_0/ . The inspected argument
uses a nonatomic Lebesgue setting and additional Orlicz hypotheses. Those
hypotheses cannot be silently transferred to arbitrary finite measure spaces.
The classical subsequence splitting is also discussed in Peralta–Pfitzner,
Studia Mathematica 227 (2015), pp. 77–95, DOI 10.4064/sm227-1-5,
whose introduction cites Bourgain–Rosenthal, Israel Journal of Mathematics
37 (1980), pp. 54–75, p. 68, DOI 10.1007/BF02762868. The latter page and
Albiac–Kalton, Topics in Banach Space Theory, second edition, Lemma 5.2.7,
are source leads; their proofs have not been acquired by the recorded access.

The Hilbert approximation argument separates the weak-extraction obligation
from the disjoint-carrier selection. All countably many hard truncations
lie in a single closed separable Hilbert span, even when the original L2 is
nonseparable. Compactness of the product of its weak dual balls supplies one
common selector. A genuine bounded linear map from this span into L1 carries
each weak limit to L1. Uniform norm errors then make these limits norm Cauchy
by a Hahn–Banach norming functional of norm at most one; completeness and a
three-term estimate give convergence against every L1 functional. This
argument includes the zero space and requires no positive measure premise.
It neither assumes nor proves the CH induction or the full signed endpoint.

For the raw-restriction construction, choose the actual strongly measurable
representative of each L1 class and use its integer hard-tail masses Q(n,k).
A common scalar Hilbert subsequence makes these bounded masses converge for
every k at once. Their limits c(k) decrease, and alpha is their infimum.
At each recursive step a large cutoff makes c(k) close to alpha and makes
its superlevel support have small integral for every input in the finite
original prefix already passed. Markov's inequality controls that support's
measure; uniform integrability of a finite family controls the old-input
integrals. Selecting the next source index after these conditions are fixed
makes its moving tail mass close to alpha. The effect of the ith support on
every earlier selected input is at most 2 to the power minus i.

Write A(i) for these actual measurable superlevel sets and let E(i) be A(i)
minus the union of all later A(h). The E(i) are pairwise disjoint as sets.
The countable-union integral inequality bounds the removed part by the
geometric tail, at most 2 to the power minus i. Thus the norms of the literal
restrictions to E(i) have the same limit alpha as the restrictions to A(i).
For every positive fixed integer k below the moving cutoff, the k-tail mass
of the literal complement of A(i) is exactly Q(i,k) minus the moving tail
mass. Its limit is c(k) minus alpha. These limits vanish as k increases;
a separate finite-prefix estimate gives uniform integrability of the entire
complement sequence.

The difference between the literal complements of E(i) and A(i) is exactly
the restriction to A(i) intersected with the union of its later supports.
Its L1 norm tends to zero by the same geometric bound. Apply the genuine
weak-extraction argument to the complements of A(i), and transfer each
continuous real functional across this norm-null difference. Passing to
that final common subsequence preserves actual set disjointness, the
indicator identities and the disjoint-norm limit. In particular, no input
measure is corrected, no constant-norm assumption is inserted, and both
summands are the literal restrictions of the same selected original L1
class. Their sum and the sum of their norms equal the original class and
its norm respectively. This is the classical analytic supplier only;
the signed-measure transfer and full CH/Talagrand endpoint are separate.


## Signed raw transfer and the sufficient diagonal criterion

Let $K$ be any compact Hausdorff space with its Borel measurable structure,
and put $D=C(K,\mathbb R)^*$. Regularity below means regularity of the actual
total-variation measure, not an automatic property of arbitrary Borel measures.
The project theorem
`SignedGrothendieckCriterion.exists_signed_raw_restriction_splitting`
transports the real L1 supplier to arbitrary regular signed inputs $s_n$
with $\sup_n |s_n|(K)<\infty$.

Set $\rho=\sum_n |s_n|$ and $\mu=\rho.\mathrm{toFinite}$. The sum is SFinite;
no finiteness or regularity of the sum is used. Its finite equivalent $\mu$ includes the
all-zero case. Each $s_n$ has a real integrable RN density $q_n$ with respect
to $\mu$, and its actual L1 class satisfies $\|q_n\|_1=|s_n|(K)$.
`SignedMeasure.absolutelyContinuous_ennreal_iff` supplies the vector absolute
continuity needed for signed reconstruction. Indicator density integration
identifies the L1 literal restrictions with the literal signed restrictions.

The L1 splitting therefore gives a strictly increasing $j$, measurable sets
$E_n$ pairwise disjoint as actual sets, a number $r\geq0$, and a regular
signed measure $s_\infty$. With

$$a_n=s_{j(n)}|_{E_n},\qquad b_n=s_{j(n)}|_{K\setminus E_n},$$

both TVs are regular, and

$$s_{j(n)}=a_n+b_n,\qquad |a_n|(K)+|b_n|(K)=|s_{j(n)}|(K),
\qquad |a_n|(K)\longrightarrow r.$$

For every $\Phi\in D^*$ one has
$\Phi(Tb_n)\to\Phi(Ts_\infty)$, where $Ts$ is the signed integration
functional. The actual bounded linear map
$J:L^1(\mu)\to D$, $Jf(g)=\int fg\,d\mu$, comes from the L1–L-infinity
pairing and the continuous-function inclusion. Its norm is at most one;
injectivity, isometry and surjectivity are not used. Every $\Phi\circ J$
is an L1 weak test. Signed RMK supplies a regular representative of $Jv$
for the L1 weak limit $v$. The particular density measure $\mu v$ is not
asserted regular. Regularity of the literal pieces instead follows from
the original regular TV and `variation_restrict`.

The public theorem
`SignedGrothendieckCriterion.weak_of_disjoint_diagonal_variation`
uses the following explicit sufficient hypothesis on $K$:

$$\begin{gathered}
\text{For every TV-bounded regular signed weak-star-null sequence }s_n,\\
\text{and every pairwise disjoint measurable sequence }E_n,
\quad \operatorname{TV}(s_n|_{E_n})(K)\longrightarrow0.
\end{gathered}$$

Here $\operatorname{TV}(s_n|_{E_n})$ denotes the TV of the literal signed restriction
$s_n|_{E_n}$. The hypothesis is over all such signed sequences and sets.
It is not a weak convergence or splitting premise. Under this hypothesis,
for arbitrary $F_n,F_\infty\in D$,

$$[\forall g\in C(K,\mathbb R),\ F_n(g)\to F_\infty(g)]
\quad\Longrightarrow\quad
[\forall\Phi\in D^*,\ \Phi(F_n)\to\Phi(F_\infty)].$$

No norm bound is assumed in this final statement. Banach–Steinhaus on the
complete space $C(K,\mathbb R)$ bounds $F_n-F_\infty$. Signed RMK chooses
regular representatives with TV masses exactly those norms. For any
selector $ns$ tending to infinity, the raw split applies to $s\circ ns$.
The diagonal hypothesis makes its captured part norm-null. The complement
is Banach-weak convergent; its continuous-function evaluations tend to
zero by exact decomposition. The actual double-dual inclusion evaluates
its weak limit at each continuous function, identifying that functional
as zero. Additivity gives convergence along a further selector; the genuine
`Filter.tendsto_of_subseq_tendsto` then gives the original sequence limit.
Its API requires only that $ns$ tend to infinity, and that generality is
retained. Adding the arbitrary limit completes the implication.

These are repository compositions of the classical splitting supplier,
signed RMK and uniform boundedness, with the parameter correspondence above;
no new literature theorem is attributed to Kania–Kąkol. The sufficient
hypothesis remains unproved for the proposed CH construction. Neither
result supplies CH bookkeeping, the signed induction, capture/global
obligations, the closed-copy prohibition or a solution of Problem 8.2.
