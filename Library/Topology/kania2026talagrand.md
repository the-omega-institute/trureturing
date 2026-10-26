---
bibkey: kania2026talagrand
authors: Tomasz Kania and Jerzy Kakol
year: 2026
title: Talagrand compacta, 2DCP, and pointwise quotients
doi: null
url: https://arxiv.org/abs/2607.06808v2
claim: Problem 8.2 asks whether Theorem A can be obtained from CH in place of diamond(S); actual_CH_Talagrand_scheme_and_endpoints now has a successful targeted Lean 4.35 build proving the full literal scheme, A-G, finite disjoint images and closed copies, no 2DCP, full signed dual-ball exclusion, Grothendieck convergence and point-space consequences on exactly one actual finalPrefix; scoped axiom inspection and three independent reviews have passed; PR 22319 tracks delivery CI, and no official acceptance is claimed.
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

## Delayed whole-fibre signed splitting

The construction-specific sources `SignedDelayedSplit` and
`SignedDelayedSuccessor` in `D5.S3.Topology.Measures` implement the local
delayed common-row step in the proposed CH construction. Their role is
in the signed induction associated with the paper's conditions (A)–(G).
The local refinement combines compact metric selection, norm-preserving
signed lifting, ordered columns and signed reference convergence. No
literature novelty claim is made for this assembled proof.

`exists_delayed_fibre_pools` starts with the actual continuous onto
predecessor projection, original supports V(n), target points y(n) in
V(n) and Q, and both infinite original intersections J with N(e).
It chooses infinite subsets of those exact intersections and cluster
points z(e). Eventual coordinate E on the whole original supports
transfers convergence of selected points to every point of the fibre:
every clopen neighborhood of z(e) eventually contains the entire fibre
over y(n). No old fibre is assumed to be a singleton.

`exists_delayed_pool_plan` resolves the equal and distinct cluster cases
internally. Equal points retain the two original parity pools as target
column pools. Distinct points give an old clopen separator. Finite
thinning separates the entire target fibres; an independent infinite
target reserve is split from one source pool, while each source set
stays in its original N(e). Both target column parities use this reserve.
Target auxiliary parity and source reservoir parity therefore have
separate meanings in this branch.

`exists_parity_ordered_split` is the consumed finite-construction core.
The finite earlier exclusion R is fixed first. Whole target-fibre
convergence and auxiliary-support avoidance of the selected point let
the next target be chosen in its prescribed column pool. The clopen
is literally H = p inverse-image (V(n) intersect Q) minus R. Its finite
Boolean tests are fixed next, and only then are auxiliary indices
chosen. All norm-preserving signed lifts satisfy the finite signed
marginal bound; the other rows are never replaced by positive measures.
The prescribed Dirac target gives mass one on H. Thus the finite strict
thirteen-forty-eighths and one-sixth bounds hold. Closure of the even
H's gives one split with onto old projection, whole-support fibre E,
and the scheduled signed G estimates.

`exists_internal_delayed_split` consumes both cluster branches and the
core, selecting its own target reference and pools. It returns infinite
M(e) inside the original source J and N(e), and one clopen of the same
split separating the entire fibres over y(n) on M(0) and M(1). In the
distinct case these source indices avoid every chosen target support,
so the new coordinate is false on their whole original supports.
Every target slice lies above Q. If the original source signed measures
are carried by a disjoint clopen P, the true sheet is absent above P.
Projection therefore transfers old source F without singleton fibres.
A genuine successor lift supplies one regular source reference; whole
support E gives that same reference to every selection. Its quantifier
order is one reference followed by all lift selections.

`SignedDelayedSuccessor.exists_delayed_successor` starts from actual
born signed data and the original old laws. Old I, J and N exist only
on genuinely old rows. Every row has signed sequences for the old labels
and the residual label, with norm one, support-nullity, regular Jordan
parts and positive Jordan mass at least one half. The target row is old;
its target sequence is prescribed Dirac data. The new row uses its own
internally chosen signed birth clusters. It has no invented old J or N.

For auxiliary columns c(q), its final sets have the exact formulas:

- I(r) contains the indices c(q).m(r) with code(r) < q; on the actual
  target row it additionally contains M(0) union M(1).
- J at the actual source pair is exactly M(0) union M(1); every other
  old-label J is its fixed-label auxiliary range.
- Every genuinely born old N is preserved. New-row old-label N(e) is
  the corresponding fixed-label auxiliary parity range.

These sets satisfy A–C, exact one-step I/J refinement sufficient for the
inherited almost-inclusion D, whole-support E, and common every-choice
signed F. Residual selection occurs only after the final I is fixed:
compact metric weak-star compactness selects its residual J on that I,
then splits J into two infinite reservoirs. Whole-support E transfers
its regular reference to every signed lift selection. This includes
old/old, new-row/old-label, old-row/residual and doubly new cases. The
scheduled G witnesses are merely two infinite index sets, without an
extra membership requirement in the updated I. The same output also
retains each even column's strict 13/48 and 1/6 bounds and each odd
column's zero true-sheet mass. Actual norm-preserving lift classes are
inhabited for every old and residual label.

The result is a local compact metric split supplier. Literal ordinal
successor insertion and readback, once-born raw I/J/N, stage-local delayed
eligibility, compatible well-founded raw-history recursion, and the final
omega-one cube construction remain further obligations. The local
supplier proves neither anti-homeomorphism, the Grothendieck endpoint nor
the entire signed dual-ball endpoint. Problem 8.2, full CH Lean completion
and official acceptance remain open.

The owning Reg mirrors preserve the unabridged source telescopes and
actual proof applications. Four-slot information registration remains
unfinished under https://github.com/the-omega-institute/trureturing/issues/21750:
full realization and source reconstruction, lawful enrolled readout,
whole-family variation and sensitivity, and observational dependence
are still missing. These source bindings are not `declared_validated`
registrations.

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


## Quantitative signed clopen oscillation criterion

On an arbitrary-universe compact Hausdorff zero-dimensional Borel space K,
`SignedGrothendieckCriterion.weak_of_signed_clopen_oscillation` assumes the
following explicit property O. Every regular signed norm-one sequence carried
in total variation by pairwise disjoint nonempty clopens, with positive Jordan
mass at least one half, has a single clopen Z at which the evaluations are at
least one sixth infinitely often and zero infinitely often. Under O, arbitrary
weak-star-convergent sequences in the full real continuous dual of C(K,Real)
converge under every continuous double-dual test. Uniform boundedness is
derived, and no positivity or nonemptiness premise is added.

The analytic argument combines the unconditional raw signed restriction split
with signed clopen disjointization at parameter 1/96. The latter gives one
constant sign and fixed TV error below 1/48. On the oscillating clopen, the
selected original evaluations exceed 7/48 infinitely often and have absolute
value below 1/48 infinitely often, excluding a real limit. A positive raw
captured-mass limit would yield a norm-one disjointly carried weak-star
convergent normalized tail by reciprocal continuity, so the mass limit must
be zero. The small captured part, the weak complementary part and the
all-subsequence criterion give the full dual implication.

This is a synthesis of classical analytic mechanisms, not a claim of global
mathematical novelty or attribution of this exact quantitative formulation
to Kania and Kakol. The cited article supplies the Talagrand-scheme context;
O remains a separate conditional hypothesis. No formal CH instance of O,
full signed-ball endpoint, anti-homeomorphism result or official solution of
Problem 8.2 is established by this criterion.

`SignedGrothendieckCriterion.eventually_eq_of_signed_clopen_oscillation`
also proves, under exactly O, that every convergent point sequence is
eventually equal to its limit. It requires no metric, first-countability or
injectivity assumption. The repository-derived proof uses actual signed
Dirac measures and the finite/infinite range distinction; it supplies no
CH instance of O or completed global CH construction.

## The full signed-ball analytic reduction

Write $D=C(K,\mathbb R)^*$ and $Ts(g)=\int g\,ds$. For compact Hausdorff
Borel $K$, `SignedBallReduction.exists_normalized_disjoint_embedding` takes
an arbitrary weak-star continuous injection $h:\beta\mathbb N\to D$ with
$\|h(p)\|\leq1$ for every $p$. Its output is a sequence of regular signed
measures $b_n$, pairwise disjoint Borel sets $E_n$, and a continuous
injection $f:\beta\mathbb N\to D$ satisfying

$$|b_n|(K)=1,\qquad |b_n|(K\setminus E_n)=0,\qquad
f(n)=Tb_n,\qquad \|f(p)\|\leq1\quad(p\in\beta\mathbb N).$$

The quantification covers the entire real signed dual unit ball. Neither
positivity, constant raw KPR norms nor a preselected collision-free
subsequence is an input. No zero-dimensionality is needed at this stage.

Signed RMK represents the principal values. The raw signed restriction
splitting gives, after an increasing selection,
$x_n=Tu_n+Tv_n$, with literal disjoint Borel carriers for $u_n$,
$Tv_n\to V$ against every member of $D^*$, and
$r_n=\|Tu_n\|\to r\geq0$. The selected original full extension $\widehat x$
is still injective: an injection of the discrete index set induces an
injection of its ultrafilter spaces. Banach–Alaoglu extends the bounded
$Tu_n$ sequence. At every free ultrafilter $p$, continuous-function
evaluation and uniqueness of limits give

$$\widehat u(p)=\widehat x(p)-V.$$

If $r=0$, then $Tu_n\to0$ in norm, so $\widehat x(p)=V$ at every free
$p$. There are two distinct free ultrafilters, contradicting injection.
Thus $r>0$, and a tail has $r_n>0$. Normalize on that tail by the actual
norms: $b_n=u_n/r_n$. Scalar variation and restriction identities preserve
regularity and the literal carrying sets and give $|b_n|(K)=1$. The
varying normalization is justified by the norm estimate

$$\left\|\frac{Tu_n}{r_n}-\frac{Tu_n}{r}\right\|
 \leq \left|r_n^{-1}-r^{-1}\right|\sup_m\|Tu_m\|\longrightarrow0.$$

Consequently $\widehat b(p)=(\widehat x(p)-V)/r$ at every free $p$.
This proves free/free injection. Disjoint carriers and variation mass one
give principal/principal injection: equal measures carried by two disjoint
sets would have zero total variation.

For completeness, separate injection on these two pieces does not yet
give full injection. Each principal value can coincide with at most one
free value. `CountableAvoidance.exists_infinite_notMem` avoids this
countable collection by an actual infinite subset $A\subseteq\mathbb N$.
Starting with an infinite pool, split each pool into two disjoint infinite
sets and choose a half absent from the next forbidden ultrafilter. An
infinite diagonal set is contained in every fixed later pool modulo a
finite set; freeness makes these finite errors irrelevant. On the clopen
of ultrafilters containing $A$, both orientations of principal/free
collision are excluded. An increasing enumeration of $A$ therefore yields
injection on the entire compactification, not only on its remainder.

`WeakStarPerturbation.norm_sub_le_of_denseRange` supplies the needed
global perturbation step for arbitrary real normed spaces. If weak-star
continuous $f,g:T\to X^*$ satisfy $\|f(i(a))-g(i(a))\|\leq\epsilon$ on
a dense range, then the same estimate holds for every $p\in T$.
The proof uses the inverse image of the weak-star closed norm ball under
$f-g$; it does not assert continuity of the norm. If every unequal pair
of $f$-values has distance at least $c$ and $2\epsilon<c$, equality of two
$g$-values contradicts the triangle inequality. This is the full-domain
`injective_of_approximation` theorem.

For zero-dimensional $K$, `SignedBallReduction.SignedClopenCollision`
states the remaining analytic sufficient hypothesis. For **every** regular
signed sequence $z_n$ of variation mass one, carried by pairwise disjoint
nonempty clopens $W_n$, with $z_n^+(K)\geq1/2$, **every** continuous
extension of its principal integration functionals has a collision at two
distinct free ultrafilters. This is a sequence-level collision statement;
it contains no KPR supplier or nonembedding conclusion.

`not_injective_signed_ball_of_collision` derives nonembedding of the whole
signed ball from exactly this hypothesis. Apply the full normalization
above, then directly reuse
`WeakStarNormSeparation.exists_pos_le_norm_sub` to obtain a global gap
$c>0$. Put $\eta=\min(c/16,1/4)$. The existing signed clopen
disjointization supplies normalized regular signed restrictions $t_n$,
disjoint nonempty clopens, and variation error less than $2\eta$. Its
further increasing selection supplies one common sign $s\in\{1,-1\}$
such that $(st_n)^+(K)\geq1/2$. Multiply the whole selected original
sequence by this same sign; the global gap remains $c$. Banach–Alaoglu
extends $st_n$. The principal error bound transfers to every ultrafilter,
and $2(2\eta)<c$ preserves full injection, contradicting the collision
hypothesis.

These are repository deductions from classical signed RMK, KPR splitting,
Banach–Alaoglu and the existing clopen and norm-separation suppliers, not
new results attributed to Kania–Kąkol. Establishing SignedClopenCollision
for the intended CH compactum, the transfinite construction, signed
induction and global capture remains outside this analytic reduction.
The reduction alone is not a solution of Problem 8.2.

## Ordinary ordinal successor and arrival readback

`D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor.exists_successor`
constructs an ordinary successor from a valid partial predecessor through a
proper ordinal `a >= omega`. The input is one literal cube Prefix, its onto
base restriction, all previously launched support and legal signed
enumerations, permanent birth entries, and the strict old I/J laws. It does
not assume a complete history or an extension theorem. CH supplies the
current exhaustive clopen/support enumerations; the launch support is
pulled back along the actual restriction and its entire signed enumeration
is constructed before whole-sequence treatment. Support launch indices and
signed measure labels have separate types and fields.

The actual local supplier is
`SignedSplitSuccessor.exists_measured_dynamic_split`. The row index is the
ordinal interval `[omega,a]`, the new row is `a`, old signed labels are
strictly below `a`, and the residual label is `a`. The new row restriction
is the identity on the actual current carrier. The supplier's same executed
split supplies all four reservoir cases. Literal insertion reuses
`SignedSuccessorCoordinates.exists_successor_coordinates`, preserving the
whole earlier Prefix. The enlarged birth pack reads each reservoir at its
unique arrival stage `succ(max(row,label))` and retains every earlier entry.
The arrival pack is additional through-stage data; a strict prefix is not
silently completed with an unborn row.

`Result.quantitative_g` transfers the same split's quantitative certificate
to the literal new-coordinate clopen. One fixed StrictMono target index
works for every norm-one signed lift of the original treated sequence:
even positions have value strictly greater than one sixth and odd
positions have value zero. Historical G is separate from A–F. The regular
common every-choice F certificate is transported to the literal cube by
`Result.literal_f`: for every row and label, one fixed regular reference
measure of variation at most one works for every norm-one lift of the
original whole signed sequence. The same coordinate equivalence pushes the
reference forward and pulls every arbitrary lift back. `Result.literal_e`
covers every old coordinate and the new sheet, with the original I/J sets.

This is a repository-derived composition and birth-readback construction,
not a literature novelty claim or a full CH realization. Delayed execution
with an exposed strictly increasing target index, fixed cofinal launch and
treatment reservations, well-founded existence and validity induction,
proper-limit integration, the final omega-one Prefix and the full problem's
functional-analytic endpoints remain separate obligations. The final
omega-one Prefix is used only for its carrier, cone and projections;
`Prefix.Data` and `Prefix.Laws` remain on proper slices.

## Actual initial ordinal prefix

`SignedOrdinalInitial.H0` constructs the entire Boolean cube at every
finite stage and at omega. Its literal restrictions are onto by extending
each Boolean function with false outside the smaller coordinate domain.
`SignedOrdinalInitial.predecessor` constructs the first predecessor at
omega without CH or an assumed predecessor. Old rows and earlier arrival
births have empty exact ordinal domains, so their obligations are eliminated
by proved contradictions. This supplies the actual initial input to the
transfinite construction; it does not establish the global CH recursion.

## Executed result to the next predecessor

`SignedOrdinalPredecessor.nextP` consumes the same executed successor
`Result` and constructs a predecessor on its literal extended Prefix.
It preserves the original Label-indexed U/V/nu families and onto proofs,
reads permanent reservoirs from the same arrival archive, and proves the
next A/B/C/E/F from the actual I/J and literal E/F certificates. No next
predecessor or complete-history assumption supplies the construction.
The global recursion must still retain the original whole Q/R packages:
nextP stores only current I/J and its weaker predecessor F interface,
not all historical DI/DJ, the bounded regular F reference, or Q.B.

A bounded arXiv check on 26 October 2026 found the primary paper still at
v2. The newest title/abstract query for "Talagrand compacta" or "2DCP"
returned this paper and the earlier mathematical paper 2606.27568v1,
alongside three unrelated materials-science matches. No later CH answer
was identified within that search; this is not a proof of global novelty.


## Literal proper-limit predecessor

`SignedOrdinalLimit.construct` takes an actual strict `Prefix l`, with
`omega < l < omega-one` and `IsSuccLimit l`, an archive of the original
whole born U/V/nu families and their onto proofs, the permanent birth
archive, historical I/J, the genuine earlier omega-stage base invariant,
and exactly `H.Laws A.data`. It constructs the literal `Prefix (succ l)`
and its actual `SignedOrdinalSuccessor.Predecessor`. Every old carrier is
unchanged, the new top is `H.limitCarrier`, and all maps are literal
coordinate restrictions with proved onto fields.

The entire dependent U/V/nu pack is cast once along the old-carrier
equality, preserving every original Label and its onto proof. Permanent
N reads the same arrival entry at `succ(max(row,label))`; the limit
introduces no new birth. `Result.extension` retains the very same proper-
limit Extension chosen by the construction. Its DI/DJ and regular
norm-at-most-one F remain available, with exact predecessor I/J readbacks.
The weaker predecessor F accepts arbitrary original signed-measure
sequences: proper compact metrizability supplies regularity internally.

This is the local proper-limit step for the ordinal recursion, not the
global well-founded history or a solution of Problem 8.2. Its authored
public additions are data structures and construction definitions; the
transport proofs are private and consumed. The inherited information
audit remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/21750.

## Proper-stage continuous clopen obstruction

`ContinuousFiniteImageTail.proper_F_clopen_dichotomy` uses the original
`SignedProperLimit.Prefix.Data` and `Laws`. At a proper stage c, every whole
Dirac lift of the original birth sequence has only finitely many visits or
only finitely many misses of each clopen along its original J(r,d,c). The
reference is chosen after the entire selected lift, exactly as in F. No split
event, final-stage convergence or final common J is assumed.

Its consumer `no_continuous_pool_separation` extends a continuous clopen set
preimage from a closed domain to an ambient clopen. For pools in the original
disjoint reservoirs whose union is the stored earlier J, DJ leaves only a
finite error at c. Removing that error from each original C-pool leaves two
infinite opposite indicator pools, contradicting the dichotomy. This is a
repository-derived local step in the finite-image argument; it does not
construct a raw history or assert that a delayed event occurs. The final
application still needs the constructed arrival/birth readback and the same
executed event, followed by reflection of the ambient preimage to one later
proper stage. No final FI/AH, full CH Talagrand or official solution is claimed.

## Actual coherent history from CH

`SignedOrdinalHistory.run` now constructs one coherent family of actual
countable-stage states from `continuum = aleph-one` alone. A strict-past
well-founded fixpoint proves totality and pairwise coherence, then recovers
the canonical present values. The run unfolds to its own actual advancement:
the initial predecessor, the same selected successor Q/R, or the literal
proper-limit extension of its own strict archive. No complete-history or
step-supplier hypothesis provides the run.

Whole original U/B/V/nu birth families, their onto proofs and every original
Label are preserved by exact transports. Permanent reservoirs are read from
the same outgoing event at max(row,label). Proper F retains regular signed
limits of total variation at most one for arbitrary original norm-one lifts.
Cofinal ordinary, delayed and launch treatments refer to the same selected
Q/R and the original birth clopen codec; local delayed eligibility is proved
stable after construction without consulting a future final space.

This closes the coherent-history construction step, not Problem 8.2. The
literal final omega-one Prefix, post-run Data/Laws, concrete RawHistory and
joint signed-ball/Grothendieck/anti-homeomorphism endpoints remain separate
obligations. FullCHLeanSolved and officialSolved remain zero. The four-slot
information audit is unfinished under issue 21750; the compiled Reg modules
currently reconstruct the exact source statements and do not claim
`declared_validated` registration.


## Literal final space and every proper slice

`SignedOrdinalRealization.finalPrefix` constructs the literal omega-one
Prefix from the same canonical coherent `SignedOrdinalHistory.run`, without
an assumed completed history. Its final space is the actual compatible-thread
subset of the Boolean cube. The initial omega cube remains an onto image.
Every proper cutoff, including zero, finite cutoffs, omega and successor last
rows, has concrete `properData` and the original `properLaws`. No Data, metric
or countable-stage F is asserted at the final omega-one cutoff.

Whole U/B/V/nu families and all original Label-by-Nat measures are read from
the same actual birth through equality of literal carriers. Successor
carriers, projections, permanent reservoirs, historical J and prepared
measures read the identical selected Q/R. `SignedOrdinalRawHistory.rawHistory`
is the concrete raw history of this run; no raw-history supplier remains in
that construction.

These results complete the final-space and proper-slice construction layer.
Ordinary and delayed treatment cofinality, and support-launch cofinality, are
proved on the actual run. `SignedOrdinalActualReindex` supplies one eta for
the actual whole-birth measure and every support launch, including self-row
events and rejected reservations. Its new labels decode to original measure
labels no larger than themselves. `SignedOrdinalReindexedLaws` therefore
retains all original A-F laws on every proper cutoff, including every-choice
signed F and the regular reference measure of norm at most one. Every new
label reads the same actual whole-birth measure at every natural index.

`SignedOrdinalActualG` transports the unchanged selected Result to the literal
successor carrier. A single clopen and strictly increasing column sequence,
fixed before the signed lifts, give both the infinite evaluations at least
one sixth and the infinite exact zero evaluations for every complete signed
norm-one lift sequence. No positivity restriction is added. The private
`actual_scheme` composition in `TalagrandTopologicalConsequences` combines
these statements on the same finalPrefix, retaining the initial cube and
literal onto restrictions. Its targeted Lean build has passed. The subsequent public total theorem below
consumes this composition together with the geometric and analytic endpoints.

The information audit remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/21750. The delivered
Reg modules check exact source reconstruction, including the public transport
and proper-slice statements; this does not constitute a declared_validated
four-slot registration.

## Combined CH theorem

`TalagrandTopologicalConsequences.actual_CH_Talagrand_scheme_and_endpoints`
has passed a targeted Lean 4.35 build. Its only input is continuum = aleph-one.
Every conclusion concerns exactly `(SignedOrdinalRealization.finalPrefix
hCH).LimitSpace`, with its actual inherited topology. The proof consumes the
complete original scheme, closed-cover Boolean insertion at successors,
proper-limit and final-thread equations, and the G coordinate-cylinder
identity. Every proper stage is compact Hausdorff, zero-dimensional and
metrizable. No diamond, completed-history, capture, Hball or no-sequence
hypothesis remains.

The same space has finite continuous disjoint images of closed domains;
therefore every two disjoint homeomorphic closed subspaces are finite,
stronger than Theorem A's nonmetrizable closed-copy prohibition. It has no
nonempty compact binary-copy tower, with no nesting or infinitude restriction.
The actual signed endpoint theorem gives full regular signed oscillation,
excludes all continuous StoneCech injections into the entire real signed dual
unit ball, and proves convergence under arbitrary continuous bidual tests for
every weak-star convergent dual sequence, without an input norm bound.
Every convergent point sequence is eventually its actual limit. Evaluation
and the omega-cube quotient yield point-space no-beta, infinitude, failure of
first countability and nonmetrizability.

This is the combined formal target of the original Problem 8.2, preregistered
in https://github.com/the-omega-institute/trureturing/issues/22300 before its
first combined compilation. The Problems dossier
`kania-kakol-2026-problem-8-2-ch-talagrand` records the exact statement bridge
and bounded literature search. The scoped report and canonical Scribe emission have passed: 66 modules and
2,138 declarations, with only propext, Classical.choice and Quot.sound.
Three independent fixed-source reviews approved; PR 22319 tracks the separate
required CI and merge evidence. The unavailable oracle seat used its documented
Codex fallback, without a model-family diversity claim.
Official acceptance and worldwide uniqueness are not claimed; officialSolved
remains zero. Problem 8.1 and the full Cp metrizable quotient problem remain
outside this theorem. The information registration remains unfinished under
issue 21750; exact-source Reg reconstruction is not declared_validated.
