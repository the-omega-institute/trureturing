---
slug: mathoverflow-469781-weighted-orthogonal-minors
bibkey: meler2024weightedminors
doi: null
url: https://mathoverflow.net/questions/469781
triage: theorem
motivation_gids:
  - D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors.weighted_minors
---

# The full weighted orthogonal-minor inequality

## Problem

The source is meler (MathOverflow user 526848; real name unverified), [MO469781](https://mathoverflow.net/questions/469781), revision 1, GUID `F53D06CE-3805-43B9-9FEB-43A79F67F7AB`, CC BY-SA 4.0, with identical [MSE4902019](https://math.stackexchange.com/questions/4902019) crosspost. The [Library note](../Library/Geometry/meler2024weightedminors.md) owns the source citation. The complete external question is:

> Fix $n \geq 3$ and take any orthonormal vectors $x,y,z \in \mathbb{R}^n$. Let also $A \in M_n(\mathbb{R})$ be a symmetric matrix with positive entries ($A_{ij} = A_{ji} > 0$). Is the following inequality true? $$\sum_{i<j}A_{ij}\begin{vmatrix}x_i & x_j \\newline y_i & y_j \end{vmatrix}^2 \leq \sum_{i<j<k}\max(A_{ij},A_{ik},A_{jk})\begin{vmatrix}x_i & x_j & x_k \\newline y_i & y_j & y_k \\newline z_i & z_j & z_k \end{vmatrix}^2$$

For ordinary mathematical rendering, the literal `\\newline` separators in that immutable transcription mean row breaks. Thus the determinants have rows (x,y) and (x,y,z), respectively, and increasing coordinate columns. No statement is changed by that typographic reading.

The source-to-Lean map is exact: `n : ℕ` covers every original integer n≥3; `x y z : EuclideanSpace ℝ (Fin n)` are the three real vectors; `Orthonormal ℝ ![x,y,z]` supplies all unit norms and pairwise orthogonalities; `A : Matrix (Fin n) (Fin n) ℝ`, `∀ i j, A i j = A j i` and `∀ i j, 0 < A i j` give precisely the matrix hypotheses. Conditional finite sums select `i < j` and `i < j ∧ j < k`. The literal `Matrix.det !![...]` terms are the displayed two- and three-row determinants, and `max (A i j) (max (A i k) (A j k))` is the same three-edge maximum. Zero-based coordinate labels merely relabel the source coordinates. The native theorem quantifies all natural dimensions; below three its orthonormal-triple premise has no instance. No distance, positive-definiteness, nonzero-minor, rationality or finite-dimension-cutoff premise is added.

## Motivation

This compares weighted squared coordinates of a two-dimensional orthonormal plane with those of its extension by one orthogonal unit vector. Arbitrary positive edge weights make the joint pair/triple support relation essential. The source question is this inequality, separately from the motivating projective-distance conjecture.

## Gap

The bounded source reading in [issue #25537](https://github.com/the-omega-institute/trureturing/issues/25537) reported no answer on either complete thread. It read the Lyons v4 nested-subspace stochastic-domination theorem and the specified portions of the motivating Bistroń–Eckstein–Friedland–Miller–Życzkowski paper. The supplied formal map additionally searched repository public/private declarations, pinned Mathlib and a bounded third-party Lean scope; it found reusable algebraic/projection ingredients but no ready full weighted-minor Lean theorem. These are bounded readings, not an exhaustive absence or priority claim. The completed array argument supplies the mathematical bridge; independent prefreeze acceptance and delivery remain pending.

## Route

For skew pair arrays v and alternating triple arrays b, define lift by `z(i)v(j,k)-z(j)v(i,k)+z(k)v(i,j)` and lower by summing `z(k)b(k,i,j)` over k. With pair mass half the ordered squared sum and triple mass one sixth, the finite adjoint identity and energy identity imply unit-vector contraction by finite squared Cauchy-Schwarz. Determinant expansion identifies the triple minors with the lift of pair minors; orthogonality identifies their lowering with the pair minors.

For each symmetric pair family retain exactly the triples containing a pair in that family. Support locality and contraction give the family domination inequality. An exact finite expansion into upper-threshold indicators represents every nonnegative weight, with ties retained. The triple's union-of-edge threshold condition is precisely the threshold condition for its three-edge maximum. Summing these inequalities and cancelling the ordered-tuple factors two and six yields the exact increasing-index inequality. The repository proof directly establishes this mechanism; no coupling or probability normalization is assumed.

## Falsifier

A falsifier of the source assertion must give an integer n≥3, a real orthonormal triple and a real symmetric entrywise strictly positive matrix for which the displayed left side exceeds the right side with the exact determinants and maximum. A distance-only claim, approximate violation, nonorthonormal triple or matrix outside that domain does not answer this question. This criterion describes the source assertion; it does not contest the kernel-checked theorem under its stated assumptions.

## Evidence

The sole proof owner is `D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors.lean`, public theorem `AlternatingArrayContraction.weighted_minors`. Its [canonical Blueprint](../Blueprint/D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors.md) binds the closed formula to `D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors.weighted_minors`, acknowledges `meler2024weightedminors` as repo-derived provenance and carries a typed `OpenProblemResolutionClaim` with `Proved` for this dossier. This is the candidate full formal settlement; independent prefreeze acceptance, freeze and publication are pending. The prior independent ordinary-proof acceptance does not certify this Lean implementation.

The retained mirrored Reg source compiles but its four-slot audit remains unfinished: `declared_unresolved`, `IE-C050 ClosedTruthReadout`, `source.residual_requires_open`, reason `unclassified_form`, certificate and `escape_from` null, and continuation open. [Issue #25537](https://github.com/the-omega-institute/trureturing/issues/25537) is the parent-owned disclosure target. Compilation is not `declared_validated`, and an unknown residual is no undecidability theorem.

## Triage

This is the provisionally Tier 1 external named problem of issue #25537. The candidate resolution is **Proved** for the complete original question by `AlternatingArrayContraction.weighted_minors`, subject to the pending independent prefreeze acceptance and delivery. The proof is repository synthesis acknowledging the external question and established determinantal context, without a priority claim.

### What the settlement shows

**Proved in the existing proof owner:** coordinate-family domination, exact finite nonnegative threshold expansion and the final weighted comparison. The final public theorem includes n=3, zero minors, tied weights and equality. Its private `weighted_minors_all_tuples` helper accepts nonnegative weights, and its coordinate argument uses only unit z and orthogonality of z to x and y. These are existing proof-internal statements and assumptions, not additional published resolution units or new public theorems.

**Sharpness and equality:** the non-strict public conclusion preserves equality cases; no classification of all equality cases is proved or claimed here. The exact constant is the displayed one, with no loss from the ordered-tuple conversion. No separate optimality theorem is added.

**Unresolved neighbors:** a complete equality characterization and the motivating paper's Conjecture 2.1 on projective distances are outside this settlement. The full complex projective-distance assertion requires its own precise bridge and proof; this real positive-weight theorem alone does not certify it. No adjacent DPP coupling theorem or stronger complex-minor theorem is claimed. Audit, review and delivery work do not count as additional solved mathematical problems.

## ASSUMED-UNVERIFIED

The real-name attribution and the Library metadata publication year remain unverified as specified in that note. The bounded supplied literature/map reading establishes neither worldwide openness nor priority, exhaustive ecosystem coverage, author acceptance or the motivating distance conjecture. The compiled proof and Reg bytes are preserved; independent implementation acceptance, successful registration classification, parent-owned issue disclosure, canonical freezing/projections, final review and exact-head required CI/merge are separate unfinished obligations.
