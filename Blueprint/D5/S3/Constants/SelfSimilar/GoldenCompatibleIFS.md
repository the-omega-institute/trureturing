# Golden-Compatible Iterated Function Systems

## Abstract

Golden-compatible affine similarities contract compact-set space and determine a unique nonempty compact attractor.

**Lemma 1.1 (Golden-compatible branches are continuous).**

$$\forall S, i, \operatorname{Continuous}\left(\operatorname{branch}\left(S, i\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.branch_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each branch is an affine map of the complex plane: a positive golden scale followed by a unit-modulus rotation, then a translation. These operations are continuous, so every branch carries compact sets to compact sets.

**Lemma 1.2 (Each branch has its exact golden similarity ratio).**

$$\forall S, i, x, y, \operatorname{dist}\left(\operatorname{branch}\left(S, i, x\right), \operatorname{branch}\left(S, i, y\right)\right) = \varphi^{-\operatorname{exponent}\left(S, i\right)} \cdot \operatorname{dist}\left(x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.branch_dist_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the branch indexed by i, the distance between two images is the original distance multiplied by the inverse golden ratio raised to that branch's exponent.

The translation cancels in a difference and the prescribed complex exponential is a rotation of modulus one. Thus only the positive golden scaling factor changes distance.

**Lemma 1.3 (Positive exponents give strict contraction ratios).**

$$\forall S, i, \varphi^{-\operatorname{exponent}\left(S, i\right)} < 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.branch_ratio_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse golden ratio lies strictly between zero and one. Since every branch exponent is positive, its corresponding power remains strictly below one, so no branch is merely nonexpansive.

**Lemma 1.4 (Each compact-set branch map has the common Lipschitz bound).**

$$\forall S, i, K, L, \operatorname{hausdorffDist}\left(\operatorname{compactBranch}\left(S, i, K\right), \operatorname{compactBranch}\left(S, i, L\right)\right) \leq \varphi^{-1} \cdot \operatorname{hausdorffDist}\left(K, L\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.compactBranch_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping nonempty compact sets through a single branch increases their Hausdorff distance by at most the inverse golden ratio. The sharper branch-specific power is bounded by this common constant because all exponents are positive.

Nearest-point comparisons in both directions transfer the pointwise distance estimate to Hausdorff distance, yielding a uniform bound independent of the branch index.

**Lemma 1.5 (Finite unions preserve the common Lipschitz bound).**

$$\forall S, s, K, L, \operatorname{Nonempty}\left(s\right) \Rightarrow \operatorname{hausdorffDist}\left(\operatorname{finiteHutchinson}\left(S, s, K\right), \operatorname{finiteHutchinson}\left(S, s, L\right)\right) \leq \varphi^{-1} \cdot \operatorname{hausdorffDist}\left(K, L\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.finite_hutchinson_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonempty finite collection of branches, the union of their compact images is Lipschitz with the same inverse-golden constant. Taking a finite union combines component errors by their maximum, so it introduces no larger factor.

Induction over the branch collection lifts the single-branch estimate to the finite Hutchinson union without weakening the bound.

**Lemma 1.6 (The Hutchinson operator is a strict contraction).**

$$\forall S, \operatorname{FiniteNonemptyGoldenIFS}\left(S\right) \Rightarrow \operatorname{ContractingWith}\left(\varphi^{-1}, \operatorname{hutchinson}\left(S\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.hutchinson_contracting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonempty golden-compatible system, the Hutchinson operator takes the union of all branch images of a nonempty compact set. Its Lipschitz constant is at most the inverse golden ratio.

Because that constant is strictly below one, the finite-union estimate upgrades directly to a contraction on the Hausdorff metric space of nonempty compact subsets of the complex plane.

**Theorem 1.7 (Every finite nonempty golden-compatible IFS has a unique attractor).**

$$\forall S, \operatorname{FiniteNonemptyGoldenIFS}\left(S\right) \Rightarrow \exists! F \in \operatorname{NonemptyCompacts}\left(C\right), F = \operatorname{hutchinson}\left(S, F\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.golden_compatible_ifs_has_unique_attractor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite nonempty golden-compatible planar iterated function system has exactly one nonempty compact set fixed by its Hutchinson operator. Equivalently, this attractor is the union of its images under all branches.

The space of nonempty compact subsets of the complex plane is complete in the Hausdorff metric. The strict Hutchinson contraction therefore has a fixed point, and contraction uniqueness identifies every compact solution of the invariance equation with that point.

## References

- Truth anchor: `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.branch_continuous`
- Truth anchor: `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.branch_dist_eq`
- Truth anchor: `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.branch_ratio_lt_one`
- Truth anchor: `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.compactBranch_lipschitz`
- Truth anchor: `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.finite_hutchinson_lipschitz`
- Truth anchor: `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.golden_compatible_ifs_has_unique_attractor`
- Truth anchor: `D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS.hutchinson_contracting`
