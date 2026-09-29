# Finite-Branching Path Clock Criterion

## Abstract

Nonnegative clocks on finite words have equivalent path, depth, and sublevel criteria.

**Definition 1.1 (Path clock).**

$$\forall A: Type, c: (\operatorname{List}(A)) \to (A) \to \mathbb{R}, h: \operatorname{List}(A),\\{}T_{c}(h) = \sum _{i: \operatorname{Fin}(\operatorname{length}(h))} \operatorname{c}(\operatorname{take}(h, i), \operatorname{get}(h, i)).$$

*Formalization.* `D5/S3/Estimation/ExperimentCost/FiniteBranchingPathClockCriterion.pathClock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The clock of a finite word is the sum of the calibrated costs of its successive edges. The cost of a letter is evaluated on the complete prefix preceding that letter.

**Definition 1.2 (Minimum path clock at a depth).**

$$\forall A: Type, [\operatorname{Fintype}(A)], [\operatorname{Nonempty}(A)],\\{}c: (\operatorname{List}(A)) \to (A) \to \mathbb{R}, n: \mathbb{N},\\{}g_{c}(n) = \min _{w: (\operatorname{Fin}(n)) \to A} T_{c}(\operatorname{ofFn}(w)).$$

*Formalization.* `D5/S3/Estimation/ExperimentCost/FiniteBranchingPathClockCriterion.minimumPathClock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each depth, the minimum is taken over every word on the finite nonempty alphabet. Thus the minimum is attained.

**Theorem 1.3 (Path divergence, depth control, and finite sublevels).**

$$\forall A: Type, [\operatorname{Fintype}(A)], [\operatorname{Nonempty}(A)],\\{}c: (\operatorname{List}(A)) \to (A) \to \mathbb{R}, (\forall h: \operatorname{List}(A), x: A, 0 \leq \operatorname{c}(h, x)) \Rightarrow \\{}\operatorname{List.TFAE}(\forall omega: (\mathbb{N}) \to A, \operatorname{Tendsto}(\Lambda n: \mathbb{N}, T_{c}(\operatorname{ofFn}(\Lambda i: \operatorname{Fin}(n), \operatorname{omega}(i))), atTop, atTop),\\{}\operatorname{Tendsto}(\Lambda n: \mathbb{N}, g_{c}(n), atTop, atTop),\\{}\forall b: \mathbb{R}, \operatorname{Finite}(\{h: \operatorname{List}(A) \mid T_{c}(h) \leq b\})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/FiniteBranchingPathClockCriterion.finite_branching_path_clock_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative increments make clocks monotone under extension. Hence the minimum clock is monotone in depth, and divergence of these minima bounds every clock sublevel by a finite set of short words.

A finite sublevel cannot contain all distinct prefixes of an infinite word. Conversely, bounded depth minima give nonempty finite level sets closed under restriction. Konig's infinity lemma selects a compatible sequence, producing an infinite word with bounded clock.

## References

- Truth anchor: `D5/S3/Estimation/ExperimentCost/FiniteBranchingPathClockCriterion.finite_branching_path_clock_criterion`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/FiniteBranchingPathClockCriterion.minimumPathClock`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/FiniteBranchingPathClockCriterion.pathClock`
