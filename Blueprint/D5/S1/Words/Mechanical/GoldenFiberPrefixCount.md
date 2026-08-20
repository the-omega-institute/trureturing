# Golden Fiber Prefix Count

## Abstract

Positive-indexed golden fiber letters have an exact floor prefix count.

**Definition 1.1 (Positive-indexed golden fiber letter).**

$$\forall m\in\mathbb{N},\ f_m = 1 + \mathbf{1}_{\operatorname{goldenWord}(m-1)=\mathrm{true}}$$

*Formalization.* `D5/S1/Words/Mechanical/GoldenFiberPrefixCount.goldenFiberLetter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural index m, the fiber letter is one plus the indicator of the golden-word bit at m minus one. Thus its positive-index sequence begins 2, 1, 2, 2, 1, and agrees with the established one-index mechanical bridge.

**Theorem 1.2 (Golden fiber prefixes have the exact floor count).**

$$\forall n\in\mathbb{N},\ \sum_{m=1}^{n} f_m = \lfloor\varphi(n+1)\rfloor - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/GoldenFiberPrefixCount.golden_fiber_prefix_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, summing the positive-indexed letters f_m from m = 1 through n gives floor(phi times (n + 1)) minus one. The empty prefix at n = 0 is included.

Pinned Mathlib was searched before proving. Its golden-ratio inverse and conjugate identities and its integer-floor shift laws are exact component hits, but no declaration states this prefix identity. The repository search likewise found no duplicate. GoldenBeattyCount proves the closely related inverse threshold including index zero, but does not state this positive-fiber sum. The direct reusable hits are the generic lowerMechanicalWindowTrueCount_eq_floor theorem and the exact golden-word shift lowerMechanicalWord_golden, so this declaration is a thin specialization: count the true bits in the shifted mechanical window, then rewrite phi as one plus its inverse.

This is an honest partial closure of clause (i) only. The later constant evaluation, limit formulas, isolated correction term, zero-drift claim, and numerical registration in clauses (ii) through (v) remain unresolved and are not asserted here.

## References

- Truth anchor: `D5/S1/Words/Mechanical/GoldenFiberPrefixCount.goldenFiberLetter`
- Truth anchor: `D5/S1/Words/Mechanical/GoldenFiberPrefixCount.golden_fiber_prefix_count`
