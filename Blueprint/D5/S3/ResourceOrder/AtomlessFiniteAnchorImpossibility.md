# Atomless Finite Anchor Impossibility

## Abstract

Finite anchor families on null-singleton probability spaces admit implementations that pass every exposed test while being wrong almost everywhere.

**Theorem 1.1 (Finite anchors permit almost-everywhere evasion).**

$$\forall A, X, mu:\operatorname{Measure}(X)[\operatorname{Fintype}(A)][\operatorname{NullSingletonClass}(mu)][\operatorname{IsProbabilityMeasure}(mu)], S:A\to\operatorname{Finset}(X), t:X\to\operatorname{Bool}, \exists p:X\to\operatorname{Bool}, (\forall a, x, x \in S(a) \Rightarrow p(x)=t(x)) \land mu(\{x \mid p(x)\neq t(x)\})=1.$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/AtomlessFiniteAnchorImpossibility.atomless_finite_anchor_evasion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the union of all exposed finite suites. It is finite, hence countable, so Mathlib's Set.Countable.measure_zero makes it null under the null-singleton hypothesis.

The witness agrees with the truth on that union and flips the Boolean truth off it. It passes every suite, and its error set is exactly the complement of a null set, whose probability is one.

The source atom is an orphaned multi-clause fragment. This theorem formalizes its complete nonatomic information-theoretic core. It does not assert the fragment's undefined covering number or optimal anchor capacity, its random-family Chernoff estimate, or its conditional PRG interpretation.

Repository searches found the finite coverage-and-evasion theorem and general countable nullity results, but no declaration combining passage of every supplied suite with an almost-everywhere error witness.

## References

- Truth anchor: `D5/S3/ResourceOrder/AtomlessFiniteAnchorImpossibility.atomless_finite_anchor_evasion`
- Dependency: [D5/S3/ResourceOrder/FiniteAnchorCoverage](FiniteAnchorCoverage.md)
