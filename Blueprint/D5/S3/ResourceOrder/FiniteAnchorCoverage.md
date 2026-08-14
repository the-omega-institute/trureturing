# Finite Anchor Coverage

## Abstract

Finite bounded test families have bounded coverage and admit exact off-union evasion.

**Theorem 1.1 (Finite anchor coverage bound and evasion).**

$$\forall A, X[\operatorname{Fintype}(A)][\operatorname{DecidableEq}(X)], S:A\to\operatorname{Finset}(X), t:X\to\operatorname{Bool}, h,m\in \mathbb{N}, \operatorname{card}(A)\leq2^{h} \land (\forall a, \operatorname{card}(S(a))\leq m) \Rightarrow \operatorname{card}(\operatorname{coveredInputs}(S))\leq2^{h}\cdot m \land \exists p:X\to\operatorname{Bool}, (\forall a,x, x \in S(a) \Rightarrow p(x)=t(x)) \land \{x \mid p(x) \neq t(x)\}=X \setminus \operatorname{coveredInputs}(S).$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/FiniteAnchorCoverage.finite_anchor_coverage_bound_and_evasion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite anchor type represents all possible revealed seeds. The first hypothesis bounds its size by two to the anchor budget, and the second bounds every exposed suite by m inputs. Finset.card_biUnion_le then gives the displayed two-to-h times m coverage bound.

The witness implementation agrees with the truth on the union of all possible suites and flips the Boolean truth everywhere else. It therefore passes every suite while its error set is exactly the uncovered complement.

This is a partial closure of the leading finite-coverage clause only. The covering-number and logarithmic consequences, the nonatomic-domain clause, and the random-family sufficiency clause remain unresolved.

Pinned Mathlib supplies Finset.card_biUnion_le. Repository searches found no complete theorem combining that bound with the off-union implementation and exact error-set identity.

## References

- Truth anchor: `D5/S3/ResourceOrder/FiniteAnchorCoverage.finite_anchor_coverage_bound_and_evasion`
