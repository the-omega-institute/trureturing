# Dual Gram Condition Number

## Abstract

Dual Gram operators have one positive-spectrum condition number and paired weak modes.

**Theorem 1.1 (State and protocol conditioning are dual).**

$$\forall K \in \operatorname{Type}, V \in \operatorname{Type}, iota \in \operatorname{Type}, ell \in iota \to \operatorname{LinearMap}\left(K, V, K\right),\; \left(\operatorname{RCLike}\left(K\right) \land \left(\operatorname{NormedAddCommGroup}\left(V\right) \land \left(\operatorname{InnerProductSpace}\left(K, V\right) \land \left(\operatorname{FiniteDimensional}\left(K, V\right) \land \operatorname{Fintype}\left(iota\right)\right)\right)\right)\right) \Rightarrow \operatorname{let} M: \operatorname{LinearMap}\left(K, V, \operatorname{PiLp}\left(2, iota \to K\right)\right) = \operatorname{comp}\left(\operatorname{toLinearMap}\left(\operatorname{symm}\left(\operatorname{withLpLinearEquiv}\left(2, K, iota \to K\right)\right)\right), \operatorname{linearPi}\left(ell\right)\right); \operatorname{let} stateSpectrum: \operatorname{Set}\left(\mathbb{R}\right) = \left\{0 < lambda \land \operatorname{HasEigenvalue}\left(\operatorname{comp}\left(\operatorname{adjoint}\left(M\right), M\right), \operatorname{ofReal}\left(K, lambda\right)\right) \mid lambda \in \mathbb{R}\right\}; \operatorname{let} protocolSpectrum: \operatorname{Set}\left(\mathbb{R}\right) = \left\{0 < lambda \land \operatorname{HasEigenvalue}\left(\operatorname{comp}\left(M, \operatorname{adjoint}\left(M\right)\right), \operatorname{ofReal}\left(K, lambda\right)\right) \mid lambda \in \mathbb{R}\right\}; \frac{\operatorname{sSup}\left(stateSpectrum\right)}{\operatorname{sInf}\left(stateSpectrum\right)} = \frac{\operatorname{sSup}\left(protocolSpectrum\right)}{\operatorname{sInf}\left(protocolSpectrum\right)} \land \left(\forall sigma \in \mathbb{R},\; 0 < sigma \Rightarrow \left(\left(\exists v \in V,\; \operatorname{HasEigenvector}\left(\operatorname{comp}\left(\operatorname{adjoint}\left(M\right), M\right), \operatorname{ofReal}\left(K, sigma^{2}\right), v\right)\right) \Leftrightarrow \left(\exists a \in \operatorname{PiLp}\left(2, iota \to K\right),\; \operatorname{HasEigenvector}\left(\operatorname{comp}\left(M, \operatorname{adjoint}\left(M\right)\right), \operatorname{ofReal}\left(K, sigma^{2}\right), a\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/DualGramConditionNumber.dual_gram_condition_number` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite indexed family of scalar readouts constructs the observation map coordinatewise on the square-summable protocol carrier. The positive state and protocol Gram spectra are displayed as literal sets.

Their supremum-to-infimum ratios agree. For every positive singular value, the observation map and its adjoint transfer nonzero eigenvectors between the state and protocol Gram operators at the same square.

The proof applies the pinned library's eigenspace and linear-map laws; the observation map is the canonical coordinatewise construction already used by the dual-Gram family.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/DualGramConditionNumber.dual_gram_condition_number`
