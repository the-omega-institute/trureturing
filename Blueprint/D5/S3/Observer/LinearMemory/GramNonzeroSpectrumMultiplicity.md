# Nonzero Gram Spectrum and Multiplicity

## Abstract

Rectangular adjoint Gram matrices have identical nonzero spectra with algebraic multiplicity.

**Theorem 1.1 (The nonzero Gram spectra agree with multiplicity).**

$$\begin{aligned}\forall K, m, n: \operatorname{Type},\\{}[\operatorname{RCLike}(K)], [\operatorname{Fintype}(m)], [\operatorname{DecidableEq}(m)],\\{}[\operatorname{Fintype}(n)], [\operatorname{DecidableEq}(n)],\\\forall M: \operatorname{Matrix}(m, n, K), lambda: K,\\{}lambda \neq 0 \Rightarrow (\operatorname{IsRoot}(\operatorname{charpoly}(\operatorname{mul}(\operatorname{conjTranspose}(M), M)), lambda) \iff \operatorname{IsRoot}(\operatorname{charpoly}(\operatorname{mul}(M, \operatorname{conjTranspose}(M))), lambda)) \land\\{}(\operatorname{rootMultiplicity}(lambda, \operatorname{charpoly}(\operatorname{mul}(\operatorname{conjTranspose}(M), M))) = \operatorname{rootMultiplicity}(lambda, \operatorname{charpoly}(\operatorname{mul}(M, \operatorname{conjTranspose}(M))))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/GramNonzeroSpectrumMultiplicity.gram_nonzero_spectrum_with_algebraic_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rectangular characteristic-polynomial identity differs only by powers of the polynomial variable. At a nonzero scalar those factors have zero root multiplicity, leaving both root membership and algebraic multiplicity unchanged between the two adjoint Gram products.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/GramNonzeroSpectrumMultiplicity.gram_nonzero_spectrum_with_algebraic_multiplicity`
