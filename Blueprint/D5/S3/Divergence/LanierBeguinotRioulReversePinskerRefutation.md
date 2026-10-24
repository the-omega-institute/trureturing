# A counterexample to the maximal reverse Pinsker bound

## Abstract

A noncommuting qubit pair violates the maximal reverse Pinsker bound.

Lanier, Béguinot and Rioul, arXiv:2501.14340v1, §III-C, p. 5: “We conjecture that (49) is in fact not necessary for (50) to hold.” The same paragraph states: “Our bound holds in general for any f-divergence, in particular for the maximal f-divergence.”

**Definition 1.1 (The maximal spectral divergence).**

$$\forall (n: \mathbb{N}), \forall (f: \mathbb{R} \to \mathbb{R}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{maxDivergence}\left(f, rho, sigma\right) = \operatorname{re}\left(\operatorname{trace}\left(\operatorname{sqrt}\left(sigma\right) \cdot \operatorname{cfc}\left(f, (\operatorname{sqrt}\left(sigma\right))^{-1} \cdot rho \cdot (\operatorname{sqrt}\left(sigma\right))^{-1}\right) \cdot \operatorname{sqrt}\left(sigma\right)\right)\right)$$

*Formalization.* `D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.maxDivergence` (`✓ std3`).

*Citation.* D. Lanier; J. Béguinot; O. Rioul (2025). *From Classical to Quantum: Explicit Classical Distributions Achieving Maximal Quantum f-Divergence*. DOI: [10.48550/arXiv.2501.14340](https://doi.org/10.48550/arXiv.2501.14340). URL: <https://arxiv.org/abs/2501.14340v1>.

*Commentary.*

Equation (4), p. 1, is the real part of the trace of the displayed product. The matrix function is Mathlib's continuous functional calculus. For the operator-convex generator f(x)=(x−1)², its status as a quantum f-divergence satisfying Definition 2 uses the Matsumoto theorem cited in the source. That general data-processing theorem is not proved here.

**Definition 1.2 (The proposed right-hand side).**

$$\forall (n: \mathbb{N}), \forall (f: \mathbb{R} \to \mathbb{R}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{reversePinskerBound}\left(f, rho, sigma\right) = \frac{\operatorname{traceNorm}\left(rho - sigma\right)}{2} \cdot (\frac{\operatorname{f}\left(\operatorname{sInf}\left(\operatorname{spectrum}\left(\mathbb{R}, (\operatorname{sqrt}\left(sigma\right))^{-1} \cdot rho \cdot (\operatorname{sqrt}\left(sigma\right))^{-1}\right)\right)\right)}{1 - \operatorname{sInf}\left(\operatorname{spectrum}\left(\mathbb{R}, (\operatorname{sqrt}\left(sigma\right))^{-1} \cdot rho \cdot (\operatorname{sqrt}\left(sigma\right))^{-1}\right)\right)} + \frac{\operatorname{f}\left(\operatorname{sSup}\left(\operatorname{spectrum}\left(\mathbb{R}, (\operatorname{sqrt}\left(sigma\right))^{-1} \cdot rho \cdot (\operatorname{sqrt}\left(sigma\right))^{-1}\right)\right)\right)}{\operatorname{sSup}\left(\operatorname{spectrum}\left(\mathbb{R}, (\operatorname{sqrt}\left(sigma\right))^{-1} \cdot rho \cdot (\operatorname{sqrt}\left(sigma\right))^{-1}\right)\right) - 1})$$

*Formalization.* `D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.reversePinskerBound` (`✓ std3`).

*Citation.* D. Lanier; J. Béguinot; O. Rioul (2025). *From Classical to Quantum: Explicit Classical Distributions Achieving Maximal Quantum f-Divergence*. DOI: [10.48550/arXiv.2501.14340](https://doi.org/10.48550/arXiv.2501.14340). URL: <https://arxiv.org/abs/2501.14340v1>.

*Commentary.*

Equation (50), p. 4, uses the least and greatest points of the real spectrum of the relative matrix and the trace norm of the state difference. The numerical example below has spectral endpoints 4/5 and 6/5, so both denominators are nonzero.

**Definition 1.3 (The conjectured maximal-divergence inequality).**

$$(claim) \Leftrightarrow (\forall (n: \mathbb{N}), \forall (f: \mathbb{R} \to \mathbb{R}), (\operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ici}\left(0\right), f\right)) \Rightarrow ((\operatorname{f}\left(1\right) = 0) \Rightarrow (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{trace}\left(rho\right) = 1) \Rightarrow ((\operatorname{PosDef}\left(sigma\right)) \Rightarrow ((\operatorname{trace}\left(sigma\right) = 1) \Rightarrow (\operatorname{maxDivergence}\left(f, rho, sigma\right) \le \operatorname{reversePinskerBound}\left(f, rho, sigma\right))))))))$$

*Formalization.* `D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.claim` (`✓ std3`).

*Citation.* D. Lanier; J. Béguinot; O. Rioul (2025). *From Classical to Quantum: Explicit Classical Distributions Achieving Maximal Quantum f-Divergence*. DOI: [10.48550/arXiv.2501.14340](https://doi.org/10.48550/arXiv.2501.14340). URL: <https://arxiv.org/abs/2501.14340v1>.

*Commentary.*

“We conjecture that (49) is in fact not necessary for (50) to hold.” (§III-C, p. 5.) The displayed proposition is its maximal-divergence instance: every dimension, every real generator convex on the nonnegative half-line and zero at one, and every pair of positive semidefinite states with the second positive definite. Each state has trace one. No matrix-order condition on the absolute difference is imposed.

**Theorem 1.4 (A qubit counterexample).**

$$\neg (\forall (n: \mathbb{N}), \forall (f: \mathbb{R} \to \mathbb{R}), (\operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ici}\left(0\right), f\right)) \Rightarrow ((\operatorname{f}\left(1\right) = 0) \Rightarrow (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{trace}\left(rho\right) = 1) \Rightarrow ((\operatorname{PosDef}\left(sigma\right)) \Rightarrow ((\operatorname{trace}\left(sigma\right) = 1) \Rightarrow (\operatorname{maxDivergence}\left(f, rho, sigma\right) \le \operatorname{reversePinskerBound}\left(f, rho, sigma\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. Lanier; J. Béguinot; O. Rioul (2025). *From Classical to Quantum: Explicit Classical Distributions Achieving Maximal Quantum f-Divergence*. DOI: [10.48550/arXiv.2501.14340](https://doi.org/10.48550/arXiv.2501.14340). URL: <https://arxiv.org/abs/2501.14340v1>.

*Commentary.*

Let σ=diag(9/25,16/25) and ρ=((9/25,12/125),(12/125,16/25)). Both matrices have trace one; σ is positive definite and ρ is positive semidefinite. The positive square root of σ is diag(3/5,4/5), and the relative matrix is ((1,1/5),(1/5,1)), with spectrum {4/5,6/5}. For f(x)=(x−1)² its matrix function is I/25, giving maxDivergence=1/25=25/625. The absolute difference is (12/125)I, with trace norm 24/125, so reversePinskerBound=24/625. This contradicts the proposed inequality. The matrix ρ+σ−|ρ−σ|=((78/125,12/125),(12/125,148/125)) is positive definite. Thus the same pair also contradicts the conditional maximal-divergence statement of Theorem 4. The proof checks that stronger failure before deriving the displayed negation. The result concerns the spectral formula (4); the Definition 2 admissibility theorem and the source's other choices of quantum divergence remain separate.

## References

- Truth anchor: `D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.claim`
- Truth anchor: `D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.maxDivergence`
- Truth anchor: `D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.result`
- Truth anchor: `D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.reversePinskerBound`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Quantum/Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../Quantum/Matrix/SpectralPower.md)
- Dependency: [D5/S3/Resource/LogDet/PathSpectralClassical](../Resource/LogDet/PathSpectralClassical.md)
