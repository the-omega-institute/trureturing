# A repeated five-site potential refutes odd-period regularity

## Abstract

A nonzero singular point for the odd clause of Conjecture 3.

M. Faust, L. Friedman, G. O’Malley, R. Ramos and A. Sharma, Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian, arXiv:2602.08304v1. All Fin indices below are zero-based; q=2m+1 and generator k+1 corresponds to source p′ₖ₊₁. Proof components of Fin indices are suppressed by ellipses. Natural subtraction is truncated subtraction and Nat.mod is remainder. Section 3, p. 7: “we are always referring to the multiplicity of a point according to the defining ideal (not with respect to the radical).”

**Definition 1.1 (Floquet matrix at z=1).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall n \in \operatorname{Nat},\; \forall V \in \operatorname{Fin}\left(n\right) \to R,\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{floquetMatrix}\left(n, V\right)\left(i, j\right) = \operatorname{if} (i = j) \operatorname{then} V\left(i\right) \operatorname{else} \operatorname{if} (\operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(i\right) + 1, n\right) = \operatorname{val}\left(j\right) \lor \operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(j\right) + 1, n\right) = \operatorname{val}\left(i\right)) \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.floquetMatrix` (`✓ std3`).

*Citation.* M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma (2026). *Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian*. DOI: [10.48550/arXiv.2602.08304](https://doi.org/10.48550/arXiv.2602.08304). URL: <https://arxiv.org/abs/2602.08304v1>.

*Commentary.*

Section 2, p. 3: “Thus, from here on we write L_V in place of L_V(1)”. The diagonal is V and each cyclic edge has coefficient one.

**Definition 1.2 (The characteristic polynomial).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall n \in \operatorname{Nat},\; \forall V \in \operatorname{Fin}\left(n\right) \to R,\; \operatorname{floquetCharPoly}\left(n, V\right) = \operatorname{Matrix}.\operatorname{det}\left(\operatorname{Matrix}.\operatorname{map}\left(\operatorname{floquetMatrix}\left(n, V\right), \operatorname{Polynomial}.\operatorname{C}\right) - \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Polynomial}.\operatorname{X}, 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.floquetCharPoly` (`✓ std3`).

*Citation.* M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma (2026). *Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian*. DOI: [10.48550/arXiv.2602.08304](https://doi.org/10.48550/arXiv.2602.08304). URL: <https://arxiv.org/abs/2602.08304v1>.

*Commentary.*

Section 2, p. 3: “Let D_V(λ) denote the characteristic polynomial of L_V”. The determinant uses L_V−λI, exactly with this sign.

**Definition 1.3 (Antisymmetric specialization).**

$$\forall m \in \operatorname{Nat},\; \forall j \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; \operatorname{specializedPotential}\left(m, j\right) = \operatorname{if} (\operatorname{val}\left(j\right) < m) \operatorname{then} \operatorname{MvPolynomial}.\operatorname{X}\left(\langle\operatorname{val}\left(j\right), ...\rangle\right) \operatorname{else} \operatorname{if} (\operatorname{val}\left(j\right) = m) \operatorname{then} 0 \operatorname{else} -(\operatorname{MvPolynomial}.\operatorname{X}\left(\langle2 \cdot m - \operatorname{val}\left(j\right), ...\rangle\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.specializedPotential` (`✓ std3`).

*Citation.* M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma (2026). *Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian*. DOI: [10.48550/arXiv.2602.08304](https://doi.org/10.48550/arXiv.2602.08304). URL: <https://arxiv.org/abs/2602.08304v1>.

*Commentary.*

Section 4, p. 8: “For odd n= 2m+1, this yields a potential function of the form (u₁, …, uₘ, 0, −uₘ, …, −u₁).” The source sites 1 through 2m+1 correspond to Fin indices 0 through 2m.

**Definition 1.4 (Difference from the free polynomial).**

$$\forall m \in \operatorname{Nat},\; \operatorname{zeta}\left(m\right) = \operatorname{floquetCharPoly}\left(2 \cdot m + 1, \operatorname{specializedPotential}\left(m\right)\right) - \operatorname{floquetCharPoly}\left(2 \cdot m + 1, (0: \operatorname{Fin}\left(2 \cdot m + 1\right) \to \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(m\right), \operatorname{Complex}\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.zeta` (`✓ std3`).

*Citation.* M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma (2026). *Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian*. DOI: [10.48550/arXiv.2602.08304](https://doi.org/10.48550/arXiv.2602.08304). URL: <https://arxiv.org/abs/2602.08304v1>.

*Commentary.*

Section 2 defines ζ_V := D_V(λ) − D_𝟎(λ). Here V is the specialized potential.

**Definition 1.5 (Generators of I′).**

$$\forall m \in \operatorname{Nat},\; \forall k \in \operatorname{Nat},\; \operatorname{pPrime}\left(m, k\right) = (-(1))^{2 \cdot m + 1 + k} \cdot \operatorname{Polynomial}.\operatorname{coeff}\left(\operatorname{zeta}\left(m\right), 2 \cdot m + 1 - 2 \cdot k\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.pPrime` (`✓ std3`).

*Citation.* M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma (2026). *Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian*. DOI: [10.48550/arXiv.2602.08304](https://doi.org/10.48550/arXiv.2602.08304). URL: <https://arxiv.org/abs/2602.08304v1>.

*Commentary.*

Section 4 defines p′ₖ := (−1)ⁿ⁺ᵏ ζ_U[λⁿ⁻²ᵏ] and I′ := ⟨p′₁, …, p′ₘ⟩. The expression defines pPrime for every natural k; only k=1 through m generate I′.

**Definition 1.6 (The common zero set).**

$$\forall m \in \operatorname{Nat},\; \forall u \in \operatorname{Fin}\left(m\right) \to \operatorname{Complex},\; \operatorname{InVariety}\left(m, u\right) = (\forall k \in \operatorname{Nat},\; (k \in \operatorname{Finset}.\operatorname{Icc}\left(1, m\right)) \Rightarrow (\operatorname{MvPolynomial}.\operatorname{eval}\left(u, \operatorname{pPrime}\left(m, k\right)\right) = 0))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.InVariety` (`✓ std3`).

*Citation.* M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma (2026). *Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian*. DOI: [10.48550/arXiv.2602.08304](https://doi.org/10.48550/arXiv.2602.08304). URL: <https://arxiv.org/abs/2602.08304v1>.

*Commentary.*

Every generator with index in the closed interval from 1 to m vanishes at u.

**Definition 1.7 (Jacobian of the generators).**

$$\forall m \in \operatorname{Nat},\; \forall u \in \operatorname{Fin}\left(m\right) \to \operatorname{Complex},\; \forall k \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{jacobianAt}\left(m, u\right)\left(k, j\right) = \operatorname{MvPolynomial}.\operatorname{eval}\left(u, \operatorname{MvPolynomial}.\operatorname{pderiv}\left(j, \operatorname{pPrime}\left(m, \operatorname{val}\left(k\right) + 1\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.jacobianAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma (2026). *Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian*. DOI: [10.48550/arXiv.2602.08304](https://doi.org/10.48550/arXiv.2602.08304). URL: <https://arxiv.org/abs/2602.08304v1>.

*Commentary.*

Rows index generators from pPrime m 1 to pPrime m m; columns index the m coordinates. Entries are evaluated formal partial derivatives.

**Definition 1.8 (Jacobian regularity).**

$$\forall m \in \operatorname{Nat},\; \forall u \in \operatorname{Fin}\left(m\right) \to \operatorname{Complex},\; \operatorname{IsRegularPoint}\left(m, u\right) = \left(\operatorname{Matrix}.\operatorname{det}\left(\operatorname{jacobianAt}\left(m, u\right)\right) \ne 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.IsRegularPoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma (2026). *Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian*. DOI: [10.48550/arXiv.2602.08304](https://doi.org/10.48550/arXiv.2602.08304). URL: <https://arxiv.org/abs/2602.08304v1>.

*Commentary.*

The proposition uses the Jacobian determinant criterion, with no separate local-algebra multiplicity theorem.

**Definition 1.9 (Conjecture 3, odd clause).**

$$\operatorname{claim} = (\forall m \in \operatorname{Nat},\; (2 \le m) \Rightarrow (\forall u \in \operatorname{Fin}\left(m\right) \to \operatorname{Complex},\; (u \ne 0) \Rightarrow ((\operatorname{InVariety}\left(m, u\right)) \Rightarrow (\operatorname{IsRegularPoint}\left(m, u\right)))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.claim` (`✓ std3`).

*Citation.* M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma (2026). *Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian*. DOI: [10.48550/arXiv.2602.08304](https://doi.org/10.48550/arXiv.2602.08304). URL: <https://arxiv.org/abs/2602.08304v1>.

*Commentary.*

Conjecture 3, p. 11: “When q is odd, then V(I′) has only regular nonzero points, and when it is an even number greater than 6 there is a single singular point, up to symmetry, of multiplicity 2^{q/2−2}. Moreover, the multiplicity at 𝟎 is 2^{⌊q/2⌋}.” The quantifier ranges over every odd q=2m+1>3. Period means a period, without a least-period requirement.

**Theorem 1.10 (Refutation at q=15).**

$$\neg (\forall m \in \operatorname{Nat},\; (2 \le m) \Rightarrow (\forall u \in \operatorname{Fin}\left(m\right) \to \operatorname{Complex},\; (u \ne 0) \Rightarrow ((\operatorname{InVariety}\left(m, u\right)) \Rightarrow (\operatorname{IsRegularPoint}\left(m, u\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma (2026). *Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian*. DOI: [10.48550/arXiv.2602.08304](https://doi.org/10.48550/arXiv.2602.08304). URL: <https://arxiv.org/abs/2602.08304v1>.

*Commentary.*

Choose a with a²=1−2i and u=(a,ia,0,−ia,−a,a,ia). The corresponding fifteen-site potential repeats (a,ia,0,−ia,−a) three times. Its five-step transfer trace equals the free trace, and determinant-one evolution preserves that equality for the cube, so every generator vanishes. Cyclic shift by five preserves the potential and the characteristic coefficients. Differentiation and antisymmetric specialization identify Jacobian columns 0 and 5, forcing zero determinant. The coordinate a is nonzero. This refutes the stated odd clause; the least-period variant, the even clause and origin multiplicity are not settled here.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.InVariety`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.IsRegularPoint`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.floquetCharPoly`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.floquetMatrix`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.jacobianAt`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.pPrime`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.specializedPotential`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.zeta`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace](CyclicTridiagonalTransferTrace.md)
