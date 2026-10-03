# Graded Congruence Spectrum

## Abstract

A positive normalized congruence has uniformly graded canonical spectrum.

**Theorem 1.1 (Uniform graded bounds for the canonical decreasing spectrum).**

$$\forall n \in \mathbb{N}, H \in \mathbb{R} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), w \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; ((\operatorname{Monotone}\left(w\right)) \land \left((\operatorname{Tendsto}\left(H, \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(A\right)\right)) \land \left((\operatorname{PosDef}\left(A\right)) \land (\forall T \in \mathbb{R},\; (T > 0) \Rightarrow \operatorname{PosDef}\left(\operatorname{diag}\left((i \mapsto T^{w\left(i\right)} \times \sqrt(T))\right) \times H\left(T\right) \times \operatorname{diag}\left((i \mapsto T^{w\left(i\right)} \times \sqrt(T))\right)\right))\right)\right)) \Rightarrow \left(\exists c \in \mathbb{R}, C \in \mathbb{R}, d \in \mathbb{R},\; (c > 0) \land \left((C > 0) \land \left((d > 0) \land (\forall T \in \mathbb{R}, i \in \operatorname{Fin}\left(n\right), p \in T > 0,\; (T < d) \Rightarrow \left((c \times T^{2 \times w\left(i\right) + 1} \le \lambda\left(T, i\right)) \land (\lambda\left(T, i\right) \le C \times T^{2 \times w\left(i\right) + 1})\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GradedCongruenceSpectrum.graded_congruence_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary n, a real matrix family H tending to a positive-definite H₀ from the positive side, and a monotone integer grade w, form the actual congruence G(T) = diag(T^(wᵢ)√T) H(T) diag(T^(wᵢ)√T). The hypothesis requires this same G(T) to be positive definite for every positive T.

The theorem derives common positive c, C and δ such that every actual canonical decreasing eigenvalue₀ coordinate lies between c T^(2wᵢ+1) and C T^(2wᵢ+1) whenever 0 < T < δ. The coordinate is transported only through the standard Fin cardinal order isomorphism; no supplied eigenvalue list, permutation, eigengap or simple-spectrum premise is used.

In the displayed formula, λ(T,i) is notation for the same actual coordinate (hG(T,p)).isHermitian.eigenvalues₀ ((Fin.castOrderIso (Fintype.card_fin n)).symm i), where p is the displayed proof that T>0 and hG(T,p) is the positive-definiteness proof for the displayed congruence. In the formula, A denotes H₀ and d denotes δ. The convergence hypothesis is right-sided: H tends to H₀ along nhdsWithin(0, Ioi(0)).

The argument takes a genuine finite minimum of all positive H₀ principal determinants, obtains simultaneous local minor bounds from convergence, scales each actual principal minor, and uses monotone grades to compare every subset exponent with the initial prefix. The characteristic-polynomial coefficient/principal-minor identity and the actual Hermitian characteristic-polynomial identity identify coefficients with elementary symmetric sums of the same canonical spectrum. A zero-safe prefix-product sandwich and adjacent positive ratios finish the uniform powers.

The n = 0 branch, empty principal minor and empty prefix are retained; repeated grades and empty grade layers are allowed. This abstract interface does not construct the physical trajectory or moment Gramian, its orthonormal graded coordinates, determinant leading term, statistical risk, or the remaining original 5.2/5.3/6.2/6.3 clauses.

## References

- Truth anchor: `D5/S3/Observer/Linear/GradedCongruenceSpectrum.graded_congruence_spectrum`
