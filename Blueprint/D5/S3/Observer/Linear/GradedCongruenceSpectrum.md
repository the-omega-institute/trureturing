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

For the observable Euclidean application with arbitrary d,p≥1 and observable matrices B,C, use the minimal layers, ordered subordinate orthonormal basis, weights w_i and fixed coordinates described in `D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian`. In that notation G_L(T)=Sᵀ G_standard(T) S, D(T)=diag(sqrt(T) T^(w_i)), H(T)=D(T)^(-1) G_L(T) D(T)^(-1), and H₀=M_L is the integral of P_L(s)ᵀ P_L(s) on [0,1] in the same basis. The norm estimate H(T)=M_L+O(T) supplies the right-sided convergence, M_L is positive definite, and the exact congruence D(T) H(T) D(T)=G_L(T) is positive definite for every T>0. Thus the abstract receiver applies to these actual objects.

There are common fixed positive c,C,δ such that, for every i<d and 0<T<δ, c T^(2w_i+1)≤λ_i(G_standard(T))≤C T^(2w_i+1). Here λ_i is the canonical decreasing eigenvalue₀ coordinate specified above, transported from G_L(T) by the orthogonal matrix S. For every 0≤j≤m, the set {i:w_i=j} has exactly d_j=dim E(j) elements, and precisely these sorted indices have the common bound Θ(T^(2j+1)). This accounts for all d indices, repeated weights and zero-dimensional groups, with constants independent of T and i. The physical realization and determinant coefficient come from the application in the native Gramian owner; the abstract theorem retains its stated hypotheses and conclusion.

## References

- Truth anchor: `D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian`
- Truth anchor: `D5/S3/Observer/Linear/GradedCongruenceSpectrum.graded_congruence_spectrum`
