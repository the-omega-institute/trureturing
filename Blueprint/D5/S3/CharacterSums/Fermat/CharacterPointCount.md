# Fermat Point Counts from Multiplicative Characters

## Abstract

Multiplicative characters count actual affine and projective Fermat points over every finite field, with the zero-fiber correction and the Weil error bound.

**Theorem 1.1 (Character kernel is the power image).**

$$\forall F, \operatorname{FiniteField}\left(F\right), \forall chi: \operatorname{MulChar}\left(F, C\right), \forall d: N, \operatorname{orderOf}\left(chi\right)=d \implies \operatorname{ker}\left(\operatorname{toUnitHom}\left(chi\right)\right)=\operatorname{range}\left(\operatorname{powerHom}\left(d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/Fermat/CharacterPointCount.character_kernel_eq_power_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a finite field and let chi be a complex multiplicative character of exact order d. Evaluation on a generator of the cyclic unit group embeds the character group into the complex units. The value of chi on that generator has order d, so its kernel consists exactly of d-th powers. This supplies the existence part of the root-count identity below.

**Theorem 1.2 (Root counting includes the zero fiber).**

$$\forall F, \operatorname{FiniteField}\left(F\right), \forall chi: \operatorname{MulChar}\left(F, C\right), \forall d: N, \operatorname{orderOf}\left(chi\right)=d \implies 0<d \implies \forall a: F, \operatorname{card}\left(\operatorname{powerFiber}\left(a, d\right)\right)=\operatorname{deltaZero}\left(a\right)+\sum_{0\leq i<d} \operatorname{apply}\left(\operatorname{pow}\left(chi, i\right), a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/Fermat/CharacterPointCount.power_fiber_card_eq_character_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume d is positive. A nonzero d-th power has d roots because every nonempty power fiber is equivalent to the kernel of the power homomorphism. Non-powers have no roots, and zero has exactly one root. A finite geometric sum of character powers recovers the nonzero count. Mathlib extends even the trivial multiplicative character by zero at zero, so the separate delta term is essential. The equivalent one-plus-nontrivial-characters form is used on the live path to affine counting.

**Theorem 1.3 (Affine Fermat points are a double Jacobi sum).**

$$\forall F, \operatorname{FiniteField}\left(F\right), \forall chi: \operatorname{MulChar}\left(F, C\right), \forall d: N, \operatorname{orderOf}\left(chi\right)=d \implies 0<d \implies \operatorname{card}\left(\operatorname{affinePoints}\left(F, d\right)\right)=\operatorname{card}\left(F\right)+\sum_{1\leq i<d} \sum_{1\leq j<d} \operatorname{J}\left(\operatorname{pow}\left(chi, i\right), \operatorname{pow}\left(chi, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/Fermat/CharacterPointCount.affine_point_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine carrier is the actual subtype of pairs satisfying x^d + y^d = 1. The Jacobi sum is J(alpha,beta) = sum over t in F of alpha(t) beta(1-t). Record t = x^d to obtain a genuine equivalence with the sum of two-root fibers. Insert the root-count identity and expand. Both linear terms vanish by nontrivial-character orthogonality, including after the bijection t maps to 1-t. The remaining mixed terms are exactly the Jacobi sums.

**Theorem 1.4 (Actual projective points split into two charts).**

$$\forall F, \operatorname{FiniteField}\left(F\right), \forall d: N, d\neq0 \implies \operatorname{card}\left(\operatorname{projectivePoints}\left(F, d\right)\right)=\operatorname{card}\left(\operatorname{affinePoints}\left(F, d\right)\right)+\operatorname{card}\left(\operatorname{infinityPoints}\left(F, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/Fermat/CharacterPointCount.projective_card_eq_affine_add_infinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projective points are a subtype of Mathlib's projectivization of the three-dimensional coordinate space. The equation is homogeneous, so membership is independent of the chosen representative. A point with nonzero last coordinate normalizes uniquely to [x:y:1]. At infinity, the equation and nonzero representative force the middle coordinate to be nonzero, giving the unique form [t:1:0] with t^d + 1 = 0. The proof constructs a bijection from these two charts to the genuine projective subtype. The hypothesis d is nonzero is required at infinity.

**Theorem 1.5 (The infinity chart cancels the inverse-character pairs).**

$$\forall F, \operatorname{FiniteField}\left(F\right), \forall chi: \operatorname{MulChar}\left(F, C\right), \forall d: N, \operatorname{orderOf}\left(chi\right)=d \implies 0<d \implies \operatorname{card}\left(\operatorname{projectivePoints}\left(F, d\right)\right)=\operatorname{card}\left(F\right)+1+\sum_{1\leq i<d} \sum_{1\leq j<d, j\neq d-i} \operatorname{J}\left(\operatorname{pow}\left(chi, i\right), \operatorname{pow}\left(chi, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/Fermat/CharacterPointCount.projective_point_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The infinity count is the root count at -1. For each nontrivial exponent i, the exponent d-i gives the inverse character, and its Jacobi sum equals minus chi^i(-1). These terms cancel the nonconstant infinity contribution. The remaining sum omits exactly one term from each row. This statement counts actual projective points and applies also in characteristic two.

**Theorem 1.6 (Weil error for the Fermat point count).**

$$\forall F, \operatorname{FiniteField}\left(F\right), \forall d: N, 2\leq d, \operatorname{divides}\left(d, \operatorname{card}\left(F\right)-1\right) \implies \left\lVert \operatorname{card}\left(\operatorname{projectivePoints}\left(F, d\right)\right)-(\operatorname{card}\left(F\right)+1) \right\rVert\leq(d-1)(d-2)\operatorname{sqrt}\left(\operatorname{card}\left(F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/Fermat/CharacterPointCount.projective_weil_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume d is at least two and divides Q-1. The proof constructs a complex multiplicative character of exact order d from a primitive complex d-th root of unity. Both characters and their product are nontrivial for every remaining pair. The standard Jacobi-sum product identity with the inverse characters, together with complex conjugation, gives norm sqrt(Q). There are exactly (d-1)(d-2) remaining pairs. The triangle inequality and the bound of the real part by the complex norm give the claimed error for Q = card(F).

These are classical finite-field character-sum results, with no mathematical novelty claim. The library contribution connects unit-group characters and Jacobi sums to the actual affine and projective carriers and their cardinalities. The exact identities take an exact-order character as input, while the final bound constructs it from divisibility.

For d = 3 the remaining exponent pairs are (1,1) and (2,2), and their Jacobi sums are complex conjugates. Thus the formula gives Q + 1 + 2 Re J(chi,chi) and an error at most 2 sqrt(Q). CubicJacobiNormalization proves J(chi,chi) = -pi for the Euler character at the specified Eisenstein prime. CubicFermatTrace transports that same character through a concrete complex embedding to obtain q + 1 - Tr(pi) for actual projective points over finite Eisenstein residue fields. The prime-period theory retains its rational-prime data; other finite-field extensions require a separate Jacobi normalization theorem.

## References

- Truth anchor: `D5/S3/CharacterSums/Fermat/CharacterPointCount.affine_point_count`
- Truth anchor: `D5/S3/CharacterSums/Fermat/CharacterPointCount.character_kernel_eq_power_image`
- Truth anchor: `D5/S3/CharacterSums/Fermat/CharacterPointCount.power_fiber_card_eq_character_sum`
- Truth anchor: `D5/S3/CharacterSums/Fermat/CharacterPointCount.projective_card_eq_affine_add_infinity`
- Truth anchor: `D5/S3/CharacterSums/Fermat/CharacterPointCount.projective_point_count`
- Truth anchor: `D5/S3/CharacterSums/Fermat/CharacterPointCount.projective_weil_bound`
