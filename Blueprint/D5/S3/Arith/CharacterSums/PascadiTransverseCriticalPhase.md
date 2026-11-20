# The Pascadi Transverse Critical Phase

## Abstract

The signed transverse phase over ZMod(p²) selects two stationary equations by exact upper-digit averaging.

**Theorem 1.1 (The two upper digits of the phase).**

$$\operatorname{Psi}\left(j, k\right) = Psi{1+p{jA-kB}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase.phase_add_digits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Work over ZMod(p²). For d,n indexed by three coordinates, take l_i = λ − d_i − α n_i and Ψ = (l_1 l_2 l_3)/λ, with λ and all three factors units. Replacing λ and α by λ + pj and α + pk multiplies Ψ by 1 + p(jA − kB). Here A = sum_i 1/l_i − 1/λ and B = sum_i n_i/l_i. The construction expands the three factors and the unit inverse exactly using p² = 0.

**Theorem 1.2 (The original signed reading has the prescribed square).**

$$\operatorname{Phi}\left(t\right)^2 = \frac{4Psi}{g\operatorname{s}\left(alpha\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase.signed_phase_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put u_i = l_3/l_i, S = sum_i u_i and s = s_0 + pα. Assume g s is a unit and λ sum_i 1/l_i = 1. If t² = S/(g s prod_i u_i), the signed reading Φ = t sum_i u_i(d_i + α n_i) squares to 4 Ψ/(g s). The proof uses sum_i u_i(d_i + α n_i) = −2l_3 and cancels the unit product.

**Theorem 1.3 (The root above each nonzero residue is unique).**

$$\operatorname{UnitRoot}\left(r\right) \implies \operatorname{UniqueLift}\left(r, j, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase.existsUnique_radical_root_of_reduce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an odd prime p, write R = 4 Ψ/(g s). A nonzero square root r of the reduction of R has a unique lift above r at every pair of upper digits j,k of λ,α on the unit chart. The proof corrects the square by the inverse of twice the root and uses p² = 0. Uniqueness follows because the sum of two roots above r is a unit.

**Theorem 1.4 (Exact orthogonality on a signed root fibre).**

$$\operatorname{CharacterFibre}\left(z\right) = \operatorname{IfStationary}\left(p^2, \operatorname{e}\left(z\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase.sum_radical_fibre` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be an odd prime and z be a unit square root of R in ZMod(p²). For every j,k in ZMod p, sum the prime-square additive character over roots above the residue of z of the radicand at λ + pj, α + pk. The resulting double sum equals p² e(z) when λ sum_i 1/l_i = 1 and sum_i n_i/l_i = 0 modulo p, and is zero otherwise.

The root computation gives the exact lift z + p(z/2)(jA − kB). The two characters in j and k are independently orthogonal by Mathlib. The unit multiplier z/2 allows the vanishing of the character coefficients to recover both stationary equations. Cancellation between distinct stationary phases in the literal short box remains open.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase.existsUnique_radical_root_of_reduce`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase.phase_add_digits`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase.signed_phase_sq`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase.sum_radical_fibre`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier](PascadiMixedQuotientFourier.md)
