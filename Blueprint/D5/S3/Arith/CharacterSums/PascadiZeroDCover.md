# Sixth-height root-relevant cover of a zero Dixon family

## Abstract

All singular nonzero-reduction pencils in a zero Dixon family have a finite root-relevant factor cover at sixth height. Localization identifies the factors relevant to the common modular root before the finite cover is selected.

**Theorem 1.1 (At most three primitive irreducible factors cover every actual pencil).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiZeroDCover.actual_zero_dixon_singular_factor_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiZeroDCover.actual_zero_dixon_singular_factor_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take an arbitrary indexed family with a distinguished baseline and a chosen member i0. The actual pencils are Pi=L0*Qi-Li*Q0, with all rows satisfying |li|≤3I, |mi|≤3J, |qi|≤I², |ri|≤2IJ, |si|≤J² and I≥J≥1. Let H≥1 bound each coefficient by H*I^(3−j)*J^j up to the original degree, which is at most three. Assume p prime, a common integer b, nonzero reductions of all Pi modulo p, p³ dividing all Pi(b), p dividing all derivatives Pi′(b), and L0(b) a unit modulo p. Assume the actual residual of every triple (baseline,i,j) is zero. If max(6804,24*(8H)⁴)*(IJ)⁶<p⁵, there is a finite set F of at most three primitive irreducible integer polynomials. Each f in F divides the chosen Pi0, vanishes at b modulo p, and has nonzero reduction modulo p; every Pi is divisible by some f in F.

The existing localized_factor_cube decomposition writes Pi=Ri*Ui, where Ri is primitive of degree two or three, Ui(b) is a modular unit, all irreducible factors of Ri vanish at the modular root, and Ri retains the prime-cube value and derivative divisibilities. If a localized factor has degree three, its complement is constant and the actual Dixon resultant identity transfers a common factor to the other localized polynomial: that factor cannot divide a complement whose value is a unit. If both localized factors are quadratic and one original is cubic, the mixed cubic-quadratic height estimate bounds their fifth-power-divisible resultant by 24*(8H)⁴*(IJ)⁶. If both originals are quadratic, zero_dixon_quadratic_resultant_zero supplies the finite-root resultant, followed by the same constant-complement transfer. Pairwise common factors of the localized polynomials therefore yield a cover by the at most three irreducible factors of one reference Ri0. Their relevance follows from localization, not from an unqualified common-factor assertion.

The finite factor lifting and complement transfer reuse the actual singular-pencil cover. Zero baseline resultant, zero baseline leading pair, low row rank and linear-projection rank at most one are included: no nonalignment or rank premise appears. The result is a conditional algebraic cover and does not itself assert a total prime-cube counting exponent or settle the arbitrary-modulus conjecture.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiZeroDCover.actual_zero_dixon_singular_factor_cover`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiZeroDQuadratic](PascadiZeroDQuadratic.md)
