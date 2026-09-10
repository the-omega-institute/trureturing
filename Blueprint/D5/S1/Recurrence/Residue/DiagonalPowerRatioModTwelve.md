# Diagonal Power Ratios Modulo Twelve

## Abstract

The coefficients of OEIS A397241 are congruent to 11 modulo 12 above degree two.

The two conjectures are recorded in hanna2026a397241b. The symbols a and A denote the existing coefficient function a and generatingSeries in DiagonalPowerRatioAllOdd. That module proves generating_equation and generating_unique for the normalized integer series. No new coefficient sequence is introduced here. All indices and exponents are natural numbers; the values a(n) and their remainders are integers.

The operator mk forms a power series from a coefficient function. The operator map applies a ring homomorphism coefficientwise, and intCast(ZMod(m)) denotes Int.castRingHom(ZMod(m)). In each series identity, both sides are over ZMod(m), X is its formal series variable, and the constant function passed to mk takes value one in that ring.

**Theorem 1.1 (The generating series modulo three).**

$$\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(3\right)\right), A\right) = (1 - 2 \cdot X^{3}) \cdot \operatorname{mk}\left((k: \mathbb{N} \mapsto 1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.mod_three_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put G=mk(1) and B=(1-2X^3)G. In ZMod(3), B^3 is B expanded at X^3. Extraction of coefficients in the three residue classes reduces the diagonal equation residual to H(n), the degree-n coefficient of (1+X)G B^n. The recurrence is H(3n)=H(n), while H(3n+1) and H(3n+2) are zero. Strong induction gives H(n)=0 for positive n. Thus B satisfies the reduced equation. The leading-coefficient comparison has multiplier n^2-(n-1)(n+1)=1, so it identifies B with the reduction of A.

**Theorem 1.2 (The generating series modulo four).**

$$\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(4\right)\right), A\right) = (1 - 2 \cdot X^{3}) \cdot \operatorname{mk}\left((k: \mathbb{N} \mapsto 1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.mod_four_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same G and B in ZMod(4), set E=2(XG+X^6). Then E^2=2E=0 and B^2 is B expanded at X^2, multiplied by 1+E. A polynomial numerator pair P,Q therefore represents the degree-n coefficient of (P+nQ)G^2 B^n. Clearing denominators to G^4 gives five pairs closed under even and odd coefficient extraction. Their symbolic transitions and strong induction show that the initial residual vanishes for every n greater than one. The multiplier-one comparison again identifies B with the reduction of A.

**Theorem 1.3 (The common remainder modulo twelve).**

$$\forall n: \mathbb{N}, (2 < n) \implies (\operatorname{a}\left(n\right) \bmod 12 = 11)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.hanna_conjecture_mod_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In both series identities the coefficients above degree two equal minus one. Their integer remainders are therefore two modulo three and three modulo four. These two remainder equations force the remainder eleven modulo twelve.

**Theorem 1.4 (Hanna's conjecture modulo three).**

$$\forall n: \mathbb{N}, (2 < n) \implies (\operatorname{a}\left(n\right) \bmod 3 = 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.hanna_conjecture_mod_three` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397241-mod-three` (proved) by `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.hanna_conjecture_mod_three`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397241-mod-three","declaration_gid":"D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.hanna_conjecture_mod_three","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397241, g.f. with n [x^n] A^n = (n-1) [x^n] A^(n+1)*. URL: <https://oeis.org/A397241>.

*Commentary.*

Reducing the common remainder eleven modulo three gives two, for every natural index n greater than two.

**Theorem 1.5 (Hanna's conjecture modulo four).**

$$\forall n: \mathbb{N}, (2 < n) \implies (\operatorname{a}\left(n\right) \bmod 4 = 3)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.hanna_conjecture_mod_four` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397241-mod-four` (proved) by `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.hanna_conjecture_mod_four`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397241-mod-four","declaration_gid":"D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.hanna_conjecture_mod_four","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397241, g.f. with n [x^n] A^n = (n-1) [x^n] A^(n+1)*. URL: <https://oeis.org/A397241>.

*Commentary.*

Reducing the common remainder eleven modulo four gives three, for every natural index n greater than two.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.hanna_conjecture_mod_four`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.hanna_conjecture_mod_three`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.hanna_conjecture_mod_twelve`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.mod_four_identity`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.mod_three_identity`
- Dependency: [D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd](DiagonalPowerRatioAllOdd.md)
