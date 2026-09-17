# OEIS A397356 Modulo Three

## Abstract

A coefficient of OEIS A397356 is nonzero modulo three exactly when twice its index plus two is a sum of two powers of three.

The integer sequence a is the coefficient sequence of generatingSeries in ReciprocalSquareExponentDiagonalParity. Its inverse has constant coefficient 1, linear coefficient -1, and equal coefficients at degree n in its powers n^2 and n^2-1 for every n>1. All indices and exponents below are natural numbers.

Over ZMod(3), let S have constant coefficient 1, coefficient -1 at each degree (3^j-1)/2 for j>0, and coefficient 0 elsewhere. The index shift gives S=1+X+X*S^3. Put Q=S^(-1). The reduction of generatingSeries is S^2.

**Theorem 1.1 (The reciprocal square diagonal).**

$$\forall S: \operatorname{PowerSeries}\left(\operatorname{ZMod}\left(3\right)\right), \forall Q: \operatorname{PowerSeries}\left(\operatorname{ZMod}\left(3\right)\right), (S = 1 + X + X * (S)^{3}) \implies ((S * Q = 1) \implies (\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{coeff}\left(n, ((Q)^{2})^{(n)^{2}}\right) = \operatorname{coeff}\left(n, ((Q)^{2})^{(n)^{2} - 1}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalModThree.inverse_cube_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any S and Q satisfying S=1+X+X*S^3 and S*Q=1, cube extraction gives coeff(3m,Q*F^3)=coeff(m,Q*F). Formal differentiation gives X*Q'=Q*(Q-1). Together these imply coeff(m,Q^(mt)*(1+Q))=0 for m>0 and t congruent to 1 modulo three, by induction stripping factors of three from m. Splitting n into its three residue classes proves the diagonal identity.

**Theorem 1.2 (Hanna's divisibility-by-three conjecture).**

$$\forall n: \mathbb{N}, \neg (3 \mid \operatorname{a}\left(n\right)) \iff (\exists u v: \mathbb{N}, 2 * (n + 1) = (3)^{u} + (3)^{v})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalModThree.a397356_mod_three` (`✓ std3`). ∎

*Citation.* Paul D. Hanna (2026). *OEIS A397356, reciprocal square-exponent diagonal generating series*. URL: <https://oeis.org/A397356>.

*Commentary.*

Uniqueness of the reciprocal diagonal equations identifies the reduction of reciprocalSeries with Q^2, so its inverse reduces to S^2. A sum of two powers of three determines the unordered pair of exponents: the sum is at least the largest summand and less than three times it. Thus the convolution has one nonzero summand for equal indices and two equal nonzero summands for distinct indices. Neither multiplicity vanishes modulo three. Exponent zero and equal exponents are both allowed.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalModThree.a397356_mod_three`
- Truth anchor: `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalModThree.inverse_cube_diagonal`
- Dependency: [D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity](ReciprocalSquareExponentDiagonalParity.md)
