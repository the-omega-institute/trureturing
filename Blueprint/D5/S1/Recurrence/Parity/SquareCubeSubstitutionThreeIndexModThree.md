# A389472 modulo three

## Abstract

The A389472 coefficients at indices 3n-1 are divisible by three for n greater than one.

The coefficient sequence a is the existing normalized integer sequence in SquareCubeSubstitutionOddIndexParity. It satisfies X^2(A+1)=A(X^2+X^3), with a(0)=0 and a(1)=a(2)=1. The index uses natural subtraction; n>1 ensures 3n-1 is positive. The independent odd-index parity theorem remains available from the same sequence owner.

**Definition 1.1 (Hanna's residue-class conjecture).**

$$(\operatorname{claim}) \iff (\forall n: \mathbb{N}, (1 < n) \implies ((3: \mathbb{Z}) \mid \operatorname{SquareCubeSubstitutionOddIndexParity}.\operatorname{a}\left(3 \cdot n - 1\right)))$$

*Formalization.* `D5/S1/Recurrence/Parity/SquareCubeSubstitutionThreeIndexModThree.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

OEIS A389472, COMMENTS (unpaginated): "Conjecture: a(3*n-1) = 0 (mod 3) for n > 1." The natural index n has its stated lower bound, divisibility is in the integers, and a is the sequence selected by the source expansion x+x^2+2*x^3+3*x^4+6*x^5+... .

**Theorem 1.2 (The modulo-three conjecture holds).**

$$\forall n: \mathbb{N}, (1 < n) \implies ((3: \mathbb{Z}) \mid \operatorname{SquareCubeSubstitutionOddIndexParity}.\operatorname{a}\left(3 \cdot n - 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/SquareCubeSubstitutionThreeIndexModThree.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

Lucas congruences annihilate summands whose upper binomial index is zero or one modulo three. Strong descent annihilates those with upper index two modulo three beyond the initial case; the remaining index two has a vanishing binomial coefficient. Every summand in the coefficient recurrence is divisible by three.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/SquareCubeSubstitutionThreeIndexModThree.claim`
- Truth anchor: `D5/S1/Recurrence/Parity/SquareCubeSubstitutionThreeIndexModThree.result`
- Dependency: [D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity](SquareCubeSubstitutionOddIndexParity.md)
