# Actual singular partners under seventh height

## Abstract

Actual nonzero-reduction, derivative-zero partners of the original prime-cube word satisfy the physical subpower bound under one structural seventh-height condition. The proof combines the actual root-relevant factor cover with the enlarged field-uniform value estimate, while preserving the original lattice, unit, separate-width and endpoint hypotheses.

Write K7=seventhHeightConstant=max(10368·3^9, max(14256, 24·(8·18)^4)).

**Theorem 1.1 (The original physical partner bound with seventh height).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiSeventhSingularCount.actual_nonzero_singular_partners_seventh`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiSeventhSingularCount.actual_nonzero_singular_partners_seventh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0 there is C>0 chosen before prime p, the widths, bases, baseline and finite set S. Let B be an actual basis of the index-p^3 middle congruence lattice and B2 a reduced basis of its index-p^2 counterpart. Assume X,Y,H>0, H^2=XY, separate widths 2X<p^3 and 2Y<p^3, anchor physical(B,q)=(-w,-t), unit t,w and B.R.1, and 1<=J2<=J1. The anchor, baseline and all partner coordinates obey their literal J1,J2 bounds. The baseline and every partner satisfy the actual original six-return word; the baseline physical first coordinates and original hyperbola right side are units. Both physical endpoints of every partner lie in the literal X,Y box. Every pencil has nonzero reduction modulo p and derivative zero at the genuine reduced beta=V.1/R.1. If K7*(J1*J2)^7<p^5, then card(S)<=C*p^epsilon*(1+6H/(p*sigma)), where sigma=sqrt(weightedSq X Y B2.R).

Realize the literal endpoint coefficients and transfer the genuine word root to integer p^3 divisibility. The structural seventh-height theorem gives at most three primitive irreducible root-relevant factors of one actual pencil. Seventh height supplies J1<=p, and the enlarged value envelope counts the actual algebraic value pairs uniformly in their number fields. The existing physical factor-partner theorem pays the fiber weight once; summing over at most three factors gives the displayed C. The actual physical reconstruction and factor-partner argument are reused from PascadiOriginalSingularCount, while the new structural cover and enlarged value envelope supply the stronger range.

This counts the specified nonzero singular partner stratum. It does not remove the zero-reduction branch, the other tuple charts, the separate physical width conditions, or the need to assemble a final original-tuple estimate. The source problem is Pascadi's six-letter conjecture; neither an arbitrary-modulus solution nor external author acceptance is asserted.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSeventhSingularCount.actual_nonzero_singular_partners_seventh`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalSingularCount](PascadiOriginalSingularCount.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiSeventhHeightCover](PascadiSeventhHeightCover.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiSeventhHeightRange](PascadiSeventhHeightRange.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiSingularValueEnvelope](PascadiSingularValueEnvelope.md)
