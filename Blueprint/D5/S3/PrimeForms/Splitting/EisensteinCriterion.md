# The Discriminant Minus-Three Splitting Criterion

## Abstract

Minus three is a quadratic residue mod an odd prime p not 3 iff p is one mod three.

**Theorem 1.1 (Minus three is a residue mod p iff p is one mod three).**

$$\forall p \operatorname{prime}, p\neq 2, p\neq 3 \Rightarrow\\\operatorname{IsSquare}(-3 : ZMod p) \iff p \operatorname{mod} 3=1$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/EisensteinCriterion.neg_three_isSquare_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an odd prime p not equal to 3, the field element -3 in ZMod p is a quadratic residue — a square in ZMod p — if and only if p is congruent to 1 modulo 3. Since -3 is the discriminant of x^2 + x + 1, this being a square mod p is exactly the condition for p to split in the Eisenstein integers. Both p not 2 and p not 3 are required: -3 is congruent to 1 (a square) mod 2 yet 2 is not 1 mod 3, and -3 is congruent to 0 mod 3.

The proof runs through the Legendre symbol. Writing -3 as (-1) times 3, the -1 factor contributes the character chi-4 of p, equal to (-1) raised to p/2, and quadratic reciprocity between p and 3 cancels that sign, reducing the residue condition (-3 / p) = 1 to (p / 3) = 1. Casting p modulo 3 and splitting the two nonzero residues — 1 is a residue, 2 is a non-residue — finishes the proof.

Only this residue criterion — the central discriminant-minus-three clause — is recorded here. The dyadic 2-adic clause, that 3 k^2 + 1 is an Eisenstein norm for odd k, and the ladder-factory corollary of the wider result are not covered by this statement.

## References

- Truth anchor: `D5/S3/PrimeForms/Splitting/EisensteinCriterion.neg_three_isSquare_iff`
