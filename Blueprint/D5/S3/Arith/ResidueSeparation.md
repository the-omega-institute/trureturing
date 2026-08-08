# Separation of Distinct Naturals by a Sufficiently Large Modular Reading

## Abstract

A modulus above both operands makes the modular reading separate distinct naturals.

**Theorem 1.1 (A modulus above both operands separates distinct residues).**

$$\forall m,n,M\in\mathbb{N},\ m \neq n \land \max(m,n) < M \Rightarrow (m \operatorname{mod} M) \neq (n \operatorname{mod} M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ResidueSeparation.residue_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The modular reading of a natural number at a modulus M is its remainder on division by M, and the theorem asks when this reading distinguishes two operands. It fixes natural numbers m and n that are genuinely distinct and a modulus M lying strictly above both, expressed as the single hypothesis that the larger of m and n is still smaller than M, and concludes that the two readings differ. The hypotheses are not vacuous: the inequality on the maximum is a real constraint relating the modulus to both operands at once, and the distinctness of m and n is the genuine premise the separation converts into distinctness of the readings. Strictness is essential rather than cosmetic, for a modulus equal to the larger operand would wrap that operand down to a smaller residue and could collapse the two readings together.

The proof reads the hypothesis on the maximum as the conjunction of two separate bounds, one placing m below M and the other placing n below M. Each bound puts its operand inside the canonical residue range from zero up to but excluding M, where the remainder map acts as the identity and returns the operand unchanged. The two readings therefore equal the operands themselves, and their inequality is exactly the given distinctness of m and n transported across the two identities. The argument is purely arithmetic and logical: it invokes only the identity behaviour of the remainder on its canonical range and asserts no numerical certificate.

## References

- Truth anchor: `D5/S3/Arith/ResidueSeparation.residue_separation`
