# Signed projective overlap and antipodal closure

## Abstract

Signed projective overlap and the rational Cayley circle for Chapter 32, sections 32.7 and 32.8.

**Theorem 1.1 (Nonzero signed scales preserve overlap).**

$$\forall p \in \mathbb{Z}, q \in \mathbb{Z}, k \in \mathbb{Z},\; k \ne 0 \Rightarrow \operatorname{Equivalent}\left(\operatorname{kappa}\left(k \cdot p, k \cdot q\right), \operatorname{kappa}\left(p, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCircleClosure.kappa_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The overlap is q squared divided by p squared plus q squared. The common scale contributes the same positive square to numerator and denominator. At the zero pair both readings are undefined and equivalent.

**Theorem 1.2 (Overlap and spread sum to one).**

$$\forall p \in \mathbb{Z}, q \in \mathbb{Z},\; \left(p \ne 0 \lor q \ne 0\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{kappa}\left(p, q\right) + \operatorname{spread}\left(p, q\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCircleClosure.kappa_add_spread_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Spread has numerator p squared and the same denominator as overlap. The nonzero-pair hypothesis keeps that denominator positive.

**Theorem 1.3 (The rational Cayley image has unit norm).**

$$\forall p \in \mathbb{Z}, q \in \mathbb{Z},\; \left(p \ne 0 \lor q \ne 0\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{X}\left(p, q\right) \cdot \operatorname{X}\left(p, q\right) + \operatorname{Y}\left(p, q\right) \cdot \operatorname{Y}\left(p, q\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCircleClosure.cayley_circle_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Cayley coordinates X and Y have numerators q squared minus p squared and twice p times q, respectively. Both use the denominator p squared plus q squared. The squared norm of the numerator pair is the square of this denominator.

**Theorem 1.4 (The point at infinity maps to the antipode).**

$$\forall p \in \mathbb{Z},\; p \ne 0 \Rightarrow \left(\operatorname{Equivalent}\left(\operatorname{kappa}\left(p, 0\right), 0\right) \land \left(\operatorname{Equivalent}\left(\operatorname{spread}\left(p, 0\right), 1\right) \land \left(\operatorname{Equivalent}\left(\operatorname{X}\left(p, 0\right), -1\right) \land \operatorname{Equivalent}\left(\operatorname{Y}\left(p, 0\right), 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCircleClosure.cayley_antipodal_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When q vanishes and p is nonzero, the denominator is p squared. This gives overlap zero, spread one and the finite Cayley image at the antipode.

**Theorem 1.5 (Homogeneous multiplication multiplies squared norms).**

$$\forall p \in \mathbb{Z}, q \in \mathbb{Z}, r \in \mathbb{Z}, s \in \mathbb{Z},\; \operatorname{normSq}\left(p, q\right) \cdot \operatorname{normSq}\left(r, s\right) = \operatorname{normSq}\left(\operatorname{projectiveMul}\left(p, q, r, s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCircleClosure.projective_circle_mul_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here normSq is the sum of the two coordinate squares. The product of (p,q) and (r,s) has coordinates ps+qr and qs-pr. Its mixed terms cancel in the sum of squares. The identity also holds for zero pairs.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCircleClosure.cayley_antipodal_closure`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCircleClosure.cayley_circle_unit`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCircleClosure.kappa_add_spread_eq_one`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCircleClosure.kappa_scale`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCircleClosure.projective_circle_mul_normSq`
