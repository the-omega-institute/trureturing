# Polar form of unit quaternions and de Moivre's formula

## Abstract

Every unit quaternion is cos t + sin t * n with t = arccos of its real part and n a unit imaginary quaternion, and powers of such quaternions obey de Moivre's formula.

**Theorem 1.1 (Polar form of a unit quaternion).**

$$\forall q \in \mathbb{H}[\mathbb{R}],\; \left\lVert q \right\rVert = 1 \Rightarrow \left(\exists n \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(n\right) = 0 \land \left(\left\lVert n \right\rVert = 1 \land q = \operatorname{cos}\left(\operatorname{arccos}\left(\operatorname{re}\left(q\right)\right)\right) + \operatorname{sin}\left(\operatorname{arccos}\left(\operatorname{re}\left(q\right)\right)\right) \cdot n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/UnitQuaternionPolar.exists_eq_cos_arccos_add_sin_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a quaternion of norm one and put t = arccos (re q). Since the squared norm of q is the sum of the squares of its four coordinates, the imaginary part of q has squared norm 1 - (re q)^2, so |re q| <= 1. Hence cos t = re q, and sin t = sqrt (1 - (re q)^2) is the norm of the imaginary part of q. If the imaginary part of q is nonzero, n is the imaginary part divided by its norm; it has real part zero and norm one, and q = re q + im q = cos t + sin t * n. If the imaginary part of q is zero, then sin t = 0 and q = cos t, and any unit imaginary quaternion, for instance the quaternion unit i, serves as n.

**Lemma 1.2 (De Moivre's formula for a unit imaginary quaternion).**

$$\forall n \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(n\right) = 0 \Rightarrow \left(\left\lVert n \right\rVert = 1 \Rightarrow \left(\forall t \in \mathbb{R},\; \forall k \in \mathbb{N},\; \left(\operatorname{cos}\left(t\right) + \operatorname{sin}\left(t\right) \cdot n\right)^{k} = \operatorname{cos}\left(k \cdot t\right) + \operatorname{sin}\left(k \cdot t\right) \cdot n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/UnitQuaternionPolar.cos_add_sin_smul_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be a quaternion with real part zero and norm one. A quaternion with real part zero squares to minus its squared norm, so n * n = -1. Hence there is a homomorphism of real algebras from the complex numbers to the quaternions that sends the imaginary unit i to n; it sends x + y i to x + y * n for real x and y. For every real angle t it sends exp (t i) = cos t + (sin t) i to cos t + sin t * n. For every natural number k, exp ((k * t) i) = exp (t i)^k, and the homomorphism preserves powers, so (cos t + sin t * n)^k is the image of exp ((k * t) i), which is cos (k * t) + sin (k * t) * n.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/UnitQuaternionPolar.cos_add_sin_smul_pow`
- Truth anchor: `D5/S3/Quantum/AURICOmega/UnitQuaternionPolar.exists_eq_cos_arccos_add_sin_smul`
