# Invariant bilinear forms on the pure quaternions

## Abstract

Bilinear forms on the pure quaternions that are invariant under conjugation by unit quaternions: uniqueness up to a factor is equivalent to irreducibility, all conjugations together act irreducibly, and a single rotation through an angle outside the multiples of pi leaves exactly a three-parameter family invariant.

**Theorem 1.1 (Uniqueness of invariant forms is irreducibility).**

$$\forall S \in \operatorname{Set}\left(\operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)\right),\; \operatorname{TFAE}\left([\forall B \in \operatorname{LinearMap}\left(\mathbb{R}, \mathbb{H}[\mathbb{R}], \operatorname{LinearMap}\left(\mathbb{R}, \mathbb{H}[\mathbb{R}], \mathbb{R}\right)\right),\; \left(\forall u \in S,\; \forall x \in \mathbb{H}[\mathbb{R}], y \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(x\right) = 0 \Rightarrow \left(\operatorname{re}\left(y\right) = 0 \Rightarrow \operatorname{B}\left(u \cdot x \cdot \operatorname{star}\left(u\right), u \cdot y \cdot \operatorname{star}\left(u\right)\right) = \operatorname{B}\left(x, y\right)\right)\right) \Rightarrow \left(\exists c \in \mathbb{R},\; \forall x \in \mathbb{H}[\mathbb{R}], y \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(x\right) = 0 \Rightarrow \left(\operatorname{re}\left(y\right) = 0 \Rightarrow \operatorname{B}\left(x, y\right) = c \cdot \langle x, y \rangle\right)\right), \forall B \in \operatorname{LinearMap}\left(\mathbb{R}, \mathbb{H}[\mathbb{R}], \operatorname{LinearMap}\left(\mathbb{R}, \mathbb{H}[\mathbb{R}], \mathbb{R}\right)\right),\; \left(\forall x \in \mathbb{H}[\mathbb{R}], y \in \mathbb{H}[\mathbb{R}],\; \operatorname{B}\left(x, y\right) = \operatorname{B}\left(y, x\right)\right) \Rightarrow \left(\left(\forall u \in S,\; \forall x \in \mathbb{H}[\mathbb{R}], y \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(x\right) = 0 \Rightarrow \left(\operatorname{re}\left(y\right) = 0 \Rightarrow \operatorname{B}\left(u \cdot x \cdot \operatorname{star}\left(u\right), u \cdot y \cdot \operatorname{star}\left(u\right)\right) = \operatorname{B}\left(x, y\right)\right)\right) \Rightarrow \left(\exists c \in \mathbb{R},\; \forall x \in \mathbb{H}[\mathbb{R}], y \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(x\right) = 0 \Rightarrow \left(\operatorname{re}\left(y\right) = 0 \Rightarrow \operatorname{B}\left(x, y\right) = c \cdot \langle x, y \rangle\right)\right)\right), \forall W \in \operatorname{Submodule}\left(\mathbb{R}, \mathbb{H}[\mathbb{R}]\right),\; \left(\forall v \in W,\; \operatorname{re}\left(v\right) = 0\right) \Rightarrow \left(\left(\forall u \in S,\; \forall v \in W,\; u \cdot v \cdot \operatorname{star}\left(u\right) \in W\right) \Rightarrow \left(W = \perp \lor \left(\forall x \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(x\right) = 0 \Rightarrow x \in W\right)\right)\right)]\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TangentInvariantForms.invariant_bilinear_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a set of unit quaternions, and let a unit quaternion u act on the pure quaternions, those x with re(x) = 0, by the conjugation x -> u x star(u), a rotation of this three-dimensional real space. A real bilinear form B on the quaternions is called invariant on the pure quaternions when B(u x star(u), u y star(u)) = B(x, y) for all u in S and all pure x, y. The theorem states that the following three conditions are equivalent: (1) every invariant bilinear form is, on the pure quaternions, a real multiple c <x, y> of the inner product; (2) the same holds for every invariant symmetric bilinear form; (3) every subspace W of the quaternions that consists of pure quaternions and is mapped into itself by the conjugations by S is either zero or contains every pure quaternion. In the display <x, y> is the real inner product of the quaternions and TFAE states that the listed propositions are pairwise equivalent; nothing is assumed of S.

(1) implies (2) trivially. (3) implies (1): on the pure quaternions B(x, y) = <A x, y> for a linear map A of the pure quaternions into themselves, and invariance means that A commutes with every conjugation by S. The pure quaternions have dimension three, which is odd, so A has a real eigenvalue c; its eigenspace is invariant and nonzero, so by (3) it contains every pure quaternion, and then B(x, y) = c <x, y> there. (2) implies (3): the orthogonal projection P onto an invariant subspace W commutes with the conjugations, so <P x, y> is an invariant symmetric form; by (2) it equals c <x, y> on the pure quaternions, and evaluating at a nonzero vector of W gives c = 1, so W contains every pure quaternion. This is Schur's lemma for real representations, in the classical form that an irreducible real representation of odd dimension is of real type: its commuting operators are real scalars. The eigenvalue in odd dimension comes from the odd-degree root theorem for the real numbers.

**Theorem 1.2 (Forms invariant under all conjugations).**

$$\forall B \in \operatorname{LinearMap}\left(\mathbb{R}, \mathbb{H}[\mathbb{R}], \operatorname{LinearMap}\left(\mathbb{R}, \mathbb{H}[\mathbb{R}], \mathbb{R}\right)\right),\; \left(\forall u \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \forall x \in \mathbb{H}[\mathbb{R}], y \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(x\right) = 0 \Rightarrow \left(\operatorname{re}\left(y\right) = 0 \Rightarrow \operatorname{B}\left(u \cdot x \cdot \operatorname{star}\left(u\right), u \cdot y \cdot \operatorname{star}\left(u\right)\right) = \operatorname{B}\left(x, y\right)\right)\right) \Rightarrow \left(\exists c \in \mathbb{R},\; \forall x \in \mathbb{H}[\mathbb{R}], y \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(x\right) = 0 \Rightarrow \left(\operatorname{re}\left(y\right) = 0 \Rightarrow \operatorname{B}\left(x, y\right) = c \cdot \langle x, y \rangle\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TangentInvariantForms.conj_invariant_bilinear_eq_smul_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real bilinear form B on the quaternions that is invariant on the pure quaternions under the conjugation by every unit quaternion is, on the pure quaternions, a real multiple c <x, y> of the inner product.

This is condition (1) of the preceding equivalence for the set of all unit quaternions, and condition (3) holds for that set: a nonzero invariant subspace W contains a nonzero pure quaternion w, any two unit quaternions with the same real part are conjugate, so w / |w| is conjugate to x / |x| for every nonzero pure quaternion x, and x is then a real multiple of a conjugate of w, which lies in W. The full conjugation group is the rotation group of the three-dimensional space of pure quaternions.

**Theorem 1.3 (Forms invariant under one rotation).**

$$\forall u \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{re}\left(u\right) \ne 0 \Rightarrow \left(\operatorname{im}\left(u\right) \ne 0 \Rightarrow \left(\forall B \in \operatorname{LinearMap}\left(\mathbb{R}, \mathbb{H}[\mathbb{R}], \operatorname{LinearMap}\left(\mathbb{R}, \mathbb{H}[\mathbb{R}], \mathbb{R}\right)\right),\; \left(\forall x \in \mathbb{H}[\mathbb{R}], y \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(x\right) = 0 \Rightarrow \left(\operatorname{re}\left(y\right) = 0 \Rightarrow \operatorname{B}\left(u \cdot x \cdot \operatorname{star}\left(u\right), u \cdot y \cdot \operatorname{star}\left(u\right)\right) = \operatorname{B}\left(x, y\right)\right)\right) \Leftrightarrow \left(\exists a \in \mathbb{R}, b \in \mathbb{R}, c \in \mathbb{R},\; \forall x \in \mathbb{H}[\mathbb{R}], y \in \mathbb{H}[\mathbb{R}],\; \operatorname{re}\left(x\right) = 0 \Rightarrow \left(\operatorname{re}\left(y\right) = 0 \Rightarrow \operatorname{B}\left(x, y\right) = a \cdot \langle x, y \rangle + b \cdot \langle \operatorname{im}\left(u\right), x \rangle \cdot \langle \operatorname{im}\left(u\right), y \rangle + c \cdot \langle \operatorname{im}\left(u\right), x \cdot y \rangle\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TangentInvariantForms.conj_invariant_bilinear_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u be a unit quaternion with re(u) nonzero and im(u) nonzero, and write n = im(u). A real bilinear form B on the quaternions is invariant on the pure quaternions under the conjugation by u if and only if there are real numbers a, b, c with B(x, y) = a <x, y> + b <n, x> <n, y> + c <n, x y> for all pure x, y. The coefficients alpha, beta, gamma of the Lean statement are written a, b, c in the display. For pure x and y one has x y = -<x, y> + x cross y, so <n, x y> = <n, x cross y>; the third form is the triple product with n and is antisymmetric, and the invariant symmetric forms are exactly those with c = 0, a two-dimensional family.

The conjugation by u = cos t + sin t m, with m a unit pure quaternion, is the rotation about the axis m through the angle 2t, and the hypotheses say that 2t is not a multiple of pi. Each of the three forms is invariant because u commutes with n. Conversely, a unit quaternion q carrying i to n / |n| reduces the problem to the axis i, where the invariance equations on the basis i, j, k force the matrix of the form on the pure quaternions to commute with a rotation through an angle outside the multiples of pi about i; such matrices are spanned by the identity, the projection onto i and the cross product with i, because the rotation has the distinct eigenvalues 1, e^(2it) and e^(-2it). Both hypotheses are needed; the following counts were obtained numerically and are not formalized. When re(u) = 0 the conjugation is a half-turn, and its invariant bilinear forms on the pure quaternions form a five-dimensional space. When im(u) = 0, that is u = 1 or u = -1, the conjugation is the identity and all bilinear forms, a nine-dimensional space, are invariant. The classification is an instance of the classical description of the commutant of a rotation in three dimensions.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/TangentInvariantForms.conj_invariant_bilinear_eq_smul_inner`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TangentInvariantForms.conj_invariant_bilinear_iff`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TangentInvariantForms.invariant_bilinear_tfae`
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/IsRealClosed/Real](../../Geometry/AlgebraicBoundary/TauCeti/FieldTheory/IsRealClosed/Real.md)
- Dependency: [D5/S3/QuadraticForms/OddDimensionZeroDivisor](../../QuadraticForms/OddDimensionZeroDivisor.md)
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity](QuaternionTwoPointHomogeneity.md)
