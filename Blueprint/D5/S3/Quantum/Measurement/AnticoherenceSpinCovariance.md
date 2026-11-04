# Spin covariance and Dicke coordinates

## Abstract

Orthogonal Pauli rotations act on collective spins and their quadratic products.

**Theorem 1.1 (Pauli conjugation gives an orthogonal matrix).**

$$\forall \left(u: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.specialUnitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\exists \left(r: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\left(\left(\operatorname{Matrix.transpose}\left(r\right)\right) \cdot \left(r\right) = 1\right) \land \left(\forall \left(a: \operatorname{Fin}\left(3\right)\right), \left(\left(\left(\operatorname{Subtype.val}\left(u\right)\right) \cdot \left(\operatorname{pauli}\left(a\right)\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(\operatorname{Subtype.val}\left(u\right)\right)\right) = \left(\sum \left(c: \operatorname{Fin}\left(3\right)\right), \left(\operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(r\left(a, c\right)\right), \operatorname{pauli}\left(c\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.pauli_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by a special unitary qubit matrix preserves the real space of traceless Hermitian matrices. Expand each conjugated Pauli matrix in the Pauli basis, with coefficient one half of the real part of its trace product with the corresponding Pauli matrix. Preservation of these trace products gives r times its transpose equal to the identity, hence also its transpose times r equal to the identity. The assertion requires orthogonality; it does not assert a determinant condition.

**Theorem 1.2 (An orthogonal change of a sandwich family).**

$$\forall \left(k: \operatorname{Type}*\right), \left(\forall \left(n: \operatorname{Type}*\right), \left([\operatorname{Fintype}\left(k\right)], [\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(k\right)], \left(\forall \left(q: \operatorname{Matrix}\left(k, k, \mathbb{C}\right)\right), \left(\left(\left(\operatorname{Matrix.transpose}\left(q\right)\right) \cdot \left(q\right) = 1\right) \to \left(\forall \left(s: \left(k\right) \to \left(\operatorname{Matrix}\left(n, n, \mathbb{C}\right)\right)\right), \left(\forall \left(x: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)\right), \left(\left(\sum \left(a: k\right), \left(\left(\left(\left(\sum \left(c: k\right), \left(\operatorname{HSMul.hSMul}\left(q\left(a, c\right), s\left(c\right)\right)\right)\right)\right) \cdot \left(x\right)\right) \cdot \left(\left(\sum \left(e: k\right), \left(\operatorname{HSMul.hSMul}\left(q\left(a, e\right), s\left(e\right)\right)\right)\right)\right)\right)\right) = \left(\sum \left(c: k\right), \left(\left(\left(s\left(c\right)\right) \cdot \left(x\right)\right) \cdot \left(s\left(c\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.orthogonal_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex matrix q satisfying q transpose times q equal to the identity, replacing each member of a matrix family s by its q-linear combination leaves the sum of s c times x times s c unchanged. Expand both combinations and contract the two q coefficients by column orthogonality. This is a bilinear identity: the hypothesis uses transpose, and neither occurrence of s c is conjugate-transposed.

**Theorem 1.3 (A tensor power is unitary).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(u: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.specialUnitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{Matrix.conjTranspose}\left(\operatorname{tensorOp}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Subtype.val}\left(u\right)\right)\right)\right)\right) \cdot \left(\operatorname{tensorOp}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Subtype.val}\left(u\right)\right)\right)\right) = 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.tensor_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tensor product of n copies of a special unitary qubit matrix is unitary. The constant family has domain Fin n, including the empty tensor product at n equal to zero.

**Theorem 1.4 (A local matrix changes one coordinate).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(k: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(a: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\forall \left(f: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \to \left(\mathbb{C}\right)\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right), \left(\operatorname{Matrix.mulVec}\left(\operatorname{localOp}\left(k, a\right), f\right)\left(x\right) = \left(\sum \left(b: \operatorname{Fin}\left(2\right)\right), \left(\left(a\left(x\left(k\right), b\right)\right) \cdot \left(f\left(\operatorname{Function.update}\left(x, k, b\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.local_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a computational basis word x, the action of a matrix on site k sums over the replacement bit b. Split a word into its k-th coordinate and the remaining coordinates. The identity factors at the other sites force those coordinates to agree with x.

**Definition 1.5 (Collective spin operators).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(a: \operatorname{Fin}\left(3\right)\right), \left(\left(\operatorname{collectiveSpin}\left(n, a\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right), \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right), \mathbb{C}\right)\right) = \operatorname{HSMul.hSMul}\left(\left(\frac{1}{2}: \mathbb{C}\right), \left(\sum \left(k: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{localOp}\left(k, \operatorname{pauli}\left(a\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.collectiveSpin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The collective spin in axis a is one half of the sum of the Pauli operator at every site. It acts on computational basis words of length n.

**Theorem 1.6 (Collective spins inherit the Pauli rotation).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(u: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.specialUnitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\forall \left(r: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\left(\forall \left(a: \operatorname{Fin}\left(3\right)\right), \left(\left(\left(\operatorname{Subtype.val}\left(u\right)\right) \cdot \left(\operatorname{pauli}\left(a\right)\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(\operatorname{Subtype.val}\left(u\right)\right)\right) = \left(\sum \left(c: \operatorname{Fin}\left(3\right)\right), \left(\operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(r\left(a, c\right)\right), \operatorname{pauli}\left(c\right)\right)\right)\right)\right)\right) \to \left(\forall \left(a: \operatorname{Fin}\left(3\right)\right), \left(\left(\left(\operatorname{tensorOp}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Subtype.val}\left(u\right)\right)\right)\right) \cdot \left(\operatorname{collectiveSpin}\left(n, a\right)\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(\operatorname{tensorOp}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Subtype.val}\left(u\right)\right)\right)\right)\right) = \left(\sum \left(c: \operatorname{Fin}\left(3\right)\right), \left(\operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(r\left(a, c\right)\right), \operatorname{collectiveSpin}\left(n, c\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.collective_tensor_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the same coefficient matrix r expresses each conjugated Pauli matrix in the Pauli basis. Conjugating a local operator by the constant tensor power conjugates its single nonidentity factor. Summing this identity over the sites and interchanging the finite sums gives the collective-spin transformation.

**Theorem 1.7 (Rotation of quadratic spin products).**

$$\forall \left(n: \operatorname{Type}*\right), \left([\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(n\right)], \left(\forall \left(d: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)\right), \left(\left(\left(\operatorname{Matrix.conjTranspose}\left(d\right)\right) \cdot \left(d\right) = 1\right) \to \left(\forall \left(r: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\left(\left(\operatorname{Matrix.transpose}\left(r\right)\right) \cdot \left(r\right) = 1\right) \to \left(\forall \left(j: \left(\operatorname{Fin}\left(3\right)\right) \to \left(\operatorname{Matrix}\left(n, n, \mathbb{C}\right)\right)\right), \left(\left(\forall \left(a: \operatorname{Fin}\left(3\right)\right), \left(\left(\left(d\right) \cdot \left(j\left(a\right)\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(d\right)\right) = \left(\sum \left(c: \operatorname{Fin}\left(3\right)\right), \left(\operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(r\left(a, c\right)\right), j\left(c\right)\right)\right)\right)\right)\right) \to \left(\forall \left(\kappa: \mathbb{C}\right), \left(\forall \left(a: \operatorname{Fin}\left(3\right)\right), \left(\forall \left(b: \operatorname{Fin}\left(3\right)\right), \left(\left(\left(d\right) \cdot \left(\operatorname{HSMul.hSMul}\left(\left(\frac{1}{2}: \mathbb{C}\right), \left(j\left(a\right)\right) \cdot \left(j\left(b\right)\right) + \left(j\left(b\right)\right) \cdot \left(j\left(a\right)\right)\right) - \operatorname{HSMul.hSMul}\left(\left(\operatorname{if} a = b \operatorname{then} \kappa \operatorname{else} 0\right), 1\right)\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(d\right)\right) = \left(\sum \left(c: \operatorname{Fin}\left(3\right)\right), \left(\left(\sum \left(e: \operatorname{Fin}\left(3\right)\right), \left(\operatorname{HSMul.hSMul}\left(\left(\operatorname{Complex.ofReal}\left(r\left(a, c\right)\right)\right) \cdot \left(\operatorname{Complex.ofReal}\left(r\left(b, e\right)\right)\right), \operatorname{HSMul.hSMul}\left(\left(\frac{1}{2}: \mathbb{C}\right), \left(j\left(c\right)\right) \cdot \left(j\left(e\right)\right) + \left(j\left(e\right)\right) \cdot \left(j\left(c\right)\right)\right) - \operatorname{HSMul.hSMul}\left(\left(\operatorname{if} c = e \operatorname{then} \kappa \operatorname{else} 0\right), 1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.quadratic_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose d is unitary, r is real orthogonal, and the family j transforms under conjugation by d with coefficients r. Inserting d adjoint times d between two factors gives the product transformation. Row orthogonality expresses the diagonal correction as the contraction of two r coefficients. Consequently the symmetrized quadratic product, with any complex diagonal correction κ, transforms with two copies of r.

**Definition 1.8 (Normalized Dicke embedding).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(\operatorname{dickeIsometry}\left(n\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right)\right) = \left(\lambda \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \mapsto \left(\left(\lambda \left(r: \operatorname{Fin}\left(n + 1\right)\right) \mapsto \left(\left(\operatorname{if} \left(\sum \left(k: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin.val}\left(x\left(k\right)\right)\right)\right) = \operatorname{Fin.val}\left(r\right) \operatorname{then} \operatorname{Inv.inv}\left(\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\left(\operatorname{Nat.cast}\left(\operatorname{Nat.choose}\left(n, \operatorname{Fin.val}\left(r\right)\right)\right): \mathbb{R}\right)\right)\right)\right) \operatorname{else} 0\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.dickeIsometry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The r-th column is supported on bit words with exactly r.val entries equal to one. Each supported entry is the reciprocal of the square root of Nat.choose n r.val. The binomial coefficient is cast from the natural numbers to the reals before taking its square root, and the result is included in the complex numbers before inversion. The spin index therefore counts ones.

**Theorem 1.9 (Partial trace through a product embedding).**

$$\forall \left(a: \operatorname{Type}*\right), \left(\forall \left(b: \operatorname{Type}*\right), \left(\forall \left(i: \operatorname{Type}*\right), \left(\forall \left(j: \operatorname{Type}*\right), \left([\operatorname{Fintype}\left(a\right)], [\operatorname{Fintype}\left(b\right)], [\operatorname{Fintype}\left(i\right)], [\operatorname{Fintype}\left(j\right)], [\operatorname{DecidableEq}\left(j\right)], \left(\forall \left(v: \operatorname{Matrix}\left(a, i, \mathbb{C}\right)\right), \left(\forall \left(w: \operatorname{Matrix}\left(b, j, \mathbb{C}\right)\right), \left(\left(\left(\operatorname{Matrix.conjTranspose}\left(w\right)\right) \cdot \left(w\right) = 1\right) \to \left(\forall \left(z: \operatorname{Matrix}\left(\left(\left(i\right) \times \left(j\right)\right), \left(\left(i\right) \times \left(j\right)\right), \mathbb{C}\right)\right), \left(\operatorname{partialTraceRight}\left(\left(\left(\operatorname{Matrix.kronecker}\left(v, w\right)\right) \cdot \left(z\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(\operatorname{Matrix.kronecker}\left(v, w\right)\right)\right)\right) = \left(\left(v\right) \cdot \left(\operatorname{partialTraceRight}\left(z\right)\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(v\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.partialTrace_isometries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugate z by the Kronecker product of v and w, where w adjoint times w is the identity. In the partial trace over the second factor, the sum of a w coefficient times the conjugate of another is a Kronecker delta. Contracting that delta leaves v times the partial trace of z times v adjoint. No isometry hypothesis on v is needed.

**Definition 1.10 (Dicke coefficient at a given weight).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(w: \mathbb{N}\right), \left(\forall \left(r: \mathbb{N}\right), \left(\left(\operatorname{dickeCoefficient}\left(n, w, r\right): \mathbb{C}\right) = \left(\operatorname{if} w = r \operatorname{then} \operatorname{Inv.inv}\left(\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\left(\operatorname{Nat.cast}\left(\operatorname{Nat.choose}\left(n, r\right)\right): \mathbb{R}\right)\right)\right)\right) \operatorname{else} 0\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.dickeCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural numbers n, w and r, this coefficient is zero unless the word weight w equals r. When they agree it is the reciprocal complex inclusion of the square root of the real cast of Nat.choose n r.

**Theorem 1.11 (Summing the single-site Dicke transitions).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(a: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right), \left(\forall \left(r: \operatorname{Fin}\left(n + 1\right)\right), \left(\left(\sum \left(k: \operatorname{Fin}\left(n\right)\right), \left(\left(\sum \left(b: \operatorname{Fin}\left(2\right)\right), \left(\left(a\left(x\left(k\right), b\right)\right) \cdot \left(\operatorname{dickeIsometry}\left(n, \operatorname{Function.update}\left(x, k, b\right), r\right)\right)\right)\right)\right)\right) = \left(\left(\operatorname{Nat.cast}\left(n\right): \mathbb{C}\right) - \left(\operatorname{Nat.cast}\left(\left(\sum \left(k: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin.val}\left(x\left(k\right)\right)\right)\right)\right): \mathbb{C}\right)\right) \cdot \left(\left(a\left(0, 0\right)\right) \cdot \left(\operatorname{dickeCoefficient}\left(n, \left(\sum \left(k: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin.val}\left(x\left(k\right)\right)\right)\right), \operatorname{Fin.val}\left(r\right)\right)\right) + \left(a\left(0, 1\right)\right) \cdot \left(\operatorname{dickeCoefficient}\left(n, \left(\sum \left(k: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin.val}\left(x\left(k\right)\right)\right)\right) + 1, \operatorname{Fin.val}\left(r\right)\right)\right)\right) + \left(\left(\operatorname{Nat.cast}\left(\left(\sum \left(k: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin.val}\left(x\left(k\right)\right)\right)\right)\right): \mathbb{C}\right)\right) \cdot \left(\left(a\left(1, 0\right)\right) \cdot \left(\operatorname{dickeCoefficient}\left(n, \left(\left(\sum \left(k: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin.val}\left(x\left(k\right)\right)\right)\right) - 1: \mathbb{N}\right), \operatorname{Fin.val}\left(r\right)\right)\right) + \left(a\left(1, 1\right)\right) \cdot \left(\operatorname{dickeCoefficient}\left(n, \left(\sum \left(k: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Fin.val}\left(x\left(k\right)\right)\right)\right), \operatorname{Fin.val}\left(r\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.dicke_site_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weight of a word is the natural-number sum of its bit values. Updating site k changes that weight by the new bit minus the old bit. Separate the sites at which x k is zero from those at which it is one. There are n minus the weight sites of the first kind and weight sites of the second kind. The two possible replacement bits yield the four displayed matrix entries and Dicke coefficients. Subtraction in the weight-minus-one argument is natural-number subtraction; the multiplicities are cast to complex scalars.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.collectiveSpin`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.collective_tensor_rotation`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.dickeCoefficient`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.dickeIsometry`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.dicke_site_sum`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.local_action`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.orthogonal_sandwich`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.partialTrace_isometries`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.pauli_rotation`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.quadratic_rotation`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance.tensor_unitary`
- Dependency: [D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint](../Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm](../Information/BinaryStabilizerGraphNormalForm.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](../QuantumChannels/QubitWassersteinCouplings.md)
- Dependency: [D5/S3/QuantumChannels/ChannelTimeReversalNoGo](../../QuantumChannels/ChannelTimeReversalNoGo.md)
