# Three Mutually Unbiased Bases in Complex Dimension Six

## Abstract

Exact tensor and Gauss-sum certificates produce three mutually unbiased bases in complex dimension six.

**Theorem 1.1 (Coordinate tensor products preserve orthonormality and overlap-only mutual unbiasedness).**

$$(\forall alpha, beta \text{ finite}, \forall x, u: \mathbb{C}^{alpha}, y, v: \mathbb{C}^{beta},\\\langle \operatorname{tensorVector}\left(x, y\right), \operatorname{tensorVector}\left(u, v\right) \rangle = \langle x, u \rangle \times \langle y, v \rangle),\\\land (\forall alpha, beta \text{ finite}, \forall b, bPrime, \operatorname{CoordinateOrthonormalBasis}\left(b\right) \Rightarrow \operatorname{CoordinateOrthonormalBasis}\left(bPrime\right) \Rightarrow \operatorname{CoordinateOrthonormalBasis}\left(\operatorname{tensorBasis}\left(b, bPrime\right)\right)),\\\land (\forall alpha, beta \text{ finite}, \forall b, c, bPrime, cPrime, \operatorname{MutuallyUnbiased}\left(b, c\right) \Rightarrow \operatorname{MutuallyUnbiased}\left(bPrime, cPrime\right) \Rightarrow \operatorname{MutuallyUnbiased}\left(\operatorname{tensorBasis}\left(b, bPrime\right), \operatorname{tensorBasis}\left(c, cPrime\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/MubDimensionSixTensor.tensor_mub_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite coordinate types alpha and beta, expanding the sum over alpha times beta and distributing multiplication factors the coordinate inner product of two tensor vectors into the product of the two coordinate inner products.

The factorization turns the Gram identity for two orthonormal bases into the product of two Kronecker deltas. It also multiplies two cross-overlap values, and Fintype.card_prod identifies the result with the reciprocal cardinality of the product carrier.

The Lean predicate MutuallyUnbiased is exactly the atom's overlap-only condition. Orthonormality remains a separate second conjunct, so the third conjunct needs no hidden Gram hypotheses.

The basis-level tensorBasis is a thin wrapper around Mathlib's Matrix.kronecker. The vector-level tensorVector remains explicit because the factorization theorem is stated for coordinate vectors.

**Theorem 1.2 (Three explicit qutrit bases are pairwise mutually unbiased).**

$$\operatorname{PairwiseMUB}\left(qutritBases\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/MubDimensionSixTensor.qutrit_three_mubs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The family consists of the standard basis, the normalized character table of Z/3Z, and the normalized quadratic-phase basis with entries omega^(j k + k^2), where omega=exp(2 pi i/3).

The proof evaluates every entry of all three Gram tables and every ordered cross-overlap table. The reductions use omega cubed equals one, omega not equal to one, conjugate omega equals omega squared, and one plus omega plus omega squared equals zero.

All computations are exact complex equalities. No floating-point approximation, frozen theorem, or unchecked evaluator supplies the one-third overlap values.

**Theorem 1.3 (Three tensor-product bases certify M(6) at least three).**

$$\operatorname{PairwiseMUB}\left(dimensionSixBases\right) \land ((\forall r: \operatorname{Fin}\left(3\right), \operatorname{CoordinateOrthonormalBasis}\left(\operatorname{dimensionSixBases}\left(r\right)\right)) \land\\(\forall r, s: \operatorname{Fin}\left(3\right), r \neq s \Rightarrow \forall i, j: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(3\right),\\\lvert \langle \operatorname{dimensionSixBases}\left(r, i\right), \operatorname{dimensionSixBases}\left(s, j\right) \rangle \rvert^{2} = \frac{1}{6})).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/MubDimensionSixTensor.dimension_six_three_mubs_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each of the three family indices, dimensionSixBases tensors the corresponding Z, X, or Y qubit basis with the corresponding standard, Fourier, or quadratic-phase qutrit basis.

The qubit overlap table has exact value one half and the qutrit table has exact value one third. Tensor factorization therefore gives one sixth for every cross-overlap on Fin 2 times Fin 3, while the same argument preserves each Gram identity.

The theorem records both the PairwiseMUB package and the source atom's separate displayed orthonormality and one-sixth clauses. It proves the known lower bound of three bases only and makes no claim about the open existence of a fourth basis in complex dimension six.

## References

- Truth anchor: `D5/S3/QuantumContext/MubDimensionSixTensor.dimension_six_three_mubs_certificate`
- Truth anchor: `D5/S3/QuantumContext/MubDimensionSixTensor.qutrit_three_mubs`
- Truth anchor: `D5/S3/QuantumContext/MubDimensionSixTensor.tensor_mub_package`
- Dependency: [D5/S3/QuantumContext/HesseSicCertificate](HesseSicCertificate.md)
