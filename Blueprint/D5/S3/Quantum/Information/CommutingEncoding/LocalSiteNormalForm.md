# Local forms of commuting qubit factors

## Abstract

Commuting qubit tensor operators have local commutation signs and diagonal or phased Pauli local forms.

**Lemma 1.1 (Local factors commute or anticommute).**

$$\forall (n: \mathbb{N}), (\forall (U: (\operatorname{Fin}\left(2^{n}\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))), ((\forall (a: \operatorname{Fin}\left(2^{n}\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (U\left(a, j\right) \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)))) \Rightarrow ((\forall (a: \operatorname{Fin}\left(2^{n}\right)), (\forall (b: \operatorname{Fin}\left(2^{n}\right)), ((\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp}\left(U\left(a\right)\right)) \cdot (\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp}\left(U\left(b\right)\right)) = (\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp}\left(U\left(b\right)\right)) \cdot (\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp}\left(U\left(a\right)\right))))) \Rightarrow (\forall (a: \operatorname{Fin}\left(2^{n}\right)), (\forall (b: \operatorname{Fin}\left(2^{n}\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (((U\left(a, j\right)) \cdot (U\left(b, j\right)) = (U\left(b, j\right)) \cdot (U\left(a, j\right))) \lor ((U\left(a, j\right)) \cdot (U\left(b, j\right)) = -((U\left(b, j\right)) \cdot (U\left(a, j\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CommutingEncoding/LocalSiteNormalForm.local_commutation_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose that every local factor U(a,j) is unitary and the complete tensor operators commute. Multiplicativity of tensor products identifies the tensor of U(a,j)U(b,j) with the tensor of U(b,j)U(a,j). This tensor is unitary and therefore nonzero. Choose a nonzero matrix entry, keep all coordinates except j fixed, and vary the row and column at j. The product of the fixed entries is nonzero, so cancellation shows that the two local products differ by a complex scalar c.

Both local products have the same nonzero determinant. Taking the determinant of the proportionality equation multiplies that determinant by c raised to the cardinality of Fin 2, namely c². Hence c² = 1, so c is 1 or −1. These give respectively commutation and anticommutation at every site j. The statement also permits n = 0, when there is no site j.

**Lemma 1.2 (A diagonal or phased Pauli family).**

$$\forall (\kappa: Type*), (\forall (B: (\kappa) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))), ((\forall (a: \kappa), (B\left(a\right) \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))) \Rightarrow ((\forall (a: \kappa), (\forall (b: \kappa), (((B\left(a\right)) \cdot (B\left(b\right)) = (B\left(b\right)) \cdot (B\left(a\right))) \lor ((B\left(a\right)) \cdot (B\left(b\right)) = -((B\left(b\right)) \cdot (B\left(a\right))))))) \Rightarrow (\exists (V: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), ((V \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land ((\forall (a: \kappa), (\exists (d: (\operatorname{Fin}\left(2\right)) \to (\mathbb{C})), (((V) \cdot (B\left(a\right))) \cdot (\operatorname{Matrix.conjTranspose}\left(V\right)) = \operatorname{Matrix.diagonal}\left(d\right)))) \lor (\exists (c: (\kappa) \to (\mathbb{C})), (\exists (p: (\kappa) \to (\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli})), ((\forall (a: \kappa), ((\operatorname{star}\left(c\left(a\right)\right)) \cdot (c\left(a\right)) = (1: \mathbb{C}))) \land (\forall (a: \kappa), (((V) \cdot (B\left(a\right))) \cdot (\operatorname{Matrix.conjTranspose}\left(V\right)) = \operatorname{SMul.smul}\left(c\left(a\right), \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix}\left(p\left(a\right)\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CommutingEncoding/LocalSiteNormalForm.local_site_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B be any family of unitary two-by-two complex matrices, with each pair commuting or anticommuting. No finiteness or nonemptiness of the index type κ is required. First suppose a nonscalar member A has nonzero trace. If A anticommutes with B(a), conjugating A by B(a) negates A. Trace invariance then forces its trace to vanish, a contradiction. Thus every B(a) commutes with A. Diagonalize the normal matrix A by a unitary K. Its eigenvalues are distinct, because equality would make A scalar. The commutation equations for KᴴB(a)K force both off-diagonal entries to vanish. Taking V = Kᴴ gives the first alternative.

Otherwise every nonscalar member is traceless. A unitary diagonalization then has eigenvalues c and −c, with star(c)c = 1. Conjugating Z back shows that each such matrix is c times a Hermitian involution. A scalar member is a unit-modulus scalar times the identity, so choose B(a) = c(a)H(a) for every a. All c(a) are nonzero; cancellation transfers each pair's commutation sign to the Hermitian involutions H(a).

If all H(a) are scalar, use the identity unitary. Otherwise diagonalize a nonscalar H(a₀). Its distinct eigenvalues square to one and therefore are 1 and −1, so a unitary sends it to Z or −Z. Every transformed H(a) now commutes or anticommutes with Z. If they all commute with Z, their off-diagonal entries vanish, and squaring to the identity shows that they commute or anticommute with X as well. If some transformed H(b) anticommutes with Z, it has zero diagonal and off-diagonal entries z and star(z), where z star(z) = 1. The diagonal unitary with entries 1 and z fixes Z and sends H(b) to X. Conjugating the sign relations with H(b) gives the signs with X for all other members.

Finally a matrix squaring to the identity that has a commutation sign with both Z and X is a scalar multiple of a Pauli matrix. The four sign pairs give I, Z, X and Y; their scalar squares equal one and hence their scalars have unit modulus. Apply this to each transformed H(a), choose the Pauli label p(a), and multiply its scalar by the original phase c(a). The product phases still satisfy star(c(a))c(a) = 1. This gives the second alternative with one common unitary V.

## References

- Truth anchor: `D5/S3/Quantum/Information/CommutingEncoding/LocalSiteNormalForm.local_commutation_signs`
- Truth anchor: `D5/S3/Quantum/Information/CommutingEncoding/LocalSiteNormalForm.local_site_normal_form`
- Dependency: [D5/S3/Quantum/BlockNorm/EssentiallyHermitian](../../BlockNorm/EssentiallyHermitian.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm](../BinaryStabilizerGraphNormalForm.md)
