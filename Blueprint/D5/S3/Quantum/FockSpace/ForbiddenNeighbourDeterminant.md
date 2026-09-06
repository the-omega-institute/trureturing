# Forbidden Neighbour Determinant

## Abstract

Weighted forbidden-neighbour configurations, their Gram determinant, and quantum readout.

**Theorem 1.1 (Admissibility as exclusion).**

$$\forall n \in \mathbb{N},\; \forall b \in \operatorname{Fin}(n) \to \operatorname{Bool},\; \operatorname{AdmissibleCount.Adm}(n, b) \Leftrightarrow \left(\forall i \in \operatorname{Fin}(n),\; \forall j \in \operatorname{Fin}(n),\; \operatorname{val}(i) + 1 = \operatorname{val}(j) \Rightarrow \left(b(i) = \operatorname{false} \lor b(j) = \operatorname{false}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AdmissibleCount.Adm owns the configuration predicate, with its existing decAdm instance. Coordinates are zero-based; a true Boolean means occupied. This characterization gives the adjacency reading used by reversal and quantum normalization.

**Definition 1.2 (Occupation number).**

$$\forall n \in \mathbb{N},\; \forall b \in \operatorname{Fin}(n) \to \operatorname{Bool},\; \operatorname{occupationCount}(b) = \sum_{i: \operatorname{Fin}(n)} (\operatorname{Bool.toNat}(b(i)))$$

*Formalization.* `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bool.toNat maps false to zero and true to one.

**Definition 1.3 (The configuration polynomial).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}(n) \to \mathbb{R},\; \operatorname{forbiddenPartition}(w) = \sum_{b: \{ b: \operatorname{Fin}(n) \to \operatorname{Bool} \mid \operatorname{AdmissibleCount.Adm}(n, b) \}} ((\operatorname{Polynomial.X})^{\operatorname{occupationCount}(\operatorname{val}(b))} \cdot \operatorname{Polynomial.C}(\prod_{i: \operatorname{Fin}(n)} ((w(i))^{\operatorname{Bool.toNat}(\operatorname{val}(b)(i))})))$$

*Formalization.* `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.forbiddenPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum is over the legal subtype. Polynomial.X and Polynomial.C are the indeterminate and constant embedding. Coefficients use only powers and products of weights.

**Definition 1.4 (The explicit bidiagonal matrix).**

$$\forall d \in \mathbb{N},\; \forall w \in \operatorname{Fin}(\operatorname{Nat.sub}(2 \cdot d, 1)) \to \mathbb{R},\; \forall i \in \operatorname{Fin}(d),\; \forall j \in \operatorname{Fin}(d),\; \operatorname{lowerBidiagonal}(w)(i, j) = \operatorname{ite}(i = j, \operatorname{Real.sqrt}(w(\operatorname{Fin.mk}(2 \cdot \operatorname{val}(i)))), \operatorname{ite}(\operatorname{val}(j) + 1 = \operatorname{val}(i), \operatorname{Real.sqrt}(w(\operatorname{Fin.mk}(2 \cdot \operatorname{val}(j) + 1))), 0))$$

*Formalization.* `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.lowerBidiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin.mk carries the displayed index with its bound proof. Odd one-based weights form the diagonal; even one-based weights form the subdiagonal. The remaining entries are zero.

**Theorem 1.5 (Gram positivity).**

$$\forall d \in \mathbb{N},\; \forall w \in \operatorname{Fin}(\operatorname{Nat.sub}(2 \cdot d, 1)) \to \mathbb{R},\; \operatorname{Matrix.PosSemidef}(\operatorname{Matrix.transpose}(\operatorname{lowerBidiagonal}(w)) \cdot \operatorname{lowerBidiagonal}(w))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.gramPosSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This companion binds Mathlib Gram positivity for the explicit matrix. It includes singular matrices and does not need strictly positive weights.

**Definition 1.6 (The Gram eigenvalues).**

$$\forall d \in \mathbb{N},\; \forall w \in \operatorname{Fin}(\operatorname{Nat.sub}(2 \cdot d, 1)) \to \mathbb{R},\; \operatorname{gramEigenvalue}(w) = \operatorname{Matrix.IsHermitian.eigenvalues}(\operatorname{Matrix.PosSemidef.isHermitian}(\operatorname{gramPosSemidef}(w)))$$

*Formalization.* `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.gramEigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The eigenvalues are Mathlib's real Hermitian eigenvalue list, including any zero eigenvalues.

**Definition 1.7 (Normalized configuration amplitudes).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}(n) \to \mathbb{R},\; \forall r \in \mathbb{R},\; \forall b \in \{ b: \operatorname{Fin}(n) \to \operatorname{Bool} \mid \operatorname{AdmissibleCount.Adm}(n, b) \},\; \operatorname{quantumState}(w, r)(b) = \operatorname{Complex.ofReal}(\frac{1}{\operatorname{Real.sqrt}(\operatorname{Polynomial.eval}(r, \operatorname{forbiddenPartition}(w)))} \cdot (r)^{\frac{\operatorname{Nat.cast}(\mathbb{R}, \operatorname{occupationCount}(\operatorname{val}(b)))}{2}} \cdot \prod_{i: \operatorname{Fin}(n)} ((w(i))^{\frac{\operatorname{Nat.cast}(\mathbb{R}, \operatorname{Bool.toNat}(\operatorname{val}(b)(i)))}{2}}))$$

*Formalization.* `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.quantumState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both half exponents are real exponents. Nat.cast here denotes the real coercion. The complex vector uses the legal configurations as its coordinates.

**Definition 1.8 (The occupation observable).**

$$\forall n \in \mathbb{N},\; \operatorname{numberOperator}(n) = \operatorname{Matrix.diagonal}((b: \{ b: \operatorname{Fin}(n) \to \operatorname{Bool} \mid \operatorname{AdmissibleCount.Adm}(n, b) \} \mapsto \operatorname{Nat.cast}(\mathbb{C}, \operatorname{occupationCount}(\operatorname{val}(b)))))$$

*Formalization.* `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.numberOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.cast here is the complex coercion. This diagonal matrix acts on the configuration space.

**Definition 1.9 (Single-particle tunnelling).**

$$\forall d \in \mathbb{N},\; \forall w \in \operatorname{Fin}(\operatorname{Nat.sub}(2 \cdot d, 1)) \to \mathbb{R},\; \operatorname{tunnellingMatrix}(w) = \operatorname{Matrix.fromBlocks}(0, \operatorname{lowerBidiagonal}(w), \operatorname{Matrix.transpose}(\operatorname{lowerBidiagonal}(w)), 0)$$

*Formalization.* `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.tunnellingMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two blocks are indexed by Fin d. This single-particle space is distinct from the configuration space.

**Theorem 1.10 (Determinant realization and quantum readout).**

$$\begin{aligned}\forall d: \mathbb{N}, w: \operatorname{Fin}(\operatorname{Nat.sub}(2 \cdot d, 1)) \to \mathbb{R},\\(1 \le d \land \left(\forall i \in \operatorname{Fin}(\operatorname{Nat.sub}(2 \cdot d, 1)),\; 0 \le w(i)\right)) \implies \\(\operatorname{forbiddenPartition}(w) = \operatorname{Matrix.det}(1 + \operatorname{Polynomial.X} \cdot \operatorname{Matrix.map}(\operatorname{Matrix.transpose}(\operatorname{lowerBidiagonal}(w)) \cdot \operatorname{lowerBidiagonal}(w), \operatorname{Polynomial.C})))\\\land (\operatorname{Matrix.PosSemidef}(\operatorname{Matrix.transpose}(\operatorname{lowerBidiagonal}(w)) \cdot \operatorname{lowerBidiagonal}(w)))\\\land (\forall i \in \operatorname{Fin}(d),\; 0 \le \operatorname{gramEigenvalue}(w, i))\\\land (\operatorname{forbiddenPartition}(w) = \prod_{i: \operatorname{Fin}(d) , \operatorname{gramEigenvalue}(w, i) \ne 0} (1 + \operatorname{Polynomial.C}(\operatorname{gramEigenvalue}(w, i)) \cdot \operatorname{Polynomial.X}))\\\land (\forall z \in \mathbb{C},\; \operatorname{Polynomial.eval}(z, \operatorname{Polynomial.map}(\operatorname{Complex.ofRealHom}, \operatorname{forbiddenPartition}(w))) = 0 \Rightarrow \left(\exists t \in \mathbb{R},\; t < 0 \land \left(z = \operatorname{Complex.ofReal}(t) \land \left(\exists i \in \operatorname{Fin}(d),\; 0 < \operatorname{gramEigenvalue}(w, i) \land t = -(\frac{1}{\operatorname{gramEigenvalue}(w, i)})\right)\right)\right))\\\land (\operatorname{Matrix.charpoly}(\operatorname{tunnellingMatrix}(w)) = \operatorname{Matrix.det}((\operatorname{Polynomial.X})^{2} \cdot 1 - \operatorname{Matrix.map}(\operatorname{Matrix.transpose}(\operatorname{lowerBidiagonal}(w)) \cdot \operatorname{lowerBidiagonal}(w), \operatorname{Polynomial.C})))\\\land (\forall v \in \mathbb{R},\; v \ne 0 \Rightarrow \operatorname{Polynomial.eval}(v, \operatorname{Matrix.charpoly}(\operatorname{tunnellingMatrix}(w))) = (v)^{2 \cdot d} \cdot \operatorname{Polynomial.eval}(-(\frac{1}{(v)^{2}}), \operatorname{forbiddenPartition}(w)))\\\land (\forall n \in \mathbb{N},\; \forall u \in \operatorname{Fin}(n + 2) \to \mathbb{R},\; \operatorname{forbiddenPartition}(u) = \operatorname{forbiddenPartition}((i: \operatorname{Fin}(n + 1) \mapsto u(\operatorname{Fin.castSucc}(i)))) + \operatorname{Polynomial.X} \cdot \operatorname{Polynomial.C}(u(\operatorname{Fin.last}(n + 1))) \cdot \operatorname{forbiddenPartition}((i: \operatorname{Fin}(n) \mapsto u(\operatorname{Fin.castSucc}(\operatorname{Fin.castSucc}(i))))))\\\land (\forall r \in \mathbb{R},\; \operatorname{quantumState}(w, r) = \frac{1}{\operatorname{Complex.ofReal}(\operatorname{Real.sqrt}(\operatorname{Polynomial.eval}(r, \operatorname{forbiddenPartition}(w))))} \cdot \sum_{b: \{ b: \operatorname{Fin}(\operatorname{Nat.sub}(2 \cdot d, 1)) \to \operatorname{Bool} \mid \operatorname{AdmissibleCount.Adm}(\operatorname{Nat.sub}(2 \cdot d, 1), b) \}} (\operatorname{Complex.ofReal}((r)^{\frac{\operatorname{Nat.cast}(\mathbb{R}, \operatorname{occupationCount}(\operatorname{val}(b)))}{2}} \cdot \prod_{i: \operatorname{Fin}(\operatorname{Nat.sub}(2 \cdot d, 1))} ((w(i))^{\frac{\operatorname{Nat.cast}(\mathbb{R}, \operatorname{Bool.toNat}(\operatorname{val}(b)(i)))}{2}})) \cdot \operatorname{Pi.single}(b, 1)))\\\land (\forall r \in \mathbb{R},\; 0 < r \Rightarrow \operatorname{dotProduct}(\operatorname{star}(\operatorname{quantumState}(w, r)), \operatorname{quantumState}(w, r)) = 1)\\\land (\forall b \in \{ b: \operatorname{Fin}(\operatorname{Nat.sub}(2 \cdot d, 1)) \to \operatorname{Bool} \mid \operatorname{AdmissibleCount.Adm}(\operatorname{Nat.sub}(2 \cdot d, 1), b) \},\; \operatorname{Matrix.mulVec}(\operatorname{numberOperator}(\operatorname{Nat.sub}(2 \cdot d, 1)), \operatorname{Pi.single}(b, 1)) = \operatorname{Nat.cast}(\mathbb{C}, \operatorname{occupationCount}(\operatorname{val}(b))) \cdot \operatorname{Pi.single}(b, 1))\\\land (\forall r \in \mathbb{R},\; \forall theta \in \mathbb{R},\; 0 < r \Rightarrow \operatorname{dotProduct}(\operatorname{star}(\operatorname{quantumState}(w, r)), \operatorname{Matrix.mulVec}(\operatorname{NormedSpace.exp}(\operatorname{Complex.ofReal}(theta) \cdot \operatorname{Complex.I} \cdot \operatorname{numberOperator}(\operatorname{Nat.sub}(2 \cdot d, 1))), \operatorname{quantumState}(w, r))) = \frac{\operatorname{Polynomial.eval}(\operatorname{Complex.ofReal}(r) \cdot \operatorname{Complex.exp}(\operatorname{Complex.ofReal}(theta) \cdot \operatorname{Complex.I}), \operatorname{Polynomial.map}(\operatorname{Complex.ofRealHom}, \operatorname{forbiddenPartition}(w)))}{\operatorname{Complex.ofReal}(\operatorname{Polynomial.eval}(r, \operatorname{forbiddenPartition}(w)))})\\\land (\forall P \in \operatorname{Polynomial}(\mathbb{R}),\; \forall r \in \mathbb{R},\; \forall theta \in \mathbb{R},\; \left(\operatorname{forbiddenPartition}(w) = P \land 0 < r\right) \Rightarrow \operatorname{dotProduct}(\operatorname{star}(\operatorname{quantumState}(w, r)), \operatorname{Matrix.mulVec}(\operatorname{NormedSpace.exp}(\operatorname{Complex.ofReal}(theta) \cdot \operatorname{Complex.I} \cdot \operatorname{numberOperator}(\operatorname{Nat.sub}(2 \cdot d, 1))), \operatorname{quantumState}(w, r))) = \frac{\operatorname{Polynomial.eval}(\operatorname{Complex.ofReal}(r) \cdot \operatorname{Complex.exp}(\operatorname{Complex.ofReal}(theta) \cdot \operatorname{Complex.I}), \operatorname{Polynomial.map}(\operatorname{Complex.ofRealHom}, P))}{\operatorname{Complex.ofReal}(\operatorname{Polynomial.eval}(r, P))})\\\land (\operatorname{Fintype.card}(\{ b: \operatorname{Fin}(\operatorname{Nat.sub}(2 \cdot d, 1)) \to \operatorname{Bool} \mid \operatorname{AdmissibleCount.Adm}(\operatorname{Nat.sub}(2 \cdot d, 1), b) \}) = \operatorname{Nat.fib}(2 \cdot d + 1) \land \operatorname{Fintype.card}(\operatorname{Sum}(\operatorname{Fin}(d), \operatorname{Fin}(d))) = 2 \cdot d)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.forbidden_neighbour_determinant` (`✓ std3`). ∎

*Citation.* Ole J. Heilmann and Elliott H. Lieb (1972). *Theory of monomer-dimer systems*. DOI: [10.1007/BF01877590](https://doi.org/10.1007/BF01877590).

*Commentary.*

The parenthesized rows hold simultaneously. The weights are nonnegative, including zero; d is at least one. Matrix multiplication, scalar multiplication and polynomial evaluation have their displayed Mathlib meanings.

The configuration recurrence is derived by splitting endpoint occupancy. A second endpoint expansion gives the path determinant recurrence, and interleaving the two parts of the explicit bidiagonal block matrix identifies the Gram determinant. Square roots cancel before the final polynomial coefficients.

The negative-root clause is the weighted-path specialization of the Heilmann-Lieb zero principle (1972). The exact bidiagonal realization and normalized readout are the repository's explicit construction; the literature note attributes only the zero principle.

The charpoly identity is an identity of real polynomials and applies at zero. The reciprocal evaluation formula is written for nonzero v; its polynomial continuation is the preceding identity, so totalized division at zero is never used to claim that formula.

The symbol P in the conditional row is an arbitrary real polynomial. Substituting the actual Jensen polynomial requires the independent equality forbiddenPartition(w)=P. No RH assumption or such Jensen equality is asserted.

The final row gives the two basis counts. Equality of partition polynomials does not assert a unitary equivalence of the complete physical systems. Nat.sub is natural truncated subtraction; every other division displayed below is in the real or complex field.

## References

- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true`
- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.forbiddenPartition`
- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.forbidden_neighbour_determinant`
- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.gramEigenvalue`
- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.gramPosSemidef`
- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.lowerBidiagonal`
- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.numberOperator`
- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount`
- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.quantumState`
- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.tunnellingMatrix`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](../../../S1/Words/AdmissibleWords/AdmissibleCount.md)
