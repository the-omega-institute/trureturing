# A three-box obstruction to the quantum-crystal Yangian conjecture

## Abstract

The three-box bosonic identity-class state contradicts the proposed expression of the negative-flip potential as a linear combination of affine Yangian generators.

Plane partitions are finite lower sets in the coordinatewise order on ℕ³, with coordinates starting at zero. We identify each plane partition with its underlying finite set of boxes. For every plane partition Λ, the ket |Λ⟩ denotes Finsupp.single Λ 1, the state with coefficient one at Λ and zero elsewhere. All coefficients lie in ℂ.

**Definition 1.1 (Plane partitions as finite lower sets).**

$$\operatorname{PlanePartition} = \{s: \operatorname{Finset}\left(\mathbb{N} \times (\mathbb{N} \times \mathbb{N})\right) \mid \forall (p: \mathbb{N} \times (\mathbb{N} \times \mathbb{N})), (\forall (q: \mathbb{N} \times (\mathbb{N} \times \mathbb{N})), ((q \le p) \Rightarrow ((p \in s) \Rightarrow (q \in s))))\}$$

*Formalization.* `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.PlanePartition` (`✓ std3`).

*Citation.* Thiago Araujo; Domenico Orlando; Susanne Reffert (2021). *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality*. DOI: [10.1103/PhysRevD.103.026020](https://doi.org/10.1103/PhysRevD.103.026020). URL: <https://arxiv.org/abs/2005.09103v2>.

*Commentary.*

A finite set of boxes is a plane partition when every box below any of its boxes also belongs to it. The three coordinates carry the product order. These are the crystal configurations on which the box-adding and box-removing operators of Eqs. (2a)–(2b) act.

**Definition 1.2 (The number of boxes).**

$$\forall (L: \operatorname{PlanePartition}), (\operatorname{boxCount}\left(L\right) = \operatorname{Finset.card}\left(\operatorname{Subtype.val}\left(L\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.boxCount` (`✓ std3`).

*Citation.* Thiago Araujo; Domenico Orlando; Susanne Reffert (2021). *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality*. DOI: [10.1103/PhysRevD.103.026020](https://doi.org/10.1103/PhysRevD.103.026020). URL: <https://arxiv.org/abs/2005.09103v2>.

*Commentary.*

The box count is the cardinality of the underlying finite set. It gives the grading preserved by the fermion-boson correspondence of Eq. (46).

**Definition 1.3 (The number of removable boxes).**

$$\forall (L: \operatorname{PlanePartition}), (\operatorname{removableCount}\left(L\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (p: \mathbb{N} \times (\mathbb{N} \times \mathbb{N})) \mapsto (\forall (q: \mathbb{N} \times (\mathbb{N} \times \mathbb{N})), ((q \in \operatorname{Subtype.val}\left(L\right)) \Rightarrow ((p \le q) \Rightarrow (q = p)))), \operatorname{Subtype.val}\left(L\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.removableCount` (`✓ std3`).

*Citation.* Thiago Araujo; Domenico Orlando; Susanne Reffert (2021). *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality*. DOI: [10.1103/PhysRevD.103.026020](https://doi.org/10.1103/PhysRevD.103.026020). URL: <https://arxiv.org/abs/2005.09103v2>.

*Commentary.*

A box can be removed precisely when it is maximal: every box of the same plane partition above it equals it. Counting these boxes gives the negative flippable plaquettes of Eq. (2b).

**Definition 1.4 (Finite complex combinations of plane partitions).**

$$\operatorname{State} = \operatorname{Finsupp}\left(\operatorname{PlanePartition}, \mathbb{C}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.State` (`✓ std3`).

*Citation.* Thiago Araujo; Domenico Orlando; Susanne Reffert (2021). *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality*. DOI: [10.1103/PhysRevD.103.026020](https://doi.org/10.1103/PhysRevD.103.026020). URL: <https://arxiv.org/abs/2005.09103v2>.

*Commentary.*

Finsupp denotes finitely supported functions. Thus State is the complex vector space with one basis vector for every plane partition, as in the basis transformation of Eqs. (42)–(46).

**Definition 1.5 (The box-number grading).**

$$\forall (n: \mathbb{N}), (\forall (u: \operatorname{State}), ((\operatorname{IsGrade}\left(n, u\right)) \Leftrightarrow (\forall (L: \operatorname{PlanePartition}), ((L \in \operatorname{Finsupp.support}\left(u\right)) \Rightarrow (\operatorname{boxCount}\left(L\right) = n)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.IsGrade` (`✓ std3`).

*Citation.* Thiago Araujo; Domenico Orlando; Susanne Reffert (2021). *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality*. DOI: [10.1103/PhysRevD.103.026020](https://doi.org/10.1103/PhysRevD.103.026020). URL: <https://arxiv.org/abs/2005.09103v2>.

*Commentary.*

A state has grade n when every plane partition with nonzero coefficient has n boxes. The zero state satisfies this condition for every n. Equation (46) preserves this box-number grading.

**Definition 1.6 (The negative-flip potential).**

$$(\operatorname{potentialMinus}: \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{State}, \operatorname{State}\right)) = \operatorname{Finsupp.linearCombination}\left(\mathbb{C}, \lambda (L: \operatorname{PlanePartition}) \mapsto (\operatorname{Finsupp.single}\left(L, (\operatorname{removableCount}\left(L\right): \mathbb{C})\right))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.potentialMinus` (`✓ std3`).

*Citation.* Thiago Araujo; Domenico Orlando; Susanne Reffert (2021). *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality*. DOI: [10.1103/PhysRevD.103.026020](https://doi.org/10.1103/PhysRevD.103.026020). URL: <https://arxiv.org/abs/2005.09103v2>.

*Commentary.*

The potential O₋ of Eq. (2b) acts diagonally on the plane-partition basis: for every Λ its value on |Λ⟩ is removableCount(Λ) times |Λ⟩. The displayed complex linear combination map extends these basis values by linearity; the removable count is coerced from ℕ to ℂ.

**Definition 1.7 (The three-box bosonic identity-class state).**

$$\operatorname{bosonicIdentityThree} = ((|\left\{(0, 0, 0), (1, 0, 0), (2, 0, 0)\right\}\rangle) + (2 \cdot (|\left\{(0, 0, 0), (1, 0, 0), (0, 1, 0)\right\}\rangle))) + (|\left\{(0, 0, 0), (0, 1, 0), (0, 2, 0)\right\}\rangle)$$

*Formalization.* `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.bosonicIdentityThree` (`✓ std3`).

*Citation.* Thiago Araujo; Domenico Orlando; Susanne Reffert (2021). *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality*. DOI: [10.1103/PhysRevD.103.026020](https://doi.org/10.1103/PhysRevD.103.026020). URL: <https://arxiv.org/abs/2005.09103v2>.

*Commentary.*

The three displayed single-layer plane partitions are the row (3), the hook (2, 1), and the column (1, 1, 1), in that order. Each has three boxes and third coordinate zero. Write v = bosonicIdentityThree. Its coefficients 1, 2, 1 are the S₃ characters on the identity class in (A13), as in Eq. (46) and Appendix C.

**Definition 1.8 (The consequence of the Yangian conjecture at v).**

$$(\operatorname{claim}) \Leftrightarrow (\exists (e: \mathbb{N} \to \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{State}, \operatorname{State}\right)), (\exists (f: \mathbb{N} \to \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{State}, \operatorname{State}\right)), (\exists (phi: \mathbb{N} \to \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{State}, \operatorname{State}\right)), (\exists (a: \operatorname{Finsupp}\left(\mathbb{N}, \mathbb{C}\right)), (\exists (b: \operatorname{Finsupp}\left(\mathbb{N}, \mathbb{C}\right)), (\exists (c: \operatorname{Finsupp}\left(\mathbb{N}, \mathbb{C}\right)), ((\forall (j: \mathbb{N}), (\operatorname{IsGrade}\left(4, e\left(j\right)\left(\operatorname{bosonicIdentityThree}\right)\right))) \land ((\forall (j: \mathbb{N}), (\operatorname{IsGrade}\left(2, f\left(j\right)\left(\operatorname{bosonicIdentityThree}\right)\right))) \land ((\forall (j: \mathbb{N}), (\exists (t: \mathbb{C}), (phi\left(j\right)\left(\operatorname{bosonicIdentityThree}\right) = t \cdot (\operatorname{bosonicIdentityThree})))) \land (\operatorname{potentialMinus}\left(\operatorname{bosonicIdentityThree}\right) = ((\operatorname{Finsupp.sum}\left(a, \lambda (j: \mathbb{N}) \mapsto (\lambda (x: \mathbb{C}) \mapsto (x \cdot (e\left(j\right)\left(\operatorname{bosonicIdentityThree}\right))))\right)) + (\operatorname{Finsupp.sum}\left(b, \lambda (j: \mathbb{N}) \mapsto (\lambda (x: \mathbb{C}) \mapsto (x \cdot (f\left(j\right)\left(\operatorname{bosonicIdentityThree}\right))))\right))) + (\operatorname{Finsupp.sum}\left(c, \lambda (j: \mathbb{N}) \mapsto (\lambda (x: \mathbb{C}) \mapsto (x \cdot (phi\left(j\right)\left(\operatorname{bosonicIdentityThree}\right))))\right))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.claim` (`✓ std3`).

*Citation.* Thiago Araujo; Domenico Orlando; Susanne Reffert (2021). *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality*. DOI: [10.1103/PhysRevD.103.026020](https://doi.org/10.1103/PhysRevD.103.026020). URL: <https://arxiv.org/abs/2005.09103v2>.

*Commentary.*

There are complex linear maps e_j, f_j and φ_j for every natural j, and finitely supported complex coefficient families a, b and c. The vectors e_j v have grade four, the vectors f_j v have grade two, and every φ_j v is a scalar multiple of v. A finite linear combination of these vectors equals O₋ v. These are the consequences at v of Eqs. (49)–(50) and the conjecture in Section VI. No Yangian commutation relations are assumed here, so the conjecture implies this statement.

**Theorem 1.9 (The removable-box counts contradict the proposed combination).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/araujo-orlando-reffert-2020-quantum-crystal-yangian-refutation` (refuted) by `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"araujo-orlando-reffert-2020-quantum-crystal-yangian-refutation","declaration_gid":"D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Thiago Araujo; Domenico Orlando; Susanne Reffert (2021). *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality*. DOI: [10.1103/PhysRevD.103.026020](https://doi.org/10.1103/PhysRevD.103.026020). URL: <https://arxiv.org/abs/2005.09103v2>.

*Commentary.*

The row (3), hook (2, 1) and column (1, 1, 1) have respectively 1, 2 and 1 removable boxes. Consequently O₋ v = |(3)⟩ + 4|(2, 1)⟩ + |(1, 1, 1)⟩. These three shapes are exactly the finite sets displayed in the definition of v.

Every proposed vector e_j v or f_j v vanishes at both three-box shapes (3) and (2, 1), by its grade. Every proposed φ_j v is a multiple of v, whose coefficient at (2, 1) is twice its coefficient at (3). Thus every term on the right of the proposed identity, and their finite sum, has at the hook twice its value at the row. The left side O₋ v has coefficient 4 at the hook and coefficient 1 at the row. Since 4 is not twice 1, the identity is impossible. In particular O₋ cannot act on these bosonic states as the asserted linear combination of the generators.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.IsGrade`
- Truth anchor: `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.PlanePartition`
- Truth anchor: `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.State`
- Truth anchor: `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.bosonicIdentityThree`
- Truth anchor: `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.boxCount`
- Truth anchor: `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.potentialMinus`
- Truth anchor: `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.removableCount`
- Truth anchor: `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.result`
