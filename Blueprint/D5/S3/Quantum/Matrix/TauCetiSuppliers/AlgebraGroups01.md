# AlgebraGroups01

## Abstract

Finite-group, partition and Young-tableau constructions from the Tau Ceti library. Symbols use the Lean names in the file namespace; tableau coordinate maps in later modules are YoungTableaux01.YoungTableau.rowIndex and colIndex. Proof arguments are suppressed when they do not affect the mathematical value.

**Theorem 1.1 (Is conj inv iff).**

$$\forall (G : \operatorname{Type}) [ \operatorname{Group} G ] (x y : G) , \operatorname{IsConj} x^{-1} y^{-1} \iff \operatorname{IsConj} x y$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.isConj_inv_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives is Conj inv iff.

**Theorem 1.2 (Ncard carrier mk eq card filter).**

$$\forall (M : \operatorname{Type}) [ \operatorname{Monoid} M ] [ \operatorname{Fintype} M ] [ \operatorname{DecidableEq} M ] (g : M) , (\operatorname{ConjClasses} . \operatorname{mk} g) . \operatorname{carrier} . \operatorname{ncard} = ((\operatorname{Finset} . \operatorname{univ} : \operatorname{Finset} M) . \operatorname{filter} (\operatorname{fun} (x : M) \mapsto \operatorname{ConjClasses} . \operatorname{mk} x = \operatorname{ConjClasses} . \operatorname{mk} g)) . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.ncard_carrier_mk_eq_card_filter` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives ncard carrier mk eq card filter.

**Theorem 1.3 (Card carrier pos).**

$$\forall (G : \operatorname{Type}) [ \operatorname{Monoid} G ] [ \operatorname{Finite} G ] (C : \operatorname{ConjClasses} G) , 0 < \operatorname{Nat} . \operatorname{card} \{ g : G // g \in C . \operatorname{carrier} \}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.card_carrier_pos` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives card carrier pos.

**Definition 1.4 (Subgroup char sum).**

$$\forall (k G : \operatorname{Type}) [ \operatorname{CommSemiring} k ] [ \operatorname{Group} G ] (chi : G \to* k) (H : \operatorname{Subgroup} G) [ \operatorname{Fintype} H ] , \operatorname{subgroupCharSum} chi H = \sum_{(h : H)} chi (\operatorname{val} h : G) \cdot \operatorname{MonoidAlgebra} . \operatorname{of} k G (\operatorname{val} h : G)$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.subgroupCharSum` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The sum assigns the character value χ(h) to each subgroup element in the monoid algebra.

**Theorem 1.5 (Subgroup char sum def).**

$$\forall (k G : \operatorname{Type}) [ \operatorname{CommSemiring} k ] [ \operatorname{Group} G ] (chi : G \to* k) (H : \operatorname{Subgroup} G) [ \operatorname{Fintype} H ] , \operatorname{subgroupCharSum} chi H = \sum_{(h : H)} chi (\operatorname{val} h : G) \cdot \operatorname{MonoidAlgebra} . \operatorname{of} k G (\operatorname{val} h : G)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.subgroupCharSum_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives subgroup Char Sum def.

**Theorem 1.6 (Subgroup char sum coeff).**

$$\forall (k : \operatorname{Type}) (G : \operatorname{Type}) [ \operatorname{CommSemiring} k ] [ \operatorname{Group} G ] (chi : G \to* k) (H : \operatorname{Subgroup} G) [ \operatorname{Fintype} H ] [ \operatorname{DecidablePred} \operatorname{fun} x \mapsto x \in H ] (g : G) , (\operatorname{subgroupCharSum} chi H) . \operatorname{coeff} g = \operatorname{if} g \in H \operatorname{then} chi g \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.subgroupCharSum_coeff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives subgroup Char Sum coeff.

**Theorem 1.7 (Single mul subgroup char sum).**

$$\forall (k : \operatorname{Type}) (G : \operatorname{Type}) [ \operatorname{CommSemiring} k ] [ \operatorname{Group} G ] (chi : G \to* k) (H : \operatorname{Subgroup} G) [ \operatorname{Fintype} H ] (p : H) , \operatorname{MonoidAlgebra} . \operatorname{single} ((\operatorname{val} p : G)) 1 * \operatorname{subgroupCharSum} chi H = chi ((\operatorname{val} p : G)^{-1}) \cdot \operatorname{subgroupCharSum} chi H$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.single_mul_subgroupCharSum` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives single mul subgroup Char Sum.

**Theorem 1.8 (Subgroup char sum mul single).**

$$\forall (k : \operatorname{Type}) (G : \operatorname{Type}) [ \operatorname{CommSemiring} k ] [ \operatorname{Group} G ] (chi : G \to* k) (H : \operatorname{Subgroup} G) [ \operatorname{Fintype} H ] (p : H) , \operatorname{subgroupCharSum} chi H * \operatorname{MonoidAlgebra} . \operatorname{single} ((\operatorname{val} p : G)) 1 = chi ((\operatorname{val} p : G)^{-1}) \cdot \operatorname{subgroupCharSum} chi H$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.subgroupCharSum_mul_single` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives subgroup Char Sum mul single.

**Theorem 1.9 (Trace mul right).**

$$\forall (k : \operatorname{Type}) (G : \operatorname{Type}) [ \operatorname{CommSemiring} k ] [ \operatorname{Monoid} G ] [ \operatorname{IsLeftCancelMul} G ] [ \operatorname{Finite} G ] (x : \operatorname{MonoidAlgebra} k G) , (\operatorname{LinearMap} . \operatorname{trace} k (\operatorname{MonoidAlgebra} k G)) (\operatorname{LinearMap} . \operatorname{mulRight} k x) = (\operatorname{Nat} . \operatorname{card} G : k) * x . \operatorname{coeff} 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.trace_mulRight` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives trace mul Right.

**Theorem 1.10 (Trace mul left single mul mul right).**

$$\forall (k : \operatorname{Type}) (G : \operatorname{Type}) [ \operatorname{CommSemiring} k ] [ \operatorname{Group} G ] [ \operatorname{Fintype} G ] (g : G) (y : \operatorname{MonoidAlgebra} k G) , (\operatorname{LinearMap} . \operatorname{trace} k (\operatorname{MonoidAlgebra} k G)) (\operatorname{LinearMap} . \operatorname{mulLeft} k (\operatorname{MonoidAlgebra} . \operatorname{single} g 1) * \operatorname{LinearMap} . \operatorname{mulRight} k y) = \sum_{(\sigma : G)} y . \operatorname{coeff} (\sigma^{-1} * g^{-1} * \sigma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.trace_mulLeft_single_mul_mulRight` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives trace mul Left single mul mul Right.

**Theorem 1.11 (Prod map x eq monomial).**

$$\forall (\sigma : \operatorname{Type}) [ \operatorname{DecidableEq} \sigma ] (R : \operatorname{Type}) [ \operatorname{CommSemiring} R ] (s : \operatorname{Multiset} \sigma) , (\operatorname{Multiset} . \operatorname{map} \operatorname{MvPolynomial} . X s) . \operatorname{prod} = (\operatorname{MvPolynomial} . \operatorname{monomial} (\operatorname{Multiset} . \operatorname{toFinsupp} s)) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.prod_map_X_eq_monomial` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives prod map X eq monomial.

**Definition 1.12 (Center congr).**

$$\forall (R A B : \operatorname{Type}) [ \operatorname{CommSemiring} R ] [ \operatorname{Semiring} A ] [ \operatorname{Semiring} B ] [ \operatorname{Algebra} R A ] [ \operatorname{Algebra} R B ] (e : A \equiv_{a} [ R ] B) (x : \operatorname{Subalgebra} . \operatorname{center} R A) (y : \operatorname{Subalgebra} . \operatorname{center} R B) , \operatorname{val} (\operatorname{centerCongr} e x) = e (\operatorname{val} x) \land \operatorname{val} ((\operatorname{centerCongr} e) . \operatorname{symm} y) = e . \operatorname{symm} (\operatorname{val} y)$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.centerCongr` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The algebra equivalence restricts to the centers. The forward and inverse maps are the restrictions of e and e.symm.

**Theorem 1.13 (Finrank pi matrix).**

$$\forall (k : \operatorname{Type}) [ \operatorname{Semiring} k ] [ \operatorname{StrongRankCondition} k ] (\iota : \operatorname{Type}) [ \operatorname{Fintype} \iota ] (d : \iota \to \mathbb{N}) , \operatorname{Module} . \operatorname{finrank} k ((i : \iota) \to \operatorname{Matrix} (\operatorname{Fin} (d i)) (\operatorname{Fin} (d i)) k) = \sum_{i} d i^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.finrank_pi_matrix` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives finrank pi matrix.

**Definition 1.14 (Center pi matrix alg equiv).**

$$\forall (k \iota : \operatorname{Type}) [ \operatorname{CommSemiring} k ] (d : \iota \to \mathbb{N}) [ \forall (i : \iota) , \operatorname{NeZero} (d i) ] (x : \operatorname{Subalgebra} . \operatorname{center} k (\operatorname{Pi} (i : \iota) , \operatorname{Matrix} (\operatorname{Fin} (d i)) (\operatorname{Fin} (d i)) k)) (y : \iota \to k) , (\forall (i : \iota) , (\operatorname{centerPiMatrixAlgEquiv} k d x) i = \operatorname{Algebra} . \operatorname{botEquivOfInjective} (\operatorname{Subalgebra} . \operatorname{equivOfEq} (\operatorname{Subalgebra} . \operatorname{center} k (\operatorname{Matrix} (\operatorname{Fin} (d i)) (\operatorname{Fin} (d i)) k)) (\perp : \operatorname{Subalgebra} k (\operatorname{Matrix} (\operatorname{Fin} (d i)) (\operatorname{Fin} (d i)) k)) \langle (\operatorname{val} x) i \rangle)) \land (\forall (i : \iota) , \operatorname{val} ((\operatorname{centerPiMatrixAlgEquiv} k d) . \operatorname{symm} y) i = \operatorname{algebraMap} k (\operatorname{Matrix} (\operatorname{Fin} (d i)) (\operatorname{Fin} (d i)) k) (y i))$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.centerPiMatrixAlgEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The center of a product of nonzero matrix algebras is identified with the coefficient functions. Each forward coordinate transports the central component to the bottom subalgebra and applies Algebra.botEquivOfInjective; the inverse applies algebraMap coordinatewise. Proof fields of subtypes are omitted.

**Theorem 1.15 (Diagonal mem unitary group iff).**

$$\forall (n : \operatorname{Type}) (\alpha : \operatorname{Type}) [ \operatorname{Fintype} n ] [ \operatorname{DecidableEq} n ] [ \operatorname{CommRing} \alpha ] [ \operatorname{StarRing} \alpha ] (d : n \to \alpha) , \operatorname{Matrix} . \operatorname{diagonal} d \in \operatorname{Matrix} . \operatorname{unitaryGroup} n \alpha \iff \forall (i : n) , d i \in \operatorname{unitary} \alpha$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.diagonal_mem_unitaryGroup_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives diagonal mem unitary Group iff.

**Theorem 1.16 (Coe mem unitary).**

$$\forall (z : \operatorname{Circle}) , \operatorname{val} z \in \operatorname{unitary} \mathbb{C}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.coe_mem_unitary` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives coe mem unitary.

**Definition 1.17 (Unitary torus hom).**

$$\forall (n : \operatorname{Type}) [ \operatorname{Fintype} n ] [ \operatorname{DecidableEq} n ] (z : n \to \operatorname{Circle}) , (\operatorname{unitaryTorusHom} n z : \operatorname{Matrix} n n \mathbb{C}) = \operatorname{Matrix} . \operatorname{diagonal} (\operatorname{fun} (i : n) \mapsto (\operatorname{val} (z i) : \mathbb{C}))$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.unitaryTorusHom` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The homomorphism sends a function with values on Circle to its diagonal unitary matrix.

**Theorem 1.18 (Coe unitary torus hom).**

$$\forall (n : \operatorname{Type}) [ \operatorname{Fintype} n ] [ \operatorname{DecidableEq} n ] (z : n \to \operatorname{Circle}) , \operatorname{val} ((\operatorname{unitaryTorusHom} n) z) = \operatorname{Matrix} . \operatorname{diagonal} \operatorname{fun} i \mapsto (\operatorname{val} (z i) : \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.coe_unitaryTorusHom` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives coe unitary Torus Hom.

**Theorem 1.19 (Exists is conj unitary torus hom).**

$$\forall (n : \operatorname{Type}) [ \operatorname{Fintype} n ] [ \operatorname{DecidableEq} n ] (g : \operatorname{Matrix} . \operatorname{unitaryGroup} n \mathbb{C}) , \exists (z : n \to \operatorname{Circle}) , \operatorname{IsConj} g ((\operatorname{unitaryTorusHom} n) z)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.exists_isConj_unitaryTorusHom` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives exists is Conj unitary Torus Hom.

**Theorem 1.20 (Parts equiv cast).**

$$\forall (m l : \mathbb{N}) (h : m = l) (p : \operatorname{Nat} . \operatorname{Partition} m) , (\operatorname{Equiv} . \operatorname{cast} (\operatorname{congrArg} \operatorname{Nat} . \operatorname{Partition} h) p) . \operatorname{parts} = p . \operatorname{parts}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.parts_equivCast` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives parts equiv Cast.

**Definition 1.21 (Partition linear order).**

$$\forall (n : \mathbb{N}) , \operatorname{PartitionLex} . \operatorname{partitionLinearOrder} = \operatorname{LinearOrder} . \operatorname{lift} ' (\operatorname{fun} (\mu : \operatorname{Nat} . \operatorname{Partition} n) \mapsto \mu . \operatorname{parts} . \operatorname{sort} (\operatorname{fun} (a b : \mathbb{N}) \mapsto b \le a))$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.partitionLinearOrder` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The linear order is lifted from the lexicographic order of the parts sorted in decreasing order. The lift uses injectivity of the sorted-parts map.

**Definition 1.22 (Dominates).**

$$\forall (n : \mathbb{N}) (\mu \nu : \operatorname{Nat} . \operatorname{Partition} n) , \operatorname{Dominates} \mu \nu \iff \forall (k : \mathbb{N}) , ((\nu . \operatorname{parts} . \operatorname{sort} (\operatorname{fun} (a b : \mathbb{N}) \mapsto b \le a)) . \operatorname{take} k) . \operatorname{sum} \le ((\mu . \operatorname{parts} . \operatorname{sort} (\operatorname{fun} (a b : \mathbb{N}) \mapsto b \le a)) . \operatorname{take} k) . \operatorname{sum}$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.Dominates` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives Dominates.

**Theorem 1.23 (Dominates iff).**

$$\forall (n : \mathbb{N}) (\mu \nu : n . \operatorname{Partition}) , \operatorname{Dominates} \mu \nu \iff \forall (k : \mathbb{N}) , (\operatorname{List} . \operatorname{take} k (\nu . \operatorname{parts} . \operatorname{sort} \operatorname{fun} \operatorname{x1} \operatorname{x2} \mapsto \operatorname{x1} \ge \operatorname{x2})) . \operatorname{sum} \le (\operatorname{List} . \operatorname{take} k (\mu . \operatorname{parts} . \operatorname{sort} \operatorname{fun} \operatorname{x1} \operatorname{x2} \mapsto \operatorname{x1} \ge \operatorname{x2})) . \operatorname{sum}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.dominates_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives dominates iff.

**Definition 1.24 (Inst decidable dominates).**

$$\begin{aligned}\forall (n : \mathbb{N}) (\mu \nu : \operatorname{Nat} . \operatorname{Partition} n) , \operatorname{instDecidableDominates} \mu \nu : \operatorname{Decidable} (\operatorname{Dominates} \mu \nu)\\\forall (n : \mathbb{N}) (\mu \nu : \operatorname{Nat} . \operatorname{Partition} n) , \operatorname{decide} (\operatorname{Dominates} \mu \nu) = \operatorname{decide} (\forall (k : \operatorname{Fin} (n + 1)) , ((\nu . \operatorname{parts} . \operatorname{sort} (\operatorname{fun} (a b : \mathbb{N}) \mapsto b \le a)) . \operatorname{take} (\operatorname{val} k)) . \operatorname{sum} \le ((\mu . \operatorname{parts} . \operatorname{sort} (\operatorname{fun} (a b : \mathbb{N}) \mapsto b \le a)) . \operatorname{take} (\operatorname{val} k)) . \operatorname{sum})\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.instDecidableDominates` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The decision procedure transports the decision of the displayed finite-prefix condition to Dominates. Prefixes beyond n contain all parts, whose sum is n. The transport proof does not change the Boolean decision.

**Theorem 1.25 (Antisymm).**

$$\forall (n : \mathbb{N}) (\mu \nu : n . \operatorname{Partition}) , \operatorname{Dominates} \mu \nu \to \operatorname{Dominates} \nu \mu \to \mu = \nu$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.antisymm` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives antisymm.

**Definition 1.26 (Partition partial order).**

$$\forall (n : \mathbb{N}) (\mu \nu : \operatorname{Nat} . \operatorname{Partition} n) , \operatorname{DominanceOrder} . \operatorname{partitionPartialOrder} . \operatorname{le} \mu \nu \iff \operatorname{Dominates} \nu \mu$$

*Formalization.* `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.partitionPartialOrder` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The partial order has μ ≤ ν when ν dominates μ. Reflexivity, transitivity and antisymmetry give its order fields.

**Theorem 1.27 (Partition le iff).**

$$\forall (n : \mathbb{N}) (\mu \nu : \operatorname{Nat} . \operatorname{Partition} n) , \operatorname{DominanceOrder} . \operatorname{partitionPartialOrder} . \operatorname{le} \mu \nu \iff \operatorname{Dominates} \nu \mu$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.partition_le_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives partition le iff.

**Theorem 1.28 (Lex le of dominates).**

$$\forall (n : \mathbb{N}) (\mu \nu : \operatorname{Nat} . \operatorname{Partition} n) , \operatorname{Dominates} \mu \nu \to \operatorname{PartitionLex} . \operatorname{partitionLinearOrder} . \operatorname{le} \nu \mu$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.lex_le_of_dominates` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives lex le of dominates.

**Theorem 1.29 (Sum list range).**

$$\forall (f : \mathbb{N} \to \mathbb{N}) (n : \mathbb{N}) , (\operatorname{List} . \operatorname{map} f (\operatorname{List} . \operatorname{range} n)) . \operatorname{sum} = \sum_{i \in \operatorname{Finset} . \operatorname{range} n} f i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.sum_list_range` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives sum list range.

**Theorem 1.30 (Lt col len zero of mem).**

$$\forall (\mu : \operatorname{YoungDiagram}) (i j : \mathbb{N}) , (i , j) \in \mu \to i < \mu . \operatorname{colLen} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.lt_colLen_zero_of_mem` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives lt col Len zero of mem.

**Theorem 1.31 (Row len bot).**

$$\forall (i : \mathbb{N}) , \perp . \operatorname{rowLen} i = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.rowLen_bot` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Len bot.

**Theorem 1.32 (Row len injective).**

$$\operatorname{Function} . \operatorname{Injective} \operatorname{YoungDiagram} . \operatorname{rowLen}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.rowLen_injective` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Kevin Gomez (2026). *Finite-group and Young-tableau suppliers for Schur moments*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a9ceb62c81b6e1f2784d7f739938686a87ca278>.

*Commentary.*

The displayed statement gives row Len injective.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.Dominates`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.antisymm`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.card_carrier_pos`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.centerCongr`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.centerPiMatrixAlgEquiv`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.coe_mem_unitary`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.coe_unitaryTorusHom`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.diagonal_mem_unitaryGroup_iff`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.dominates_iff`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.exists_isConj_unitaryTorusHom`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.finrank_pi_matrix`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.instDecidableDominates`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.isConj_inv_iff`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.lex_le_of_dominates`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.lt_colLen_zero_of_mem`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.ncard_carrier_mk_eq_card_filter`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.partitionLinearOrder`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.partitionPartialOrder`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.partition_le_iff`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.parts_equivCast`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.prod_map_X_eq_monomial`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.rowLen_bot`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.rowLen_injective`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.single_mul_subgroupCharSum`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.subgroupCharSum`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.subgroupCharSum_coeff`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.subgroupCharSum_def`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.subgroupCharSum_mul_single`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.sum_list_range`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.trace_mulLeft_single_mul_mulRight`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.trace_mulRight`
- Truth anchor: `D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01.unitaryTorusHom`
- Dependency: [D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts](../../../../S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.md)
- Dependency: [D5/S3/Quantum/BlockNorm/EssentiallyHermitian](../../BlockNorm/EssentiallyHermitian.md)
