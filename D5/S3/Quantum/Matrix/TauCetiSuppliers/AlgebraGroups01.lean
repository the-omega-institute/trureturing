/- GID: D5/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/TauCetiSuppliers/AlgebraGroups01
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tau Ceti suppliers for finite-group and Young-diagram identities. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in Library/FiniteGroups/tauceti2026nksuppliers.md.
Modified in trureturing: relocate names into the file namespace, prune unused declarations,
inline type aliases, reuse pinned owners, and adapt the pinned Mathlib APIs.
The center and diagonal homomorphisms use AlgHom.pi, AlgHom.codRestrict,
AlgEquiv.ofBijective, Matrix.diagonalRingHom and Circle.coeHom; list sums use List.sum_toFinset.
Authors: The Tau Ceti contributors.
Repository: https://github.com/TauCetiProject/TauCeti
Revision: 5a9ceb62c81b6e1f2784d7f739938686a87ca278
Source files:
  TauCeti/Algebra/Group/Conj.lean
  TauCeti/Algebra/Group/ConjFinite.lean
  TauCeti/Algebra/MonoidAlgebra/SubgroupCharSum.lean
  TauCeti/Algebra/MonoidAlgebra/Trace.lean
  TauCeti/Algebra/MvPolynomial/Monomial.lean
  TauCeti/Algebra/Subalgebra/Center.lean
  TauCeti/Algebra/Matrix/Pi.lean
  TauCeti/Analysis/Matrix/UnitaryGroup/Basic.lean
  TauCeti/Analysis/Matrix/UnitaryGroup/Torus.lean
  TauCeti/Combinatorics/Enumerative/Partition/Basic.lean
  TauCeti/Combinatorics/Enumerative/Partition/Dominance.lean
  TauCeti/Combinatorics/Young/Diagram.lean
Retirement: when the Mathlib revision pinned in `lake-manifest.json` contains a declaration equivalent to a ported one, its clients use that declaration and the port is deleted.
admission_basis: escape-witness
escape_witness: D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.Dominates.antisymm
Direct frozen dependencies:
  D5/S3/Quantum/BlockNorm/EssentiallyHermitian.Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal
    declaration statement_id: sha256:d62beb8157c961473226b2c53ec1ff9177dff9c428778acd1b29bcc47be97cec.
  D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.rowLen_zero
    declaration statement_id: sha256:efaaa12164c1db0e709c1a0104797eb3bf77e2e3e1442c2b671f377ce75a429f.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16827
Rows beyond the first-column height use
  D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.rowLen_zero.
Declaration classification:
isConj_inv_iff — proof_shape: bind-only;
  consumer: WeylSpecht02.ClassFunction.characterPairing_classIndicator_inv.
ConjClasses.ncard_carrier_mk_eq_card_filter — proof_shape: bind-only;
  consumer: WeylSpecht03.ClassFunction.card_conjClass_mul_sum_char_mul_char_inv.
ConjClasses.card_carrier_pos — proof_shape: bind-only;
  consumer: WeylSpecht12.symmetricCharacterTable_column_orthogonality.
subgroupCharSum — proof_shape: bind-only;
  consumer: AlgebraGroups01.single_mul_subgroupCharSum.
subgroupCharSum_def — proof_shape: bind-only;
  consumer: AlgebraGroups01.single_mul_subgroupCharSum.
subgroupCharSum_coeff — proof_shape: bind-only;
  consumer: WeylSpecht06.YoungTableau.columnAntisymmetrizer_coeff.
single_mul_subgroupCharSum — proof_shape: bind-only;
  consumer: WeylSpecht06.YoungTableau.mul_columnAntisymmetrizer_left.
subgroupCharSum_mul_single — proof_shape: bind-only;
  consumer: WeylSpecht04.asAlgebraHom_subgroupCharSum_apply_eq_zero.
MonoidAlgebra.trace_mulRight — proof_shape: bind-only;
  consumer: WeylSpecht08.YoungTableau.trace_mulRight_youngSymmetrizer.
MonoidAlgebra.trace_mulLeft_single_mul_mulRight — proof_shape: bind-only;
  consumer: WeylSpecht04.Representation.mul_char_ofModule'_span_singleton.
prod_map_X_eq_monomial — proof_shape: bind-only;
  consumer: SchurPolynomial01.coeff_psumPart_partition.
Subalgebra.map_center_eq — proof_shape: bind-only;
  consumer: AlgebraGroups01.centerCongr.
centerCongr — proof_shape: bind-only;
  consumer: WeylSpecht03.AlgEquiv.centerMonoidAlgebraAlgEquivPi.
centerPiAlgEquiv — proof_shape: bind-only;
  consumer: AlgebraGroups01.centerPiMatrixAlgEquiv.
centerAlgEquivOfIsCentral — proof_shape: bind-only;
  consumer: AlgebraGroups01.centerPiMatrixAlgEquiv.
finrank_pi_matrix — proof_shape: bind-only;
  consumer: WeylSpecht03.AlgEquiv.sum_sq_eq_card_of_pi_matrix.
centerPiMatrixAlgEquiv — proof_shape: bind-only;
  consumer: WeylSpecht03.AlgEquiv.centerMonoidAlgebraAlgEquivPi.
Matrix.diagonal_mem_unitaryGroup_iff — proof_shape: bind-only;
  consumer: AlgebraGroups01.mem_unitaryTorus_iff.
Circle.coe_mem_unitary — proof_shape: bind-only;
  consumer: AlgebraGroups01.unitaryTorusHom.
unitaryTorusHom — proof_shape: bind-only;
  consumer: AlgebraGroups01.coe_unitaryTorusHom.
coe_unitaryTorusHom — proof_shape: bind-only;
  consumer:
    D5.S3.Quantum.Matrix.Schur.UnitaryPolynomialRepresentations.NKWeylCharacter.character_diagonal.
mem_unitaryTorus_iff_exists_unitaryTorusHom — proof_shape: bind-only;
  consumer: AlgebraGroups01.exists_isConj_unitaryTorusHom.
mem_unitaryTorus_iff — proof_shape: bind-only;
  consumer: AlgebraGroups01.exists_conj_mem_unitaryTorus.
exists_conj_mem_unitaryTorus — proof_shape: bind-only;
  consumer: AlgebraGroups01.exists_isConj_unitaryTorusHom.
exists_isConj_unitaryTorusHom — proof_shape: bind-only;
  consumer:
    D5.S3.Quantum.Matrix.Schur.UnitaryPolynomialRepresentations.NKWeylCharacter.character_unitary.
parts_equivCast — proof_shape: bind-only;
  consumer: WeylSpecht06.card_carrier_partitionEquivConjClasses_mul_zPart.
sortedParts_sum — proof_shape: bind-only;
  consumer: AlgebraGroups01.dominates_iff_forall_fin.
sortedParts_length_le — proof_shape: bind-only;
  consumer: AlgebraGroups01.dominates_iff_forall_fin.
PartitionLex.partitionLinearOrder — proof_shape: bind-only;
  consumer: AlgebraGroups01.PartitionLex.partition_lt_iff.
PartitionLex.partition_lt_iff — proof_shape: bind-only;
  consumer: AlgebraGroups01.lex_lt_of_strictlyDominates.
Dominates — proof_shape: bind-only;
  consumer: AlgebraGroups01.DominanceOrder.partitionPartialOrder.
dominates_iff — proof_shape: bind-only;
  consumer: WeylSpecht09.dominates_of_youngBlock_colIndex_injective.
dominates_iff_forall_fin — proof_shape: bind-only;
  consumer: AlgebraGroups01.instDecidableDominates.
instDecidableDominates — proof_shape: bind-only;
  consumer:
    WeylSpecht09.YoungTableau.dominates_of_asAlgebraHom_columnAntisymmetrizer_apply_ne_zero.
dominates_refl — proof_shape: bind-only;
  consumer: AlgebraGroups01.DominanceOrder.partitionPartialOrder.
Dominates.trans — proof_shape: bind-only;
  consumer: AlgebraGroups01.DominanceOrder.partitionPartialOrder.
lex_lt_of_prefix_sum_le — proof_shape: content;
  consumer: AlgebraGroups01.lex_lt_of_dominates_of_ne.
lex_lt_of_dominates_of_ne — proof_shape: content;
  consumer: AlgebraGroups01.Dominates.antisymm.
Dominates.antisymm — proof_shape: content;
  consumer: AlgebraGroups01.DominanceOrder.partitionPartialOrder.
DominanceOrder.partitionPartialOrder — proof_shape: bind-only;
  consumer: AlgebraGroups01.DominanceOrder.partition_le_iff.
DominanceOrder.partition_le_iff — proof_shape: bind-only;
  consumer: AlgebraGroups01.DominanceOrder.partition_lt_iff.
DominanceOrder.partition_lt_iff — proof_shape: bind-only;
  consumer: AlgebraGroups01.strictlyDominates_iff.
strictlyDominates_iff — proof_shape: bind-only;
  consumer: AlgebraGroups01.lex_le_of_dominates.
lex_lt_of_strictlyDominates — proof_shape: bind-only;
  consumer: AlgebraGroups01.lex_le_of_dominates.
lex_le_of_dominates — proof_shape: content;
  consumer: WeylSpecht14.isUnit_det_schurPolyElem.
YoungDiagram.sum_list_range — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.sum_take_rowLens_eq_card_filter_fst.
YoungDiagram.lt_colLen_zero_of_mem — proof_shape: bind-only;
  consumer: D5.S3.Quantum.Matrix.Schur.MatrixSchurPolynomial.NKSchurMatrix.dimension_ne_zero.
YoungDiagram.rowLen_bot — proof_shape: bind-only;
  consumer: SchurPolynomial03.diagramSchurPoly_mul_alternant.
YoungDiagram.rowLen_injective — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.ofRowLensFin_rowLen.
-/

import D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.IsDiag

namespace D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01


open _root_.Matrix _root_.Subalgebra
open scoped BigOperators

section
variable {G : Type*} [Group G]

theorem isConj_inv_iff {x y : G} : IsConj x⁻¹ y⁻¹ ↔ IsConj x y := by
  simp only [IsConj, SemiconjBy.inv_right_iff]
end
namespace ConjClasses
variable {G : Type*} [Group G]

@[simp]
theorem ncard_carrier_mk_eq_card_filter {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]
    (g : M) :
    (ConjClasses.mk g).carrier.ncard =
      {x ∈ (Finset.univ : Finset M) | ConjClasses.mk x = ConjClasses.mk g}.card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [_root_.ConjClasses.mem_carrier_iff_mk_eq]
end ConjClasses
section
variable {G : Type*} [Group G]
end
namespace ConjClasses
end ConjClasses
namespace ConjClasses
variable {M : Type*} [Monoid M]
end ConjClasses
namespace MulEquiv
variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
end MulEquiv
namespace ConjClasses
variable {M : Type*} [Monoid M]
end ConjClasses
namespace MulEquiv
variable {M N : Type*} [Monoid M] [Monoid N]
end MulEquiv
namespace ConjClasses
variable {M : Type*} [Monoid M]
end ConjClasses
section
variable {G : Type*}
section Monoid
variable [Monoid G]
end Monoid
end
namespace MulAut
variable {G : Type*}
section Monoid
variable [Monoid G]
end Monoid
variable [Group G]
end MulAut
section
variable {G : Type*} [Group G]
end

section
namespace ConjClasses
variable {G : Type*} [Monoid G]

theorem card_carrier_pos [Finite G] (C : _root_.ConjClasses G) : 0 < Nat.card C.carrier := by
  obtain ⟨g, rfl⟩ := C.exists_rep
  have : Nonempty (_root_.ConjClasses.mk g).carrier := ⟨⟨g, _root_.ConjClasses.mem_carrier_mk⟩⟩
  exact Nat.card_pos
end ConjClasses
end

section
variable {k G : Type*} [CommSemiring k] [Group G] (χ : G →* k) (H : Subgroup G) [Fintype H]

noncomputable def subgroupCharSum : MonoidAlgebra k G :=
  ∑ h : H, χ (h : G) • MonoidAlgebra.of k G (h : G)

theorem subgroupCharSum_def :
    subgroupCharSum χ H = ∑ h : H, χ (h : G) • MonoidAlgebra.of k G (h : G) :=
  (rfl)

@[simp]
theorem subgroupCharSum_coeff [DecidablePred (· ∈ H)] (g : G) :
    (subgroupCharSum χ H).coeff g = if g ∈ H then χ g else 0 := by
  rw [subgroupCharSum_def, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
    smul_eq_mul]
  by_cases hg : g ∈ H
  · rw [if_pos hg, Finset.sum_eq_single (⟨g, hg⟩ : H)]
    · rw [Finsupp.single_eq_same, mul_one]
    · exact fun h _ hh => by
        rw [Finsupp.single_eq_of_ne' fun e => hh (Subtype.ext e), mul_zero]
    · simp
  · rw [if_neg hg]
    exact Finset.sum_eq_zero fun h _ => by
      rw [Finsupp.single_eq_of_ne' fun e : (h : G) = g => hg (e ▸ h.property), mul_zero]

@[simp]
theorem single_mul_subgroupCharSum (p : H) :
    MonoidAlgebra.single (p : G) 1 * subgroupCharSum χ H =
      χ ((p : G)⁻¹) • subgroupCharSum χ H := by
  rw [subgroupCharSum_def, ← MonoidAlgebra.of_apply, Finset.mul_sum, Finset.smul_sum]
  simp_rw [mul_smul_comm, ← (MonoidAlgebra.of k G).map_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft p)
  intro h
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, smul_smul]
  rw [← mul_assoc, map_mul_eq_one χ (inv_mul_cancel (p : G)), one_mul]

@[simp]
theorem subgroupCharSum_mul_single (p : H) :
    subgroupCharSum χ H * MonoidAlgebra.single (p : G) 1 =
      χ ((p : G)⁻¹) • subgroupCharSum χ H := by
  rw [subgroupCharSum_def, ← MonoidAlgebra.of_apply, Finset.sum_mul, Finset.smul_sum]
  simp_rw [smul_mul_assoc, ← (MonoidAlgebra.of k G).map_mul]
  apply Fintype.sum_equiv (Equiv.mulRight p)
  intro h
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, smul_smul]
  rw [mul_left_comm, map_mul_eq_one χ (inv_mul_cancel (p : G)), mul_one]
end

open MonoidAlgebra
section

@[simp]
theorem MonoidAlgebra.trace_mulRight {k G : Type*} [CommSemiring k] [Monoid G]
    [IsLeftCancelMul G] [Finite G] (x : MonoidAlgebra k G) :
    LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulRight k x) =
      (Nat.card G : k) * x.coeff 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hdiag : ∀ g : G, (MonoidAlgebra.single g (1 : k) * x).coeff g = x.coeff 1 := fun g => by
    simpa using x.coeff_single_mul_eq_mul_coeff (m₁ := g) (r := 1) 1 (by simp)
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis G k), Matrix.trace]
  have hb : ∀ v : MonoidAlgebra k G, (MonoidAlgebra.basis G k).repr v = v.coeff :=
    fun _ => rfl
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    hb, LinearMap.mulRight_apply, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card]
end

@[simp]
theorem MonoidAlgebra.trace_mulLeft_single_mul_mulRight {k G : Type*} [CommSemiring k] [Group G]
    [Fintype G] (g : G) (y : MonoidAlgebra k G) :
    LinearMap.trace k (MonoidAlgebra k G)
        (LinearMap.mulLeft k (MonoidAlgebra.single g 1) * LinearMap.mulRight k y) =
      ∑ σ : G, y.coeff (σ⁻¹ * g⁻¹ * σ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis G k), Matrix.trace]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hb : ∀ v : MonoidAlgebra k G, (MonoidAlgebra.basis G k).repr v = v.coeff :=
    fun _ => rfl
  simp [LinearMap.toMatrix_apply, hb, ← mul_assoc, _root_.mul_inv_rev]

section
open MvPolynomial

theorem prod_map_X_eq_monomial {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod = monomial s.toFinsupp (1 : R) := by
  rw [Finset.prod_multiset_map_count, ← prod_X_pow_eq_monomial, Multiset.toFinsupp_support]
  exact Finset.prod_congr rfl fun a _ => by rw [Multiset.toFinsupp_apply]
end

namespace Subalgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable (S : Subalgebra R (Subalgebra.center R A))
section FiniteOverCenter
end FiniteOverCenter
end Subalgebra
namespace Subalgebra
section FiniteOverCentralSubalgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (S : Subalgebra R (center R A))
end FiniteOverCentralSubalgebra
section NoetherianCenter
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (S : Subalgebra R (center R A))
end NoetherianCenter
end Subalgebra
section
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
private theorem Subalgebra.map_center_eq (e : A ≃ₐ[R] B) :
    (Subalgebra.center R A).map e.toAlgHom = Subalgebra.center R B := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    apply Subalgebra.mem_center_iff.mpr
    intro z
    obtain ⟨w,rfl⟩ := e.surjective z
    change e w * e y = e y * e w
    simpa only [map_mul] using congrArg e ((Subalgebra.mem_center_iff.mp hy) w)
  · intro hx
    refine Subalgebra.mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply Subalgebra.mem_center_iff.mpr
    intro w
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using (Subalgebra.mem_center_iff.mp hx) (e w)

def centerCongr (e : A ≃ₐ[R] B) :
    Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B :=
  (e.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.Subalgebra.map_center_eq e))
section Pi
variable {ι : Type*} {S : ι → Type*} [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)]

private noncomputable def centerPiAlgEquiv :
    Subalgebra.center R (Π i, S i) ≃ₐ[R] Π i, Subalgebra.center R (S i) :=
  have mem_iff : ∀ x : Π i, S i,
      x ∈ Subalgebra.center R (Π i, S i) ↔ ∀ i, x i ∈ Subalgebra.center R (S i) := fun _ => by
    rw [Subalgebra.center_pi]; simp
  AlgEquiv.ofBijective
    (AlgHom.pi fun i =>
      ((Pi.evalAlgHom R S i).comp (Subalgebra.center R (Π i, S i)).val).codRestrict
        (Subalgebra.center R (S i)) (fun x => (mem_iff x.1).mp x.2 i))
    ⟨fun x y h => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i)),
      fun y => ⟨⟨fun i => (y i).1, (mem_iff _).mpr fun i => (y i).2⟩, rfl⟩⟩

end Pi
section IsCentral
variable (K D : Type*) [CommSemiring K] [Semiring D] [Algebra K D]
  [FaithfulSMul K D] [Algebra.IsCentral K D]

private noncomputable def centerAlgEquivOfIsCentral : Subalgebra.center K D ≃ₐ[K] K :=
  (Subalgebra.equivOfEq _ _ (Algebra.IsCentral.center_eq_bot K D)).trans
    (Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective K D))
end IsCentral
end

section
open scoped BigOperators
section Semiring
variable (k : Type*) [Semiring k] [StrongRankCondition k] {ι : Type*} [Fintype ι] (d : ι → ℕ)

theorem finrank_pi_matrix :
    Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) = ∑ i, d i ^ 2 := by
  rw [Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.finrank_matrix]
  simp [sq]
end Semiring
section CommSemiring
variable (k : Type*) [CommSemiring k] {ι : Type*} (d : ι → ℕ)

noncomputable def centerPiMatrixAlgEquiv [∀ i, NeZero (d i)] :
    Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) ≃ₐ[k] (ι → k) :=
  centerPiAlgEquiv.trans (AlgEquiv.piCongrRight fun i =>
    haveI : FaithfulSMul k (Matrix (Fin (d i)) (Fin (d i)) k) :=
      inferInstanceAs (FaithfulSMul k (Fin (d i) → Fin (d i) → k))
    centerAlgEquivOfIsCentral k _)
section FiniteIndex
variable [StrongRankCondition k] [Fintype ι]
end FiniteIndex
end CommSemiring
section Field
variable (k : Type*) [Field k] {ι : Type*} (d : ι → ℕ)
section Presentation
variable {d : ι → ℕ} {A : Type*} [Ring A] [Algebra k A] {D : ι → Type*} [∀ i, Ring (D i)]
  [∀ i, Algebra k (D i)]
section Blocks
variable [FiniteDimensional k A] (e : A ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
end Blocks
section Count
variable [Fintype ι] [FiniteDimensional k A]
end Count
section Bounds
variable [FiniteDimensional k A] (e : A ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
end Bounds
end Presentation
end Field
end

namespace Matrix
variable {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]

@[simp]
theorem diagonal_mem_unitaryGroup_iff {d : n → α} :
    diagonal d ∈ unitaryGroup n α ↔ ∀ i, d i ∈ unitary α := by
  simp only [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one, diagonal_eq_diagonal_iff, Pi.star_apply,
    Unitary.mem_iff_self_mul_star]
end Matrix
section
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Circle.coe_mem_unitary (z : Circle) : (z : ℂ) ∈ unitary ℂ :=
  Unitary.mem_iff_star_mul_self.mpr <| by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, Complex.ofReal_one]
end

section
open _root_.Matrix
open D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.Matrix
variable (n : Type*) [Fintype n] [DecidableEq n]

noncomputable def unitaryTorusHom : (n → Circle) →* unitaryGroup n ℂ :=
  (((_root_.Matrix.diagonalRingHom n ℂ : (n → ℂ) →+* Matrix n n ℂ).toMonoidHom).comp
    (MonoidHom.pi fun i => _root_.Circle.coeHom.comp (Pi.evalMonoidHom (fun _ : n => Circle) i))).codRestrict
      (unitaryGroup n ℂ) (fun z =>
        diagonal_mem_unitaryGroup_iff.mpr fun i => Circle.coe_mem_unitary (z i))

variable {n}

@[simp]
theorem coe_unitaryTorusHom (z : n → Circle) :
    (unitaryTorusHom n z : Matrix n n ℂ) = diagonal fun i => (z i : ℂ) :=
  (rfl)


private theorem mem_unitaryTorus_iff_exists_unitaryTorusHom {g : unitaryGroup n ℂ} :
    g ∈ (unitaryTorusHom n).range ↔ ∃ z : n → Circle, unitaryTorusHom n z = g :=
  MonoidHom.mem_range

private theorem mem_unitaryTorus_iff {g : unitaryGroup n ℂ} :
    g ∈ (unitaryTorusHom n).range ↔ (g : Matrix n n ℂ).IsDiag := by
  refine ⟨fun ⟨z, hz⟩ => hz ▸ isDiag_diagonal _, fun hg => ?_⟩
  -- The diagonal entries of a diagonal unitary matrix are unitary, so lie on the circle.
  have hunit := diagonal_mem_unitaryGroup_iff.mp (hg.diagonal_diag.symm ▸ g.2)
  refine ⟨fun i => ⟨(g : Matrix n n ℂ) i i,
    mem_sphere_zero_iff_norm.mpr (CStarRing.norm_of_mem_unitary (hunit i))⟩, Subtype.ext ?_⟩
  exact hg.diagonal_diag

private theorem exists_conj_mem_unitaryTorus (g : unitaryGroup n ℂ) :
    ∃ u : unitaryGroup n ℂ, u * g * u⁻¹ ∈ (unitaryTorusHom n).range := by
  obtain ⟨U, hU, d, hd⟩ := exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (g : Matrix n n ℂ)
  refine ⟨(⟨U, hU⟩ : unitaryGroup n ℂ)⁻¹, mem_unitaryTorus_iff.mpr ?_⟩
  -- Inversion in `U(n)` is `star`, which commutes with the coercion to matrices.
  have hcoe : (((⟨U, hU⟩ : unitaryGroup n ℂ)⁻¹ * g * ((⟨U, hU⟩ : unitaryGroup n ℂ)⁻¹)⁻¹ :
      unitaryGroup n ℂ) : Matrix n n ℂ) = star U * g * U := by
    rw [inv_inv, Submonoid.coe_mul, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star]
  rw [hcoe, hd]
  exact isDiag_diagonal d

theorem exists_isConj_unitaryTorusHom (g : unitaryGroup n ℂ) :
    ∃ z : n → Circle, IsConj g (unitaryTorusHom n z) := by
  obtain ⟨u, hu⟩ := exists_conj_mem_unitaryTorus g
  obtain ⟨z, hz⟩ := mem_unitaryTorus_iff_exists_unitaryTorusHom.mp hu
  exact ⟨z, isConj_iff.mpr ⟨u, hz.symm⟩⟩
end

section

theorem parts_equivCast {m l : ℕ} (h : m = l) (p : m.Partition) :
    (Equiv.cast (congrArg Nat.Partition h) p).parts = p.parts := by
  subst h; rfl
namespace Nat.Partition
end Nat.Partition
end

section

private theorem sortedParts_sum {n : ℕ} (μ : n.Partition) : ((μ.parts.sort (· ≥ ·))).sum = n := by
  calc
    ((μ.parts.sort (· ≥ ·))).sum = (↑((μ.parts.sort (· ≥ ·))) : Multiset ℕ).sum :=
      (Multiset.sum_coe _).symm
    _ = μ.parts.sum := congrArg Multiset.sum (Multiset.sort_eq μ.parts (· ≥ ·))
    _ = n := μ.parts_sum
private theorem sortedParts_length_le {n : ℕ} (μ : n.Partition) : ((μ.parts.sort (· ≥ ·))).length ≤ n := by
  calc
    ((μ.parts.sort (· ≥ ·))).length ≤ ((μ.parts.sort (· ≥ ·))).sum :=
      List.length_le_sum_of_one_le _ fun i hi =>
        μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
    _ = n := sortedParts_sum μ
namespace PartitionLex

scoped instance partitionLinearOrder {n : ℕ} : LinearOrder n.Partition :=
  LinearOrder.lift' (fun μ => μ.parts.sort (· ≥ ·)) (by
    intro μ ν h
    apply Nat.Partition.ext
    calc
      μ.parts = ↑(μ.parts.sort (· ≥ ·)) := (Multiset.sort_eq μ.parts (· ≥ ·)).symm
      _ = ↑(ν.parts.sort (· ≥ ·)) := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
      _ = ν.parts := Multiset.sort_eq ν.parts (· ≥ ·))

@[simp]
private theorem partition_lt_iff {n : ℕ} {μ ν : n.Partition} :
    @LT.lt n.Partition partitionLinearOrder.toLT μ ν ↔
      μ.parts.sort (· ≥ ·) < ν.parts.sort (· ≥ ·) :=
  Iff.rfl
end PartitionLex

def Dominates {n : ℕ} (μ ν : n.Partition) : Prop :=
  ∀ k : ℕ,
    ((ν.parts.sort (· ≥ ·)).take k).sum ≤ ((μ.parts.sort (· ≥ ·)).take k).sum

theorem dominates_iff {n : ℕ} {μ ν : n.Partition} :
    Dominates μ ν ↔
      ∀ k : ℕ,
        ((ν.parts.sort (· ≥ ·)).take k).sum ≤
          ((μ.parts.sort (· ≥ ·)).take k).sum :=
  Iff.rfl

private theorem dominates_iff_forall_fin {n : ℕ} {μ ν : n.Partition} :
    Dominates μ ν ↔
      ∀ k : Fin (n + 1),
        ((ν.parts.sort (· ≥ ·)).take k).sum ≤
          ((μ.parts.sort (· ≥ ·)).take k).sum := by
  refine ⟨fun h k => h k, fun h k => ?_⟩
  by_cases hk : k ≤ n
  · exact h ⟨k, Nat.lt_succ_iff.mpr hk⟩
  · have hn_lt_k : n < k := Nat.lt_of_not_ge hk
    rw [List.take_of_length_le ((sortedParts_length_le ν).trans hn_lt_k.le),
      List.take_of_length_le ((sortedParts_length_le μ).trans hn_lt_k.le),
      sortedParts_sum, sortedParts_sum]
instance instDecidableDominates {n : ℕ} (μ ν : n.Partition) : Decidable (Dominates μ ν) :=
  decidable_of_iff _ dominates_iff_forall_fin.symm

@[simp, refl]
private theorem dominates_refl {n : ℕ} (μ : n.Partition) : Dominates μ μ :=
  fun _ => le_rfl

@[trans]
private theorem Dominates.trans {n : ℕ} {μ ν ξ : n.Partition}
    (hμν : Dominates μ ν) (hνξ : Dominates ν ξ) : Dominates μ ξ :=
  fun k => (hνξ k).trans (hμν k)
private theorem lex_lt_of_prefix_sum_le {l₁ l₂ : List ℕ} (hsum : l₁.sum = l₂.sum)
    (hpos₁ : ∀ i ∈ l₁, 0 < i) (hpos₂ : ∀ i ∈ l₂, 0 < i)
    (hle : ∀ k : ℕ, (l₂.take k).sum ≤ (l₁.take k).sum) (hne : l₁ ≠ l₂) : l₂ < l₁ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => exact (hne rfl).elim
      | cons b l₂ =>
          have hb : 0 < b := hpos₂ b (by simp)
          simp only [List.sum_nil, List.sum_cons] at hsum
          omega
  | cons a l₁ ih =>
      cases l₂ with
      | nil =>
          have ha : 0 < a := hpos₁ a (by simp)
          simp only [List.sum_cons, List.sum_nil] at hsum
          omega
      | cons b l₂ =>
          have hba : b ≤ a := by
            simpa only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil,
              add_zero] using hle 1
          rcases hba.eq_or_lt with hba | hba
          · subst b
            apply List.Lex.cons
            apply ih
            · simpa only [List.sum_cons, Nat.add_left_cancel_iff] using hsum
            · intro i hi
              exact hpos₁ i (by simp [hi])
            · intro i hi
              exact hpos₂ i (by simp [hi])
            · intro k
              simpa only [List.take_succ_cons, List.sum_cons, Nat.add_le_add_iff_left] using
                hle (k + 1)
            · intro h
              exact hne (congrArg (List.cons a) h)
          · exact List.Lex.rel hba
private theorem lex_lt_of_dominates_of_ne {n : ℕ} {μ ν : n.Partition}
    (hdom : Dominates μ ν) (hne : μ ≠ ν) :
    (ν.parts.sort (· ≥ ·)) < (μ.parts.sort (· ≥ ·)) := by
  apply lex_lt_of_prefix_sum_le (sortedParts_sum μ |>.trans (sortedParts_sum ν).symm)
  · intro i hi
    exact μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
  · intro i hi
    exact ν.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
  · exact hdom
  · intro h
    apply hne
    apply Nat.Partition.ext
    calc
      μ.parts = ↑((μ.parts.sort (· ≥ ·))) := (Multiset.sort_eq μ.parts (· ≥ ·)).symm
      _ = ↑((ν.parts.sort (· ≥ ·))) := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
      _ = ν.parts := Multiset.sort_eq ν.parts (· ≥ ·)

theorem Dominates.antisymm {n : ℕ} {μ ν : n.Partition}
    (hμν : Dominates μ ν) (hνμ : Dominates ν μ) : μ = ν := by
  by_contra hne
  have hν_lt_μ := lex_lt_of_dominates_of_ne hμν hne
  have hμ_lt_ν := lex_lt_of_dominates_of_ne hνμ (Ne.symm hne)
  exact hν_lt_μ.asymm hμ_lt_ν
namespace DominanceOrder

scoped instance partitionPartialOrder {n : ℕ} : PartialOrder n.Partition where
  le μ ν := Dominates ν μ
  le_refl μ := dominates_refl μ
  le_trans _ _ _ hμν hνξ := hνξ.trans hμν
  le_antisymm _ _ hμν hνμ := hνμ.antisymm hμν

@[simp]
theorem partition_le_iff {n : ℕ} {μ ν : n.Partition} :
    @LE.le n.Partition partitionPartialOrder.toLE μ ν ↔ Dominates ν μ :=
  Iff.rfl

@[simp]
private theorem partition_lt_iff {n : ℕ} {μ ν : n.Partition} :
    @LT.lt n.Partition partitionPartialOrder.toLT μ ν ↔ Dominates ν μ ∧ μ ≠ ν := by
  let := partitionPartialOrder (n := n)
  exact lt_iff_le_and_ne.trans (and_congr partition_le_iff Iff.rfl)
end DominanceOrder


@[simp]
private theorem strictlyDominates_iff {n : ℕ} {μ ν : n.Partition} :
    DominanceOrder.partitionPartialOrder.lt ν μ ↔ Dominates μ ν ∧ μ ≠ ν := by
  exact DominanceOrder.partition_lt_iff.trans (and_congr Iff.rfl ne_comm)
open scoped D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.PartitionLex

private theorem lex_lt_of_strictlyDominates {n : ℕ} {μ ν : n.Partition}
    (h : DominanceOrder.partitionPartialOrder.lt ν μ) : ν < μ := by
  rw [PartitionLex.partition_lt_iff]
  rw [strictlyDominates_iff] at h
  exact lex_lt_of_dominates_of_ne h.1 h.2

theorem lex_le_of_dominates {n : ℕ} {μ ν : n.Partition} (h : Dominates μ ν) : ν ≤ μ := by
  rcases eq_or_ne μ ν with rfl | hne
  · exact le_rfl
  · exact (lex_lt_of_strictlyDominates (strictlyDominates_iff.mpr ⟨h, hne⟩)).le
end

namespace YoungDiagram
theorem sum_list_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  simpa only [List.toFinset_range] using (List.sum_toFinset f (List.nodup_range (n := n))).symm

theorem lt_colLen_zero_of_mem {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∈ μ) :
    i < μ.colLen 0 := by
  by_contra hi
  have hz := D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.rowLen_zero
    μ i (Nat.le_of_not_gt hi)
  have hj := _root_.YoungDiagram.mem_iff_lt_rowLen.mp h
  omega

@[simp]
theorem rowLen_bot (i : ℕ) : (⊥ : YoungDiagram).rowLen i = 0 := by
  simp [_root_.YoungDiagram.rowLen]

theorem rowLen_injective : Function.Injective _root_.YoungDiagram.rowLen := by
  intro μ ν h
  ext c
  obtain ⟨i, j⟩ := c
  rw [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_cells,
    _root_.YoungDiagram.mem_iff_lt_rowLen, _root_.YoungDiagram.mem_iff_lt_rowLen, congrFun h i]
end YoungDiagram

end D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01
