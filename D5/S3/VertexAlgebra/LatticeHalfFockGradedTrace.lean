/- GID: D5/S3/VertexAlgebra/LatticeHalfFockGradedTrace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockGradedTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual all-grade half-Fock support, finite fibres, basis and inserted trace. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
import D5.S3.VertexAlgebra.PolynomialFockCharacter
import D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

/-! # Actual finite half-Fock grades and inserted traces

The original tensor zero-mode is diagonal in its infinite ambient basis.
Finite coordinate support identifies each grade, and a finite basis computes
the restriction of every ground endomorphism. Independent coloured-partition
counting gives its multiplicity and its formal product.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct PowerSeries.WithPiTopology

namespace D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients
open LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient TwistedGround.OperatorAlgebra
open D5.S3.VertexAlgebra.HalfFockSpectralFiberSource

abbrev OddMonomial (D : LatticeData) := Index D →₀ ℕ

def oddWeight (D : LatticeData) (d : OddMonomial D) : ℕ :=
  Finsupp.weight (omega D) d

abbrev OddFiber (D : LatticeData) (N : ℕ) := {d : OddMonomial D // oddWeight D d = N}

theorem oddFiber_support_bounds (D : LatticeData) (N : ℕ)
    (d : OddFiber D N) (x : Index D) (hx : x ∈ d.1.support) :
    omega D x ≤ N ∧ x.2 ≤ N := by
  have hw : omega D x ≤ oddWeight D d.1 :=
    Finsupp.le_weight_of_ne_zero' (w := omega D)
      (by exact Finsupp.mem_support_iff.mp hx)
  have hw' : omega D x ≤ N := by simpa [d.2] using hw
  constructor
  · exact hw'
  · dsimp [omega] at hw'
    omega

theorem oddFiber_exponent_bound (D : LatticeData) (N : ℕ)
    (d : OddFiber D N) (x : Index D) :
    d.1 x ≤ N := by
  have hw := Finsupp.le_weight (omega D) (s := x) (by simp [omega]) d.1
  change d.1 x ≤ oddWeight D d.1 at hw
  rw [d.2] at hw
  exact hw


theorem oddFiber_finite (D : LatticeData) (N : ℕ) : Finite (OddFiber D N) := by
  classical
  have hindex (d : OddFiber D N) (x : Index D) (hx : N ≤ x.2) : d.1 x = 0 := by
    by_contra hne
    have h := (oddFiber_support_bounds D N d x (Finsupp.mem_support_iff.mpr hne)).1
    dsimp [omega] at h
    omega
  have hexponent (d : OddFiber D N) (x : Index D) : d.1 x ≤ N :=
    oddFiber_exponent_bound D N d x
  let encode (d : OddFiber D N) (x : Fin D.rank × Fin N) : Fin (N + 1) :=
    ⟨d.1 (x.1, x.2.val), Nat.lt_succ_of_le (hexponent d _)⟩
  have hinj : Function.Injective encode := by
    intro d e h
    apply Subtype.ext
    apply Finsupp.ext
    intro x
    by_cases hx : x.2 < N
    · exact congrArg Fin.val (congrFun h (x.1, ⟨x.2, hx⟩))
    · rw [hindex d x (Nat.le_of_not_lt hx), hindex e x (Nat.le_of_not_lt hx)]
  exact Finite.of_injective encode hinj

noncomputable instance oddFiber_fintype (D : LatticeData) (N : ℕ) :
    Fintype (OddFiber D N) := @Fintype.ofFinite _ (oddFiber_finite D N)

def actualTensorL0 (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (ActualTensor D hu) :=
  tensorL D (ActualGround D hu) (actualInverse D) 0

def actualGrade (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ) :
    Submodule ℂ (ActualTensor D hu) :=
  LinearMap.ker
    (actualTensorL0 D hu -
      ((D.rank : ℂ) / 16 + (N : ℂ) / 2) •
        (LinearMap.id : Module.End ℂ (ActualTensor D hu)))

private theorem actualInverse_left_local (D : LatticeData) (hu : IsUnit D.G.det) :
    actualInverse D * gramComplex D = 1 := by
  have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℤ =>
    M.map (Int.castRingHom ℂ)) (Matrix.nonsing_inv_mul D.G hu)
  change (D.G⁻¹).map (Int.castRingHom ℂ) * D.G.map (Int.castRingHom ℂ) = 1
  rw [← Matrix.map_mul]
  simpa using h

private theorem actualInverse_right_local (D : LatticeData) (hu : IsUnit D.G.det) :
    gramComplex D * actualInverse D = 1 := by
  have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℤ =>
    M.map (Int.castRingHom ℂ)) (Matrix.mul_nonsing_inv D.G hu)
  change D.G.map (Int.castRingHom ℂ) * (D.G⁻¹).map (Int.castRingHom ℂ) = 1
  rw [← Matrix.map_mul]
  simpa using h

theorem oddWeight_eq_two_energy (D : LatticeData) (d : OddMonomial D) :
    (oddWeight D d : ℂ) / 2 =
      ∑ x ∈ d.support, (d x : ℂ) * ((x.2 : ℂ) + 1 / 2) := by
  simp only [oddWeight, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_sum,
    Nat.cast_mul, omega]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  push_cast
  ring

def actualAmbientBasis (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.Basis (OddMonomial D × Half (groundRank D hu)) ℂ (ActualTensor D hu) :=
  (MvPolynomial.basisMonomials (Index D) ℂ).tensorProduct
    (Pi.basisFun ℂ (Half (groundRank D hu)))

theorem actual_basis_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (d : OddMonomial D) (b : Half (groundRank D hu)) :
    actualAmbientBasis D hu (d, b) =
      MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] Pi.single b (1 : ℂ) := by
  simp [actualAmbientBasis, Pi.basisFun_apply]

theorem actual_basis_eigenvalue (D : LatticeData) (hu : IsUnit D.G.det)
    (d : OddMonomial D) (b : Half (groundRank D hu)) :
    actualTensorL0 D hu (actualAmbientBasis D hu (d, b)) =
      ((D.rank : ℂ) / 16 + (oddWeight D d : ℂ) / 2) •
        actualAmbientBasis D hu (d, b) := by
  rw [actual_basis_apply]
  simp only [actualTensorL0, tensorL, tensorEnd, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rw [L_zero_monomial_coeff D (actualInverse D)
    (actualInverse_left_local D hu) (actualInverse_right_local D hu) d 1]
  rw [oddWeight_eq_two_energy, TensorProduct.smul_tmul']

theorem actualTensorL0_repr (D : LatticeData) (hu : IsUnit D.G.det)
    (v : ActualTensor D hu) (ib : OddMonomial D × Half (groundRank D hu)) :
    (actualAmbientBasis D hu).repr (actualTensorL0 D hu v) ib =
      ((D.rank : ℂ) / 16 + (oddWeight D ib.1 : ℂ) / 2) *
        (actualAmbientBasis D hu).repr v ib := by
  classical
  let b := actualAmbientBasis D hu
  have heigen (j : OddMonomial D × Half (groundRank D hu)) :
      actualTensorL0 D hu (b j) =
        ((D.rank : ℂ) / 16 + (oddWeight D j.1 : ℂ) / 2) • b j :=
    actual_basis_eigenvalue D hu j.1 j.2
  change b.repr (actualTensorL0 D hu v) ib =
    ((D.rank : ℂ) / 16 + (oddWeight D ib.1 : ℂ) / 2) * b.repr v ib
  conv_lhs => rw [← b.linearCombination_repr v]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    heigen, b.repr_self, Finsupp.smul_apply, smul_eq_mul]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single ib]
  · simp only [Finsupp.single_eq_same, mul_one]
    ring
  · intro j hj hne
    simp [Finsupp.single_apply, hne]
  · intro hn
    have hz := Finsupp.notMem_support_iff.mp hn
    simp [hz]

theorem actual_grade_mem_iff_repr_support (D : LatticeData)
    (hu : IsUnit D.G.det) (N : ℕ) (v : ActualTensor D hu) :
    v ∈ actualGrade D hu N ↔
      ∀ ib ∈ ((actualAmbientBasis D hu).repr v).support,
        oddWeight D ib.1 = N := by
  classical
  let b := actualAmbientBasis D hu
  simp only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro hv ib hib
    have hcoord := congrArg (fun x => (b.repr x) ib) hv
    rw [actualTensorL0_repr] at hcoord
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord
    have hnonzero : b.repr v ib ≠ 0 := Finsupp.mem_support_iff.mp hib
    have hscalar := mul_right_cancel₀ hnonzero hcoord
    have hc : (oddWeight D ib.1 : ℂ) = (N : ℂ) := by linear_combination 2 * hscalar
    exact_mod_cast hc
  · intro hv
    apply b.repr.injective
    ext ib
    rw [actualTensorL0_repr]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases h : b.repr v ib = 0
    · change ((D.rank : ℂ) / 16 + (oddWeight D ib.1 : ℂ) / 2) * b.repr v ib =
        ((D.rank : ℂ) / 16 + (N : ℂ) / 2) * b.repr v ib
      rw [h, mul_zero, mul_zero]
    · rw [hv ib (Finsupp.mem_support_iff.mpr h)]

def actualGradeVector (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    (x : OddFiber D N × Half (groundRank D hu)) : ActualTensor D hu :=
  actualAmbientBasis D hu (x.1.1, x.2)

theorem actualGradeVector_mem (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    (x : OddFiber D N × Half (groundRank D hu)) :
    actualGradeVector D hu N x ∈ actualGrade D hu N := by
  rw [actualGrade, LinearMap.mem_ker]
  simp only [actualGradeVector, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, actual_basis_eigenvalue]
  simp [x.1.2]

theorem actual_grade_span (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ) :
    actualGrade D hu N =
      Submodule.span ℂ (Set.range (actualGradeVector D hu N)) := by
  classical
  let b := actualAmbientBasis D hu
  have hset : Set.range (actualGradeVector D hu N) =
      b '' {ib | oddWeight D ib.1 = N} := by
    ext v
    constructor
    · rintro ⟨⟨d, c⟩, rfl⟩
      exact ⟨(d.1, c), d.2, rfl⟩
    · rintro ⟨⟨d, c⟩, hd, rfl⟩
      exact ⟨(⟨d, hd⟩, c), rfl⟩
  apply le_antisymm
  · intro v hv
    rw [hset, b.mem_span_image]
    exact (actual_grade_mem_iff_repr_support D hu N v).mp hv
  · apply Submodule.span_le.mpr
    rintro v ⟨x, rfl⟩
    exact actualGradeVector_mem D hu N x

def actualGroundInsert (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) :
    Module.End ℂ (ActualTensor D hu) :=
  TensorProduct.map LinearMap.id A

theorem actualTensorL0_groundInsert_commute (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) :
    actualTensorL0 D hu * actualGroundInsert D hu A =
      actualGroundInsert D hu A * actualTensorL0 D hu := by
  apply TensorProduct.ext'
  intro p g
  simp only [actualTensorL0, actualGroundInsert, tensorL, tensorEnd,
    Module.End.mul_apply, TensorProduct.map_tmul, LinearMap.id_apply]

theorem actualGroundInsert_preserves_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (A : Module.End ℂ (ActualGround D hu))
    (v : ActualTensor D hu) (hv : v ∈ actualGrade D hu N) :
    actualGroundInsert D hu A v ∈ actualGrade D hu N := by
  simp only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv ⊢
  have hc := LinearMap.congr_fun (actualTensorL0_groundInsert_commute D hu A) v
  change actualTensorL0 D hu (actualGroundInsert D hu A v) =
    actualGroundInsert D hu A (actualTensorL0 D hu v) at hc
  rw [hc, hv, map_smul]

def actualGroundInsertRestrict (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (A : Module.End ℂ (ActualGround D hu)) :
    Module.End ℂ (actualGrade D hu N) :=
  (actualGroundInsert D hu A).restrict (actualGroundInsert_preserves_grade D hu N A)

theorem actualGroundInsertRestrict_coe (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (A : Module.End ℂ (ActualGround D hu)) (v : actualGrade D hu N) :
    (actualGroundInsertRestrict D hu N A v : ActualTensor D hu) =
      actualGroundInsert D hu A v := rfl

abbrev ActualGradeIndex (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ) :=
  OddFiber D N × Half (groundRank D hu)

theorem actualGradeVector_linearIndependent (D : LatticeData)
    (hu : IsUnit D.G.det) (N : ℕ) :
    LinearIndependent ℂ (actualGradeVector D hu N) := by
  classical
  let b := actualAmbientBasis D hu
  have hinj : Function.Injective
      (fun x : ActualGradeIndex D hu N => (x.1.1, x.2)) := by
    rintro ⟨⟨d, hd⟩, c⟩ ⟨⟨e, he⟩, f⟩ h
    simpa only [Prod.mk.injEq, Subtype.mk.injEq] using h
  exact b.linearIndependent.comp _ hinj

def actualGradeBasis (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ) :
    Module.Basis (ActualGradeIndex D hu N) ℂ (actualGrade D hu N) :=
  (Module.Basis.span (actualGradeVector_linearIndependent D hu N)).map
    { toFun := fun v => ⟨v.1, by rw [actual_grade_span]; exact v.2⟩
      invFun := fun v => ⟨v.1, by rw [← actual_grade_span]; exact v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem actualGradeBasis_coe (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    (x : ActualGradeIndex D hu N) :
    (actualGradeBasis D hu N x : ActualTensor D hu) = actualGradeVector D hu N x := by
  simp [actualGradeBasis, Module.Basis.coe_span_apply]

instance actualGrade_module_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) : Module.Finite ℂ (actualGrade D hu N) :=
  Module.Finite.of_basis (actualGradeBasis D hu N)

theorem actual_grade_finrank_basis (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) :
    Module.finrank ℂ (actualGrade D hu N) =
      Fintype.card (ActualGradeIndex D hu N) := by
  classical
  letI : Finite (OddFiber D N) := oddFiber_finite D N
  letI : Fintype (OddFiber D N) := Fintype.ofFinite (OddFiber D N)
  rw [Module.finrank_eq_card_basis (actualGradeBasis D hu N)]

theorem actualGradeBasis_repr (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    (v : actualGrade D hu N) (x : ActualGradeIndex D hu N) :
    (actualGradeBasis D hu N).repr v x =
      (actualAmbientBasis D hu).repr (v : ActualTensor D hu) (x.1.1, x.2) := by
  classical
  let b := actualGradeBasis D hu N
  change b.repr v x = _
  have hv : (v : ActualTensor D hu) =
      ∑ y, b.repr v y • actualAmbientBasis D hu (y.1.1, y.2) := by
    have h := congrArg (fun w : actualGrade D hu N => (w : ActualTensor D hu))
      (b.sum_repr v)
    simpa only [b, Submodule.coe_sum, Submodule.coe_smul, actualGradeBasis_coe,
      actualGradeVector] using h.symm
  rw [hv]
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  have hinj (y : ActualGradeIndex D hu N) :
      (y.1.1, y.2) = (x.1.1, x.2) ↔ y = x := by
    rcases y with ⟨⟨d, hd⟩, c⟩
    rcases x with ⟨⟨e, he⟩, f⟩
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hinj]

theorem actual_grade_insert_trace (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (A : Module.End ℂ (ActualGround D hu)) :
    LinearMap.trace ℂ (actualGrade D hu N)
        (actualGroundInsertRestrict D hu N A) =
      (Fintype.card (OddFiber D N) : ℂ) *
        LinearMap.trace ℂ (ActualGround D hu) A := by
  classical
  let b := actualGradeBasis D hu N
  let g := Pi.basisFun ℂ (Half (groundRank D hu))
  rw [LinearMap.trace_eq_matrix_trace ℂ b,
    LinearMap.trace_eq_matrix_trace ℂ g]
  have hdiag (d : OddFiber D N) (c : Half (groundRank D hu)) :
      b.repr (actualGroundInsertRestrict D hu N A (b (d, c))) (d, c) =
        g.repr (A (g c)) c := by
    rw [actualGradeBasis_repr]
    rw [actualGroundInsertRestrict_coe, actualGradeBasis_coe]
    simp [actualGradeVector, actual_basis_apply, actualGroundInsert,
      actualAmbientBasis, g, MvPolynomial.basisMonomials, MvPolynomial.coeff_monomial]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  simp_rw [hdiag]
  simp [Fintype.sum_prod_type, Finset.mul_sum]

theorem actual_ground_finrank (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.finrank ℂ (ActualGround D hu) = 2 ^ (D.rank / 2) := by
  have h := Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))
  simpa [groundRank, ActualGround] using h.2.2.2.1

theorem actual_grade_finrank_factor (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) :
    Module.finrank ℂ (actualGrade D hu N) =
      Nat.card (OddFiber D N) * 2 ^ (D.rank / 2) := by
  classical
  rw [actual_grade_finrank_basis, Fintype.card_prod]
  have hcard : Fintype.card (Half (groundRank D hu)) = 2 ^ (D.rank / 2) := by
    rw [← Module.finrank_fintype_fun_eq_card ℂ]
    exact actual_ground_finrank D hu
  rw [hcard, Nat.card_eq_fintype_card]

def bRank (r N : ℕ) : ℕ :=
  D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.partitionCount r N

theorem actual_odd_fiber_card_bRank (D : LatticeData) (N : ℕ) :
    Nat.card (OddFiber D N) = bRank D.rank N := by
  exact D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.card_colouredFiber D.rank N

theorem actual_grade_finrank_bRank (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) :
    Module.finrank ℂ (actualGrade D hu N) = 2 ^ (D.rank / 2) * bRank D.rank N := by
  rw [actual_grade_finrank_factor, actual_odd_fiber_card_bRank, mul_comm]

theorem actual_grade_insert_trace_bRank (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (A : Module.End ℂ (ActualGround D hu)) :
    LinearMap.trace ℂ (actualGrade D hu N) (actualGroundInsertRestrict D hu N A) =
      (bRank D.rank N : ℂ) * LinearMap.trace ℂ (ActualGround D hu) A := by
  rw [actual_grade_insert_trace, ← Nat.card_eq_fintype_card, actual_odd_fiber_card_bRank]

theorem actual_rank24_grade_one_finrank_98304 (D : LatticeData)
    (hu : IsUnit D.G.det) (h24 : D.rank = 24) :
    actualGrade D hu 1 = LinearMap.ker
      (actualTensorL0 D hu - (2 : ℂ) • (LinearMap.id : Module.End ℂ (ActualTensor D hu))) ∧
    Module.finrank ℂ (actualGrade D hu 1) = 98304 ∧
    (D.rank : ℚ) / 16 + 1 / 2 - (D.rank : ℚ) / 24 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [actualGrade, h24]
  · rw [actual_grade_finrank_bRank, h24]
    change 2 ^ (24 / 2) *
      D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.partitionCount 24 1 = 98304
    rw [(D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.partitionCount_small 24).2.1]
    norm_num
  · norm_num [h24]

def actualInsertedTraceSeries (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) : PowerSeries ℂ :=
  PowerSeries.mk (fun N =>
    LinearMap.trace ℂ (actualGrade D hu N) (actualGroundInsertRestrict D hu N A))

theorem actual_inserted_series_eq_genFun (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) :
    actualInsertedTraceSeries D hu A =
      PowerSeries.C (LinearMap.trace ℂ (ActualGround D hu) A) *
        Nat.Partition.genFun (fun k m =>
          (D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.oddColourFactor
            D.rank k m : ℂ)) := by
  classical
  rw [← D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.colouredFiberSeries_eq_genFun
    ℂ D.rank]
  ext N
  rw [actualInsertedTraceSeries, PowerSeries.coeff_mk, actual_grade_insert_trace_bRank,
    PowerSeries.coeff_C_mul,
    D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredFiberSeries,
    PowerSeries.coeff_mk,
    D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.card_colouredFiber]
  exact mul_comm _ _

theorem actual_inserted_series_eq_odd_product (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) :
    actualInsertedTraceSeries D hu A =
      PowerSeries.C (LinearMap.trace ℂ (ActualGround D hu) A) *
        ∏' n : ℕ, (((1 : PowerSeries ℂ) - PowerSeries.X ^ (2*n+1))⁻¹) ^ D.rank := by
  rw [actual_inserted_series_eq_genFun,
    (D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.hasProd_partitionGenFun D.rank).tprod_eq]

theorem actual_quotient_charge_ground_trace_zero (D : LatticeData)
    (hu : IsUnit D.G.det) (x : Extension D ⧸ K D)
    (hx : quotientCharge D x ≠ 0) :
    LinearMap.trace ℂ (ActualGround D hu) (groundRepresentation D hu x) = 0 := by
  have h := Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))
  exact nonzero_charge_trace D hu (groundRepresentation D hu)
    h.2.2.1 x hx

theorem actual_quotient_charge_grade_trace_zero (D : LatticeData)
    (hu : IsUnit D.G.det) (N : ℕ) (x : Extension D ⧸ K D)
    (hx : quotientCharge D x ≠ 0) :
    LinearMap.trace ℂ (actualGrade D hu N)
        (actualGroundInsertRestrict D hu N (groundRepresentation D hu x)) = 0 := by
  rw [actual_grade_insert_trace_bRank, actual_quotient_charge_ground_trace_zero D hu x hx,
    mul_zero]

end D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
