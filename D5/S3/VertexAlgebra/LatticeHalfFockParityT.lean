/- GID: D5/S3/VertexAlgebra/LatticeHalfFockParityT
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockParityT
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual oscillator parity on every finite half-Fock grade and its inserted trace.
-/

import D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
import D5.S3.VertexAlgebra.LatticeInvolution

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeHalfFockParityT

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients
open LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient TwistedGround.OperatorAlgebra
open D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
open D5.S3.VertexAlgebra.LatticeInvolution
open D5.S3.VertexAlgebra.LatticeAllStateField
open MvPolynomial

/-! The oscillator involution is tensored with the genuine ground identity. -/

def actualParity (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (ActualTensor D hu) :=
  TensorProduct.map (sigmaLinear D)
    (LinearMap.id : Module.End ℂ (ActualGround D hu))

private theorem oddWeight_mod_two (D : LatticeData) (d : OddMonomial D) :
    oddWeight D d % 2 = (occurrences D d).length % 2 := by
  induction d using Finsupp.induction with
  | zero => simp [oddWeight, occurrences, Finsupp.weight_apply]
  | single_add a n d ha hne ih =>
      change Finsupp.weight (omega D) (Finsupp.single a n + d) % 2 = _
      rw [map_add, Finsupp.weight_single]
      simp only [nsmul_eq_mul]
      simp only [occurrences, Finsupp.toMultiset_add,
        Finsupp.toMultiset_single, Multiset.length_toList,
        Multiset.card_add, Multiset.card_nsmul, Multiset.card_singleton]
      simp only [Nat.cast_id, mul_one]
      rw [show Finsupp.weight (omega D) d = oddWeight D d by rfl]
      have hlen : (Finsupp.toMultiset d).card = (occurrences D d).length := by
        simp [occurrences]
      rw [hlen]
      rw [Nat.add_mod, Nat.add_mod, ih]
      have hodd : (n * omega D a) % 2 = n % 2 := by
        simp [omega, Nat.mul_mod]
      rw [hodd]
      omega

private theorem oddWeight_sign (D : LatticeData) (d : OddMonomial D) :
    (-1 : ℂ) ^ oddWeight D d = (-1 : ℂ) ^ (occurrences D d).length := by
  calc
    (-1 : ℂ) ^ oddWeight D d = (-1 : ℂ) ^ (oddWeight D d % 2) :=
      neg_one_pow_eq_pow_mod_two _
    _ = (-1 : ℂ) ^ ((occurrences D d).length % 2) := by
      rw [oddWeight_mod_two]
    _ = (-1 : ℂ) ^ (occurrences D d).length := by
      symm
      exact neg_one_pow_eq_pow_mod_two _

theorem actualParity_on_grade_basis (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (x : ActualGradeIndex D hu N) :
    actualParity D hu (actualGradeBasis D hu N x : ActualTensor D hu) =
      ((-1 : ℂ) ^ N) • (actualGradeBasis D hu N x : ActualTensor D hu) := by
  rw [actualGradeBasis_coe, actualGradeVector, actual_basis_apply]
  simp only [actualParity, TensorProduct.map_tmul, LinearMap.id_apply]
  change sigma D (monomial (x.1.1 : OddMonomial D) 1) ⊗ₜ[ℂ] _ = _
  rw [sigma_monomial, ← oddWeight_sign D x.1.1]
  rw [x.1.2]
  simp only [TensorProduct.smul_tmul']

theorem actualParity_on_actualGrade (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (v : actualGrade D hu N) :
    actualParity D hu (v : ActualTensor D hu) =
      ((-1 : ℂ) ^ N) • (v : ActualTensor D hu) := by
  let b := actualGradeBasis D hu N
  let f : actualGrade D hu N →ₗ[ℂ] ActualTensor D hu :=
    (actualParity D hu).comp (actualGrade D hu N).subtype
  let g : actualGrade D hu N →ₗ[ℂ] ActualTensor D hu :=
    ((-1 : ℂ) ^ N) • (actualGrade D hu N).subtype
  have hfg : f = g := by
    apply b.ext
    intro x
    exact actualParity_on_grade_basis D hu N x
  exact LinearMap.congr_fun hfg v

theorem actualParity_preserves_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (v : ActualTensor D hu) (hv : v ∈ actualGrade D hu N) :
    actualParity D hu v ∈ actualGrade D hu N := by
  have hp := actualParity_on_actualGrade D hu N ⟨v, hv⟩
  rw [hp]
  exact Submodule.smul_mem _ _ hv

def actualParityGroundInsertRestrict (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (A : Module.End ℂ (ActualGround D hu)) :
    Module.End ℂ (actualGrade D hu N) :=
  ((actualParity D hu).comp (actualGroundInsert D hu A)).restrict
    (fun v hv => actualParity_preserves_grade D hu N
      (actualGroundInsert D hu A v)
      (actualGroundInsert_preserves_grade D hu N A v hv))

theorem actualParityGroundInsertRestrict_coe
    (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    (A : Module.End ℂ (ActualGround D hu)) (v : actualGrade D hu N) :
    (actualParityGroundInsertRestrict D hu N A v : ActualTensor D hu) =
      actualParity D hu (actualGroundInsert D hu A v) := rfl

theorem actualParityGroundInsertRestrict_eq_smul
    (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    (A : Module.End ℂ (ActualGround D hu)) :
    actualParityGroundInsertRestrict D hu N A =
      ((-1 : ℂ) ^ N) • actualGroundInsertRestrict D hu N A := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [actualParityGroundInsertRestrict_coe]
  change actualParity D hu (actualGroundInsert D hu A v) =
    ((-1 : ℂ) ^ N) • actualGroundInsert D hu A v
  exact actualParity_on_actualGrade D hu N
    ⟨actualGroundInsert D hu A v,
      actualGroundInsert_preserves_grade D hu N A v (by exact v.property)⟩

theorem actualParityTraceTerm_eq (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (A : Module.End ℂ (ActualGround D hu)) :
    LinearMap.trace ℂ (actualGrade D hu N)
        (actualParityGroundInsertRestrict D hu N A) =
      ((-1 : ℂ) ^ N) *
        LinearMap.trace ℂ (actualGrade D hu N)
          (actualGroundInsertRestrict D hu N A) := by
  rw [actualParityGroundInsertRestrict_eq_smul]
  change LinearMap.trace ℂ (actualGrade D hu N)
      (((-1 : ℂ) ^ N) • actualGroundInsertRestrict D hu N A) = _
  simp [smul_eq_mul]

theorem actualParityTraceTerm_eq_bRank (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (A : Module.End ℂ (ActualGround D hu)) :
    LinearMap.trace ℂ (actualGrade D hu N)
        (actualParityGroundInsertRestrict D hu N A) =
      ((-1 : ℂ) ^ N) *
        (bRank D.rank N : ℂ) * LinearMap.trace ℂ (ActualGround D hu) A := by
  rw [actualParityTraceTerm_eq, actual_grade_insert_trace_bRank]
  ring

end D5.S3.VertexAlgebra.LatticeHalfFockParityT
