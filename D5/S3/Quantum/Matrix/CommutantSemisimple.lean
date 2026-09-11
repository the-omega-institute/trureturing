/- GID: D5/S3/Quantum/Matrix/CommutantSemisimple
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CommutantSemisimple
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unitary matrix representations have semisimple commutants and record capacity bounds. -/

import D5.S3.Quantum.Matrix.RecordCapacity
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.Center
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Tactic.FinCases

open scoped ComplexOrder

namespace D5.S3.Quantum.Matrix.CommutantSemisimple

open D5.S3.Quantum.Matrix.RecordCapacity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A complex matrix subalgebra closed under adjoints has zero Jacobson radical. -/
theorem jacobson_eq_bot_of_conjTranspose_closed
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Subalgebra ℂ (Matrix n n ℂ))
    (hA : ∀ X ∈ A, X.conjTranspose ∈ A) : Ring.jacobson A = ⊥ := by
  have : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  apply le_antisymm _ bot_le
  intro X hX
  change X = 0
  let Y : A := ⟨X.val.conjTranspose, hA X.val X.property⟩
  have hYX : Y * X ∈ Ring.jacobson A := (Ring.jacobson A).mul_mem_left Y hX
  obtain ⟨k, hk⟩ := IsSemiprimaryRing.isNilpotent (R := A)
  have hn : IsNilpotent (Y * X) := by
    refine ⟨k, ?_⟩
    have hp := Ideal.pow_mem_pow hYX k
    rw [hk] at hp
    exact hp
  have hm : IsNilpotent (X.val.conjTranspose * X.val) := hn.map A.val.toRingHom
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hm).eq_zero
  exact Subtype.ext (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht)

/-- Adjoints preserve the commutant of an arbitrary unitary group representation. -/
theorem commutant_conjTranspose_mem_of_unitary
    {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ unitary (Matrix n n ℂ))
    {X : Matrix n n ℂ} (hX : X ∈ commutant U) : X.conjTranspose ∈ commutant U := by
  have hinv (g : G) : U g⁻¹ = (U g).conjTranspose := by
    calc
      U g⁻¹ = U g⁻¹ * (U g * (U g).conjTranspose) := by
        rw [← Matrix.star_eq_conjTranspose, Unitary.mul_star_self_of_mem (hU g), mul_one]
      _ = (U g).conjTranspose := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  exact Set.star_mem_centralizer' (fun _ ⟨g, hg⟩ =>
    hg ▸ ⟨g⁻¹, hinv g⟩) hX

/-- The commutant of a finite-dimensional unitary representation is semisimple. -/
theorem commutant_isSemisimpleRing_of_unitary
    {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ)
    (hU : ∀ g, U g ∈ unitary (Matrix n n ℂ)) :
    IsSemisimpleRing (commutant U) := by
  have : IsArtinianRing (commutant U) := IsArtinianRing.of_finite ℂ (commutant U)
  apply IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr
  exact jacobson_eq_bot_of_conjTranspose_closed (commutant U)
    (fun _ hX => commutant_conjTranspose_mem_of_unitary U hU hX)

/-- Unitarity supplies the semisimplicity needed for the sharp record capacity bound. -/
theorem unitary_commutant_has_record_capacity
    {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ unitary (Matrix n n ℂ)) :
    ∃ (k : ℕ) (m : Fin k → ℕ), (∀ b, NeZero (m b)) ∧
      Nonempty (commutant U ≃ₐ[ℂ] ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) ∧
      ∀ (I : Type) [Fintype I] (P : I → Matrix n n ℂ),
        CompleteOrthogonalIdempotents P → (∀ i, P i ≠ 0) →
        (∀ i g, P i * U g = U g * P i) → Fintype.card I ≤ ∑ b, m b := by
  have : IsSemisimpleRing (commutant U) := commutant_isSemisimpleRing_of_unitary U hU
  exact semisimple_commutant_has_record_capacity U

open _root_.Matrix

/-- The integer shear representation, with z acting by [[1,z],[0,1]]. -/
noncomputable def unipotentRepresentation : Multiplicative ℤ →* Matrix (Fin 2) (Fin 2) ℂ :=
  (Units.coeHom _).comp
    ((GeneralLinearGroup.upperRightHom (R := ℂ)).compAddMonoidHom
      (Int.castAddHom ℂ)).toMonoidHom

private theorem mem_unipotent_commutant_iff (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X ∈ commutant unipotentRepresentation ↔ X 1 0 = 0 ∧ X 0 0 = X 1 1 := by
  constructor
  · intro h
    have he := (Subalgebra.mem_centralizer_iff ℂ).mp h
      (unipotentRepresentation (Multiplicative.ofAdd 1)) ⟨_, rfl⟩
    have h00 := congrFun (congrFun he 0) 0
    have h01 := congrFun (congrFun he 0) 1
    simp [unipotentRepresentation, GeneralLinearGroup.upperRightHom, Matrix.mul_apply,
      Fin.sum_univ_two] at h00 h01
    exact ⟨h00, add_right_cancel (h01.symm.trans (add_comm _ _))⟩
  · rintro ⟨hc, hd⟩
    apply (Subalgebra.mem_centralizer_iff ℂ).mpr
    rintro _ ⟨z, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentRepresentation, GeneralLinearGroup.upperRightHom, Matrix.mul_apply,
        Fin.sum_univ_two, hc, hd, mul_comm, add_comm]

/-- The upper-right matrix unit in the shear commutant. -/
noncomputable def unipotentRadicalElement : commutant unipotentRepresentation :=
  ⟨!![0, 1; 0, 0], (mem_unipotent_commutant_iff _).mpr (by simp)⟩

/-- The nonzero upper-right matrix unit belongs to the Jacobson radical. -/
theorem unipotent_radical_element_mem :
    unipotentRadicalElement ∈ Ring.jacobson (commutant unipotentRepresentation) := by
  rw [← Ideal.jacobson_bot]
  apply Ideal.mem_jacobson_iff.mpr
  intro Y
  refine ⟨1 - Y * unipotentRadicalElement, ?_⟩
  rw [Ideal.mem_bot]
  apply Subtype.ext
  have hc := ((mem_unipotent_commutant_iff _).mp Y.property).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentRadicalElement, Matrix.mul_apply, Fin.sum_univ_two, hc]

/-- The upper-right matrix unit is nonzero in the shear commutant. -/
theorem unipotent_radical_element_ne_zero : unipotentRadicalElement ≠ 0 := by
  intro h
  have := congrArg (fun X : commutant unipotentRepresentation => X.val 0 1) h
  simp [unipotentRadicalElement] at this

/-- Omitting unitarity permits a nonsemisimple commutant, even for an integer action. -/
theorem unipotent_commutant_not_isSemisimpleRing :
    ¬ IsSemisimpleRing (commutant unipotentRepresentation) := by
  intro h
  have hz := IsSemisimpleRing.jacobson_eq_bot (commutant unipotentRepresentation)
  have hm := unipotent_radical_element_mem
  rw [hz] at hm
  exact unipotent_radical_element_ne_zero hm

/-- The shear commutant consists precisely of upper triangular matrices with equal diagonals. -/
theorem unipotent_commutant_characterization (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X ∈ commutant unipotentRepresentation ↔ ∃ a b : ℂ, X = !![a, b; 0, a] := by
  rw [mem_unipotent_commutant_iff]
  constructor
  · rintro ⟨hc, hd⟩
    refine ⟨X 0 0, X 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc, hd]
  · rintro ⟨a, b, rfl⟩
    simp

end D5.S3.Quantum.Matrix.CommutantSemisimple
