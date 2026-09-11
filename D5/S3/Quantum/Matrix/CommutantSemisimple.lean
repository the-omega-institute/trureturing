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

open scoped ComplexOrder
namespace D5.S3.Quantum.Matrix.CommutantSemisimple

open D5.S3.Quantum.Matrix.RecordCapacity

set_option autoImplicit false

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
  apply (Subalgebra.mem_centralizer_iff ℂ).mpr
  rintro _ ⟨g, rfl⟩
  have hx := (Subalgebra.mem_centralizer_iff ℂ).mp hX (U g⁻¹) ⟨g⁻¹, rfl⟩
  have hs := congrArg Matrix.conjTranspose hx
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hinv,
    Matrix.conjTranspose_conjTranspose] at hs
  exact hs.symm

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

end D5.S3.Quantum.Matrix.CommutantSemisimple
