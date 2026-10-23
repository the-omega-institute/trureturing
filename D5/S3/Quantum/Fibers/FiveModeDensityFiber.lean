/- GID: D5/S3/Quantum/Fibers/FiveModeDensityFiber
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/FiveModeDensityFiber
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Full-rank five-mode density fibres have 21 real local directions and distinguish coherence. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Fibers.FiveModeDensityFiber

open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition

private def coordinate (i : Fin 5) : traceZeroHermitian 5 →ₗ[ℝ] ℝ where
  toFun A := (A.1.1 i i).re
  map_add' A B := by simp [add_apply, Complex.add_re]
  map_smul' r A := by simp [smul_apply, Complex.mul_re]

/-- Three means of any Hermitian matrix, ordered as X, Z, Y. -/
def means (ρ : Matrix (Fin 5) (Fin 5) ℂ) : Fin 3 → ℝ :=
  ![(ρ 1 1).re + (ρ 4 4).re, (ρ 2 2).re, (ρ 3 3).re + (ρ 4 4).re]

def modeReadout : traceZeroHermitian 5 →ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearMap.pi (fun j : Fin 3 =>
    match j with
    | 0 => coordinate 1 + coordinate 4
    | 1 => coordinate 2
    | 2 => coordinate 3 + coordinate 4)

private theorem modeReadout_apply (A : traceZeroHermitian 5) :
    modeReadout A = means A.1.1 := by
  funext j
  fin_cases j <;> rfl

private def diagonalWitness (x : Fin 3 → ℝ) : traceZeroHermitian 5 := by
  let values : Fin 5 → ℝ := fun i =>
    if i = 0 then -(x 0 + x 1 + x 2)
    else if i = 1 then x 0
    else if i = 2 then x 1
    else if i = 3 then x 2
    else 0
  let H : HermitianSpace 5 :=
    ⟨Matrix.diagonal (fun i => (values i : ℂ)), by
      apply Matrix.isHermitian_diagonal_of_self_adjoint
      ext i
      simp⟩
  refine ⟨H, ?_⟩
  change Matrix.trace H.1 = 0
  simp [H, values, Matrix.trace, Fin.sum_univ_succ]
  ring

private theorem modeReadout_surjective : Function.Surjective modeReadout := by
  intro x
  refine ⟨diagonalWitness x, ?_⟩
  funext j
  rw [modeReadout_apply]
  fin_cases j <;> norm_num +decide [means, diagonalWitness, Matrix.diagonal] <;> rfl

private theorem five_mode_tangent_fibre_finrank :
    Module.finrank ℝ (LinearMap.ker modeReadout) = 21 := by
  have hrange : LinearMap.range modeReadout = ⊤ := by
    apply (eq_top_iff).2
    intro y _
    obtain ⟨x, hx⟩ := modeReadout_surjective y
    exact ⟨x, hx⟩
  have hsum := modeReadout.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, trace_zero_hermitian_finrank] at hsum
  norm_num [Module.finrank_fin_fun] at hsum ⊢
  omega

def fiveModeCenter : Matrix (Fin 5) (Fin 5) ℂ :=
  (5 : ℝ)⁻¹ • (1 : Matrix (Fin 5) (Fin 5) ℂ)

/-- The affine-fibre coordinates are the genuine trace-zero kernel, restricted by PSD. -/
def fibrePoint (ρ : Matrix (Fin 5) (Fin 5) ℂ) (h : LinearMap.ker modeReadout) :=
  ρ + h.1.1.1

private theorem fibrePoint_constraints (ρ : Matrix (Fin 5) (Fin 5) ℂ)
    (h : LinearMap.ker modeReadout) :
    Matrix.trace (fibrePoint ρ h) = Matrix.trace ρ ∧ means (fibrePoint ρ h) = means ρ := by
  constructor
  · rw [fibrePoint, Matrix.trace_add]
    have ht : Matrix.trace h.1.1.1 = 0 := h.1.2
    simp [ht]
  · have hk : modeReadout h.1 = 0 := h.2
    funext j
    have hj := congrArg (fun f : Fin 3 → ℝ => f j) hk
    rw [modeReadout_apply] at hk
    have hj := congrArg (fun f : Fin 3 → ℝ => f j) hk
    fin_cases j <;> simp [means, fibrePoint] at hj ⊢ <;> linarith

private theorem affine_fibre_coordinates (ρ : Matrix (Fin 5) (Fin 5) ℂ)
    (hρ : ρ.IsHermitian) (ht : Matrix.trace ρ = 1)
    (σ : Matrix (Fin 5) (Fin 5) ℂ) (hσ : σ.IsHermitian) :
    (Matrix.trace σ = 1 ∧ means σ = means ρ) ↔
      ∃! h : LinearMap.ker modeReadout, σ = fibrePoint ρ h := by
  constructor
  · intro hs
    let A : traceZeroHermitian 5 := ⟨⟨σ - ρ, hσ.sub hρ⟩, by
      change Matrix.trace (σ - ρ) = 0
      rw [Matrix.trace_sub, hs.1, ht, sub_self]⟩
    have hk : A ∈ LinearMap.ker modeReadout := by
      rw [LinearMap.mem_ker, modeReadout_apply]
      funext j
      have hj := congrFun hs.2 j
      fin_cases j <;> simp [means, A, Complex.sub_re] at hj ⊢ <;> linarith
    let h : LinearMap.ker modeReadout := ⟨A,hk⟩
    have he : σ = fibrePoint ρ h := by simp [fibrePoint,h,A]
    refine ⟨h,he,?_⟩
    intro k hk
    have heq : k.1.1.1 = h.1.1.1 := add_left_cancel (hk.symm.trans he)
    exact Subtype.ext (Subtype.ext (Subtype.ext heq))
  · rintro ⟨h,he,_⟩
    rw [he]
    exact ⟨(fibrePoint_constraints ρ h).1.trans ht,(fibrePoint_constraints ρ h).2⟩

/-- Every full-rank point has a PSD neighborhood inside its 21-dimensional affine fibre.
The norm is the operator norm of the C-star matrix, not an entrywise proxy. -/
theorem full_rank_local_fibre (ρ : Matrix (Fin 5) (Fin 5) ℂ)
    (hρ : ρ.PosDef) (ht : Matrix.trace ρ = 1) :
    Module.finrank ℝ (LinearMap.ker modeReadout) = 21 ∧
    (∀ σ : Matrix (Fin 5) (Fin 5) ℂ, σ.IsHermitian →
      ((Matrix.trace σ = 1 ∧ means σ = means ρ) ↔
        ∃! h : LinearMap.ker modeReadout, σ = fibrePoint ρ h)) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : LinearMap.ker modeReadout,
      ‖CStarMatrix.ofMatrix h.1.1.1‖ < ε →
      (fibrePoint ρ h).PosDef ∧ Matrix.trace (fibrePoint ρ h) = 1 ∧
        means (fibrePoint ρ h) = means ρ := by
  refine ⟨five_mode_tangent_fibre_finrank,
    affine_fibre_coordinates ρ hρ.isHermitian ht, ?_⟩
  have hs := hρ.isStrictlyPositive
  obtain ⟨ε, hε, hbound⟩ := (CFC.exists_pos_algebraMap_le_iff ρ hs.isSelfAdjoint).mpr
    (fun x hx => hs.spectrum_pos hx)
  refine ⟨ε, hε, fun h hh => ?_⟩
  have hherm : IsSelfAdjoint (CStarMatrix.ofMatrix h.1.1.1) := h.1.1.2
  have hlo := hherm.neg_algebraMap_norm_le_self
  let φ := CStarMatrix.ofMatrixStarAlgEquiv (n := Fin 5) (A := ℂ)
  have scalar (t : ℝ) : φ (t • (1 : Matrix (Fin 5) (Fin 5) ℂ)) =
      algebraMap ℝ (CStarMatrix (Fin 5) (Fin 5) ℂ) t := by
    ext i j
    change (t • (1 : Matrix (Fin 5) (Fin 5) ℂ)) i j = _
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply, CStarMatrix.one_apply]
  have hb : algebraMap ℝ (CStarMatrix (Fin 5) (Fin 5) ℂ) ε ≤ φ ρ := by
    rw [Algebra.algebraMap_eq_smul_one] at hbound
    have hm : (0 : CStarMatrix (Fin 5) (Fin 5) ℂ) ≤ φ (ρ - ε • 1) :=
      map_nonneg φ (sub_nonneg.mpr hbound)
    rw [map_sub, scalar] at hm
    exact sub_nonneg.mp hm
  have hsmallMatrix : ((ε - ‖CStarMatrix.ofMatrix h.1.1.1‖) •
      (1 : Matrix (Fin 5) (Fin 5) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (sub_pos.mpr hh)
  have hsmall : IsStrictlyPositive
      (algebraMap ℝ (CStarMatrix (Fin 5) (Fin 5) ℂ) (ε - ‖CStarMatrix.ofMatrix h.1.1.1‖)) := by
    have hunit := hsmallMatrix.isUnit.map φ.toRingHom
    have hn : (0 : CStarMatrix (Fin 5) (Fin 5) ℂ) ≤
        φ ((ε - ‖CStarMatrix.ofMatrix h.1.1.1‖) • (1 : Matrix (Fin 5) (Fin 5) ℂ)) :=
      map_nonneg φ hsmallMatrix.posSemidef.nonneg
    rw [← scalar]
    exact hunit.isStrictlyPositive hn
  have hres : IsStrictlyPositive (φ (fibrePoint ρ h)) := by
    apply hsmall.of_le
    rw [map_sub]
    change algebraMap ℝ _ ε - algebraMap ℝ _ ‖CStarMatrix.ofMatrix h.1.1.1‖ ≤
      φ ρ + CStarMatrix.ofMatrix h.1.1.1
    exact add_le_add hb hlo
  have hp : (fibrePoint ρ h).PosDef := by
    have hn : (0 : Matrix (Fin 5) (Fin 5) ℂ) ≤ fibrePoint ρ h := map_nonneg φ.symm hres.nonneg
    exact Matrix.IsStrictlyPositive.posDef ((hres.isUnit.map φ.symm.toRingHom).isStrictlyPositive hn)
  exact ⟨hp, (fibrePoint_constraints ρ h).1.trans ht, (fibrePoint_constraints ρ h).2⟩

#print axioms full_rank_local_fibre
end D5.S3.Quantum.Fibers.FiveModeDensityFiber
