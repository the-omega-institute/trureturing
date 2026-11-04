import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.OneSidedGoldenHistory
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Measurement.OneSidedGoldenHistory
open _root_.D5.S3.Quantum.Measurement.OneSidedGoldenHistory
open _root_.D5.S3.ObserverMemory.Prediction.OneSidedPredictorMinimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder
noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ d : ℕ, Σ _ : Matrix (Fin d) (Fin d) ℂ, DensityState (Fin d)
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p h => mass p.2.1 (CStarMatrix.ofMatrix.symm p.2.2.val) h) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P*P=P) (hPh : P.IsHermitian) (ρ : DensityState (Fin d))
    (hq : 0 < (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re ∧
      (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re < 1),
    let state := CStarMatrix.ofMatrix.symm ρ.val
    let q := (Matrix.trace (P*state)).re
    (∀ h, 0 < R.readout () ⟨d,P,ρ⟩ h ∧
      nextZero P state h = if false ∈ h then x else ageProbability q h.length) ∧
    (∀ n, mass P state (List.replicate n true) = q+(1-q)*x^(2*n) ∧
      posterior P state (List.replicate n true) = q/(q+(1-q)*x^(2*n))) ∧
    (∀ ε : ℝ, 0 < ε → ε < x/2 → ∃ N : ℕ, N = cutoff q ε ∧
      (∀ n, ageProbability q n ≤ 2*ε ↔ N ≤ n) ∧
      (∃ M : Predictor (Fin (N+1) ⊕ Unit), NativeCorrect M P ρ ε) ∧
      Fintype.card (Fin (N+1) ⊕ Unit) = N+2 ∧
      ∀ (S : Type u) [Fintype S] (M : Predictor S), NativeCorrect M P ρ ε → N+2 ≤ Fintype.card S) ∧
    (∀ ε : ℝ, x/2 ≤ ε → ∃ M : Predictor Unit, NativeCorrect M P ρ ε) ∧
    (∀ (S : Type u) [Fintype S] (M : Predictor S), ¬ NativeCorrect M P ρ 0) ∧
    ((kraus P false).conjTranspose * kraus P false +
      (kraus P true).conjTranspose * kraus P true = 1) ∧
    (∀ b, nativePort P b = zeta^2 • kraus P b) ∧
    (∀ b σ, nativePort P b * σ * (nativePort P b).conjTranspose = branch P b σ) ∧
    (∀ h, false ∈ h → posterior P state h = 0)

private def projection : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0,1]
private def density : DensityState (Fin 2) :=
  ⟨(1/2 : ℝ) • (1 : CStarMatrix (Fin 2) (Fin 2) ℂ),
    smul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) zero_le_one,
    by
      unfold Matrix.trace
      rw [Fin.sum_univ_two]
      change ((1/2 : ℝ) • (1 : ℂ)) + ((1/2 : ℝ) • (1 : ℂ)) = 1
      norm_num⟩
private theorem projection_idem : projection*projection=projection := by
  simp [projection,Matrix.diagonal_mul_diagonal]
private theorem projection_hermitian : projection.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [projection,Matrix.conjTranspose_apply]
private theorem qvalue : (Matrix.trace (projection*CStarMatrix.ofMatrix.symm density.val)).re = 1/2 := by
  norm_num [projection,density,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,
    Matrix.smul_apply,Matrix.one_apply,Matrix.diagonal_apply]
private theorem qrange : 0 < (Matrix.trace (projection*CStarMatrix.ofMatrix.symm density.val)).re ∧
    (Matrix.trace (projection*CStarMatrix.ofMatrix.symm density.val)).re < 1 := by
  rw [qvalue]
  norm_num

theorem bad_law : ¬ arena.{u}.Law bad := by
  intro h
  have hh := (h projection projection_idem projection_hermitian density qrange).1 []
  norm_num [bad,realize] at hh

def evidence : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_predictor_minimum.{u},bad,bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_law
  dependence := by
    intro i
    let p : signature.Params := ⟨2,projection,density⟩
    refine ⟨p,[],[true],?_⟩
    intro h
    change mass projection _ [] = mass projection _ [true] at h
    have hl := (native_predictor_minimum.{u} projection projection_idem projection_hermitian density qrange).2.1
    have h0 := (hl 0).1
    have h1 := (hl 1).1
    norm_num [qvalue] at h0 h1
    rw [h0,h1] at h
    have hx : 0 < x ∧ x < 1 :=
      ⟨inv_pos.mpr Real.goldenRatio_pos, inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio⟩
    nlinarith [mul_pos hx.1 (sub_pos.mpr hx.2)]


#print axioms evidence
end
end Reg.D5.S3.Quantum.Measurement.OneSidedGoldenHistory
