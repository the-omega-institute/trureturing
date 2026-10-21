import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CirculantCharpoly
import Reg.Support.SingleDependentReadout

/-! Source registrations for Fourier eigenvalues and circulant characteristic factors. -/

namespace Reg.D5.S3.Quantum.Matrix.CirculantCharpoly
open _root_.D5.S3.Quantum.Matrix.CirculantCharpoly
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial Finset Complex
open _root_.Matrix
open scoped BigOperators
noncomputable section

namespace RealFactors
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ → ℝ) (fun _ => ℝ[X])

def actual : Realization signature :=
  realize signature (fun _ m f => (realCirculant m f).charpoly) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ m f => (realCirculant m f).charpoly + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (f : ℕ → ℝ)
    (_hf : ∀ k ∈ Icc 1 (2 * m), f (2 * m + 1 - k) = f k),
    R.readout () m f = (X - C (cosineValue m f 0)) *
      ∏ j ∈ Icc 1 m, (X - C (cosineValue m f j)) ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 (fun _ => 0) (by simp)
  change (realCirculant 0 (fun _ => 0)).charpoly + 1 = _ at hh
  rw [realCirculant_charpoly 0 (fun _ => 0) (by simp)] at hh
  exact one_ne_zero (add_left_cancel (hh.trans (add_zero _).symm))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro h
  have h0 : realCirculant 0 (0 : ℕ → ℝ) = 0 := by ext i j; simp [realCirculant]
  have h1 : realCirculant 0 (1 : ℕ → ℝ) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [realCirculant]
  change (realCirculant 0 (0 : ℕ → ℝ)).charpoly =
    (realCirculant 0 (1 : ℕ → ℝ)).charpoly at h
  rw [h0, h1, Matrix.charpoly_zero, Matrix.charpoly_one] at h
  have he := congrArg (Polynomial.eval 0) h
  norm_num at he

def source : Registration arena (type_of% @realCirculant_charpoly) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@realCirculant_charpoly, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@realCirculant_charpoly) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CirculantCharpoly.RealFactors.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CirculantCharpoly.RealFactors.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m f => (realCirculant m f).charpoly) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CirculantCharpoly
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end RealFactors

end

end Reg.D5.S3.Quantum.Matrix.CirculantCharpoly
