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

namespace Eigenvectors
abbrev parameters := Σ n : ℕ, Fin n

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature parameters
    (fun p => Fin p.1 → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p v => fourierValue v p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p v => fourierValue v p.2 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} [NeZero n] (v : Fin n → ℂ) (j : Fin n),
    Matrix.circulant v *ᵥ fourierVector j = R.readout () ⟨n, j⟩ v • fourierVector j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congr_fun (h (n := 1) (fun _ => 0) 0) 0
  norm_num [rejected, realize, fourierValue, fourierVector, Matrix.mulVec,
    dotProduct, Matrix.circulant_apply] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  change fourierValue (fun _ : Fin 1 => (0 : ℂ)) 0 ≠
    fourierValue (fun _ : Fin 1 => (1 : ℂ)) 0
  norm_num [fourierValue]

def source : Registration arena (type_of% @circulant_mulVec_fourier) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@circulant_mulVec_fourier, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@circulant_mulVec_fourier) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CirculantCharpoly.Eigenvectors.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CirculantCharpoly.Eigenvectors.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => fourierValue v p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CirculantCharpoly
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Eigenvectors

namespace ComplexFactors
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun n => Fin n → ℂ) (fun _ => ℂ[X])

def actual : Realization signature :=
  realize signature (fun _ _ v => (Matrix.circulant v).charpoly) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ v => (Matrix.circulant v).charpoly + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} [NeZero n] (v : Fin n → ℂ),
    R.readout () n v = ∏ j : Fin n, (X - C (fourierValue v j))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 1) (fun _ => 0)
  change (Matrix.circulant (fun _ : Fin 1 => (0 : ℂ))).charpoly + 1 = _ at hh
  rw [circulant_charpoly] at hh
  exact one_ne_zero (add_left_cancel (hh.trans (add_zero _).symm))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have hc : Matrix.circulant (1 : Fin 1 → ℂ) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  change (Matrix.circulant (0 : Fin 1 → ℂ)).charpoly =
    (Matrix.circulant (1 : Fin 1 → ℂ)).charpoly at h
  rw [Matrix.circulant_zero, hc, Matrix.charpoly_zero, Matrix.charpoly_one] at h
  have he := congrArg (Polynomial.eval 0) h
  norm_num at he

def source : Registration arena (type_of% @circulant_charpoly) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@circulant_charpoly, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@circulant_charpoly) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CirculantCharpoly.ComplexFactors.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CirculantCharpoly.ComplexFactors.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => (Matrix.circulant v).charpoly) (fun e => nomatch e))
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
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ComplexFactors

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
