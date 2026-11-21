import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.InverseFourierSupport

/-! The inverse uses the angular-to-cycles frequency restriction. -/

noncomputable section

open Complex MeasureTheory LeanInformationAudit
open _root_.Reg.Support
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.InverseFourierSupport
open scoped ENNReal

namespace Reg.D5.S3.Fourier.InverseFourierSupport

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ) (fun _ => ℝ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ F => frequencyRestriction F) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {F : ℂ → ℂ} {a C : ℝ} {m : ℕ}
    (_hF : Differentiable ℂ F)
    (_h₂ : MemLp (fun x : ℝ => F (x : ℂ)) 2 volume)
    (_hbound : ∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (a * |z.im|)),
    let g := R.readout () () F
    ∃ hg : MemLp g 2 volume,
      ∀ᵐ t : ℝ, a < |t| → ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (hg.toLp g)) t = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hg, _⟩ := h (F := fun _ => 0) (a := 0) (C := 1) (m := 0)
    (differentiable_const (0 : ℂ)) (by simp) (by simp)
  have hconst : MemLp (fun _ : ℝ => (1 : ℂ)) 2 volume := hg
  simpa [memLp_const_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top,
    Real.volume_univ] using hconst

def family : Registration arena (type_of% @inverse_fourier_L2_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inverse_fourier_L2_support, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have hz := congrFun h 0
    change frequencyRestriction (fun _ => 0) 0 = frequencyRestriction (fun _ => 1) 0 at hz
    simp [frequencyRestriction] at hz

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@inverse_fourier_L2_support) (Realization signature) Type Unit where
  unitName := `D5.S3.Fourier.InverseFourierSupport.inverse_fourier_L2_support.__information_unit
  realizationName := `Reg.D5.S3.Fourier.InverseFourierSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => frequencyRestriction F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.InverseFourierSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Fourier.InverseFourierSupport
