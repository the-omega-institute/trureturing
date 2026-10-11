import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay
open LeanInformationAudit Set

noncomputable section
namespace Reg.D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ)
    (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p f => ∫ x in p.1..p.2, f x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {F H : ℝ → ℝ → ℝ} {a b t δ : ℝ}
    (_hab : a ≤ b) (_hδ : 0 < δ)
    (_hF : ContinuousOn F.uncurry (Icc (t-δ) (t+δ) ×ˢ Icc a b))
    (_hH : ContinuousOn H.uncurry (Icc (t-δ) (t+δ) ×ˢ Icc a b))
    (_hd : ∀ s ∈ Ioo (t-δ) (t+δ), ∀ x ∈ Icc a b,
      HasDerivAt (fun r => F r x) (H s x) s),
    HasDerivAt (fun s => ∫ x in a..b, F s x) (R.readout () ⟨a,b⟩ (H t)) t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (F := fun s _ => s) (H := fun _ _ => 1)
    (a := 0) (b := 1) (t := 0) (δ := 1)
    (by norm_num) (by norm_num)
    continuous_fst.continuousOn continuous_const.continuousOn
    (by intro s _ x _; exact hasDerivAt_id s)
  have hh' : HasDerivAt (fun s : ℝ => s) 0 0 := by
    simpa [rejected, realize] using hh
  have he := hh'.unique (hasDerivAt_id 0)
  norm_num at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def evidence : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deriv_integral_compact, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay.deriv_integral_compact)
    (type_of% (realize signature (fun _ p f => ∫ x in p.1..p.2, f x)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay.compact_integral_unit
  realizationName := `Reg.D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => ∫ x in p.1..p.2, f x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay
