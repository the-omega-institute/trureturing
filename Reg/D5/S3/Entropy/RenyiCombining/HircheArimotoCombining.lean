import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.RenyiCombining.HircheArimotoCombining
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the complete Hirche threshold and combining claim. -/

namespace Reg.D5.S3.Entropy.RenyiCombining.HircheArimotoCombining
open _root_.D5.S3.Entropy.RenyiCombining.HircheArimotoCombining
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the threshold as real data at its strict lower bound. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ αhat => αhat) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve the threshold and both complete order ranges of the source claim. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∃ αhat : ℝ, 1 < R.readout () () αhat ∧ αhat < (15783 : ℝ) / 10000 ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ y ∈ I α,
      ConvexOn ℝ (I α) (fun x => G α x y)) ∧
    (∀ α : ℝ, 1 < α → α ≤ αhat → ∀ y ∈ I α,
      ConcaveOn ℝ (I α) (fun x => G α x y))

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨αhat, hlow, _⟩
  change (1 : ℝ) < 0 at hlow
  exact (by norm_num : ¬ (1 : ℝ) < 0) hlow

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize, claim] using result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Entropy.RenyiCombining.HircheArimotoCombining.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Entropy.RenyiCombining.HircheArimotoCombining.unit
  realizationName :=
    `Reg.D5.S3.Entropy.RenyiCombining.HircheArimotoCombining.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ αhat => αhat) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.HircheArimotoCombining
    definition := some {
      owner := `D5.S3.Entropy.RenyiCombining.HircheArimotoCombining
      name := `D5.S3.Entropy.RenyiCombining.HircheArimotoCombining.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev tanhSignature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def tanhActual : Realization tanhSignature :=
  realize tanhSignature (fun _ _ s => Real.tanh s) (fun e => nomatch e)

def tanhRejected : Realization tanhSignature :=
  realize tanhSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem tanhDependence : ObservationalDependence tanhSignature tanhActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Real.tanh 0 ≠ Real.tanh 1
  simpa using (tanh_mem zero_lt_one).1.ne

abbrev tanhMemArena : Arena where
  signature := tanhSignature
  Law R := ∀ {s : ℝ}, 0 < s → R.readout () () s ∈ Ioo (0 : ℝ) 1

private theorem tanhMemRejected : ¬ tanhMemArena.Law tanhRejected := by
  intro h
  have hh := (h (s := 1) zero_lt_one).2
  exact (lt_irrefl (1 : ℝ)) hh

def tanhMemFamily : Registration tanhMemArena (type_of% @tanh_mem) where
  actual := tanhActual
  bridge := Iff.rfl
  variation := ⟨tanh_mem, tanhRejected, tanhMemRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    tanhMemArena.Law tanhActual tanhRejected tanhMemRejected
  dependence := tanhDependence

abbrev ratioTanhArena : Arena where
  signature := tanhSignature
  Law R := ∀ s : ℝ,
    _root_.D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.ratio
      (R.readout () () s) = Real.exp (-2 * s)

private theorem ratioTanhRejected : ¬ ratioTanhArena.Law tanhRejected := by
  intro h
  have hh := h 0
  norm_num [tanhRejected, realize,
    _root_.D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.ratio] at hh

def ratioTanhFamily : Registration ratioTanhArena (type_of% @ratio_tanh) where
  actual := tanhActual
  bridge := Iff.rfl
  variation := ⟨ratio_tanh, tanhRejected, ratioTanhRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    ratioTanhArena.Law tanhActual tanhRejected ratioTanhRejected
  dependence := tanhDependence

def tanhMemAudit :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tanh_mem) (Realization tanhSignature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.RenyiCombining.HircheArimotoCombining.tanhMemUnit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.HircheArimotoCombining.tanhMemFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tanhMemArena⟩
  objectArena := .source ⟨tanhMemArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tanhMemArena ⟨tanhMemFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tanhSignature (fun _ _ s => Real.tanh s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.HircheArimotoCombining
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def ratioTanhAudit :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@ratio_tanh) (Realization tanhSignature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.RenyiCombining.HircheArimotoCombining.ratioTanhUnit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.HircheArimotoCombining.ratioTanhFamily
  realizationSource := none
  generated := false
  arena := .source ⟨ratioTanhArena⟩
  objectArena := .source ⟨ratioTanhArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ratioTanhArena ⟨ratioTanhFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tanhSignature (fun _ _ s => Real.tanh s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.HircheArimotoCombining
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Entropy.RenyiCombining.HircheArimotoCombining
