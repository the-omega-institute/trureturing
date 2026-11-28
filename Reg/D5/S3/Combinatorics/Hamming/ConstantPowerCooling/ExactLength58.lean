import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ExactLength58
import Reg.Support.SingleDependentReadout

/-! A source-bound observation of the length-58 code optimum. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open CPECCBridge CPECCBridge.Length58

noncomputable section

namespace Reg.D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ExactLength58

namespace SupportOptimum

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun m => Fin m → Finset (Finset (Fin 58)))
    (fun m => Fin m → Finset (Finset (Fin 58)))

def actual : Realization signature :=
  realize signature (fun _ _ P => P) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := IsGreatest {m : ℕ | ∃ P : Fin m → Finset (Finset (Fin 58)),
    IsSupportFamily (R.readout () m P) 6 2} 57

private theorem empty_invalid :
    ¬ IsSupportFamily (fun _ : Fin 57 => (∅ : Finset (Finset (Fin 58)))) 6 2 := by
  intro h
  obtain ⟨A, hA, _⟩ := h.2.1 0 {0, 1} (by decide)
  simp at hA

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, hEmpty⟩ := h.1
  exact empty_invalid hEmpty

theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨P, hP⟩ := support_optimum.1
  refine ⟨57, P, fun _ => ∅, ?_⟩
  change P ≠ fun _ => ∅
  intro h
  exact empty_invalid (h ▸ hP)

def source_registration : Registration arena
    (IsGreatest {m : ℕ | ∃ P : Fin m → Finset (Finset (Fin 58)), IsSupportFamily P 6 2} 57)
    where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨support_optimum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@support_optimum) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ExactLength58.SupportOptimum.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ExactLength58.SupportOptimum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ExactLength58
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "arg", "body", "arg", "body", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end SupportOptimum

end Reg.D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ExactLength58
