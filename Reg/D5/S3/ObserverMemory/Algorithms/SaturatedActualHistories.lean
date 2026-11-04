import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the natural value preserved by the finite residue equivalence. -/

namespace Reg.D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories

open _root_.D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun m => Fin m) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x.val) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => x.val + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) [NeZero m] (x : Fin m),
    (ZMod.finEquiv m x).val = R.readout () m x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (0 : Fin 1)
  change (ZMod.finEquiv 1 (0 : Fin 1)).val = (0 : Fin 1).val + 1 at hb
  rw [fin_equiv_val] at hb
  norm_num at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, (0 : Fin 2), (1 : Fin 2), ?_⟩
  change (0 : Fin 2).val ≠ (1 : Fin 2).val
  decide

def source : Registration arena (type_of% @fin_equiv_val) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fin_equiv_val, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fin_equiv_val) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories.unit
  realizationName := ``source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories
