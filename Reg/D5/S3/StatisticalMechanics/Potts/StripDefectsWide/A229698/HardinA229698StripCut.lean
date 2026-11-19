import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripCut

/-! Dependent observations of the exact five-row defect counts. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripCut
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal (Col)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData (cross boundary)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripCut
namespace Transition
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 41 ⊕ (Fin 41 ⊕ Fin 41))
    (fun _ => Fin 41 ⊕ (Fin 41 ⊕ Fin 41)) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (p : Col) (d : Fin 3) (s : Fin 41 ⊕ (Fin 41 ⊕ Fin 41)),
    (∑ r : Fin 5 → Fin 3, if cross p r ≤ d.val ∧
      cl (boundary r) (d.val - cross p r) = s then (1 : ℤ) else 0) =
        A.readout () s (cl p d.val)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (0,0,0,0,0) 0 (Sum.inr (Sum.inr 0))
  have ha := transition_counts (0,0,0,0,0) 0 (Sum.inr (Sum.inr 0))
  change _ = T (cl (0,0,0,0,0) 0) (Sum.inr (Sum.inr 0)) at ha
  change _ = T (cl (0,0,0,0,0) 0) (Sum.inr (Sum.inr 0)) + 1 at hb
  linarith
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨Sum.inr (Sum.inr 0), Sum.inl 0, Sum.inl 1, ?_⟩
    change T (Sum.inl 0) (Sum.inr (Sum.inr 0)) ≠ T (Sum.inl 1) (Sum.inr (Sum.inr 0))
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.A229698CutTransition.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s r => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripCut
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transition
namespace Initial
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 41 ⊕ (Fin 41 ⊕ Fin 41)) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ _ s => initial s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ s => initial s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ s : Fin 41 ⊕ (Fin 41 ⊕ Fin 41),
    (∑ r : Fin 5 → Fin 3, if cl (boundary r) 2 = s then (1 : ℤ) else 0) = A.readout () () s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (Sum.inl 0)
  have ha := initial_counts (Sum.inl 0)
  change _ = initial (Sum.inl 0) + 1 at hb
  linarith
def family : Registration arena (type_of% @initial_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨initial_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), Sum.inl 0, Sum.inr (Sum.inr 0), ?_⟩
    change initial (Sum.inl 0) ≠ initial (Sum.inr (Sum.inr 0))
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@initial_counts) (Realization signature) Type Unit where
  unitName := `Reg.A229698CutInitial.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => initial s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Initial
end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripCut
