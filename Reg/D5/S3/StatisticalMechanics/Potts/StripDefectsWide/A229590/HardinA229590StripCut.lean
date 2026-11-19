import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut

/-! Dependent observations of the exact five-row defect counts. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal (Col column)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut
namespace Transition
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 41 ⊕ Fin 41)
    (fun _ => Fin 41 ⊕ Fin 41) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (p : Col) (d : Fin 2) (s : Fin 41 ⊕ Fin 41),
    (∑ r : Fin 5 → Fin 3, if cross p r ≤ d.val ∧
      cl (boundary r) (d.val - cross p r) = s then (1 : ℤ) else 0) =
        A.readout () s (cl p d.val)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (0,0,0,0,0) 0 (Sum.inr 0)
  have ha := transition_counts (0,0,0,0,0) 0 (Sum.inr 0)
  change _ = T (cl (0,0,0,0,0) 0) (Sum.inr 0) at ha
  change _ = T (cl (0,0,0,0,0) 0) (Sum.inr 0) + 1 at hb
  linarith
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨Sum.inr 0, Sum.inl 0, Sum.inl 27, ?_⟩
    change T (Sum.inl 0) (Sum.inr 0) ≠ T (Sum.inl 27) (Sum.inr 0)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.A229590CutTransition.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 41 ⊕ Fin 41) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ _ s => initial s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ s => initial s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ s : Fin 41 ⊕ Fin 41,
    (∑ r : Fin 5 → Fin 3, if cl (boundary r) 1 = s then (1 : ℤ) else 0) = A.readout () () s
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
    refine ⟨(), Sum.inl 0, Sum.inr 0, ?_⟩
    change initial (Sum.inl 0) ≠ initial (Sum.inr 0)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@initial_counts) (Realization signature) Type Unit where
  unitName := `Reg.A229590CutInitial.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut
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
namespace Column
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Col) (fun _ => Fin 5 → Fin 3)
def readout : Realization signature := realize signature (fun _ _ c => column c) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (0 : Fin 5 → Fin 3)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ r : Fin 5 → Fin 3, A.readout () () (boundary r) = r
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congrFun (h (fun _ => 1)) 0
  change (0 : Fin 3) = 1 at hh
  exact (by decide : (0 : Fin 3) ≠ 1) hh
def family : Registration arena (type_of% @column_boundary) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨column_boundary, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0,0,0,0,0), (1,1,1,1,1), ?_⟩
    intro he
    have hh := congrFun he 0
    exact (by decide : (0 : Fin 3) ≠ 1) hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@column_boundary) (Realization signature) Type Unit where
  unitName := `Reg.A229590Column.auditUnit
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
  readout := some (realize signature (fun _ _ c => column c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Column
end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut
