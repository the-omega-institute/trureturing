import D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ × ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ k =>
    (Nat.card ((_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.stripGraph true 1 k).Coloring (Fin 3)),
     Nat.card ((_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.stripGraph true 2 k).Coloring (Fin 3))))
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0,0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k, (R.readout () () k).1 = 3*vB k 0 + 6*vB k 1 ∧
    (R.readout () () k).2 = 3*hV k 0 + 12*hV k 1 + 6*hV k 2 + (if k=0 then 6 else 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have h0 := (hh 0).1
  change 0 = 3*vB 0 0 + 6*vB 0 1 at h0
  norm_num [vB] at h0

def family : Registration arena (type_of% @column_result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨column_result,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    intro he
    have hh := congrArg (fun x : ℕ × ℕ => x.1) he
    change Nat.card ((_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.stripGraph true 1 0).Coloring (Fin 3)) =
      Nat.card ((_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.stripGraph true 1 1).Coloring (Fin 3)) at hh
    rw [(column_result 0).1,(column_result 1).1] at hh
    norm_num [vB,B,Fin.sum_univ_succ] at hh

/-- Exact source occurrence selection remains unresolved; no validated registration is asserted. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@column_result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k =>
    (Nat.card ((_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.stripGraph true 1 k).Coloring (Fin 3)),
     Nat.card ((_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.stripGraph true 2 k).Coloring (Fin 3))))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations
