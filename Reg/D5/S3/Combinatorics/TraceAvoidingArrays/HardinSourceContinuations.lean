import D5.S3.Combinatorics.TraceAvoidingArrays.HardinSourceContinuations
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinSourceContinuations
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinSourceContinuations
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ)
    (fun _ => (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen →
      (Fin 4 → Fin 3) → ℤ) × ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ m =>
    (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthV
      (fun c => _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.proper
        (fun j => _root_.D5.S3.Observer.Separation.BooleanRankThreeK4.beta (c j)))
      (fun c j => _root_.D5.S3.Observer.Separation.BooleanRankThreeK4.beta (c j))
      (fun p c => _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.compatible
        true p (fun j => _root_.D5.S3.Observer.Separation.BooleanRankThreeK4.beta (c j))) m,
     (Nat.card (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.literalStrip true m 3) : ℤ)))
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (fun _ _ => 0, -1)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m, (∀ s p, admissible s p →
    (R.readout () () m).1 s p = sourceV m (sourceClass s p)) ∧
    (R.readout () () m).2 = ∑ j, r j * sourceV m j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have h0 := (hh 0).2
  change -1 = ∑ j, r j * sourceV 0 j at h0
  norm_num [sourceV,r,Fin.sum_univ_succ] at h0

def family : Registration arena (type_of% @four_class_result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨four_class_result,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    intro he
    have hh := congrArg (fun x => x.2) he
    change (Nat.card (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.literalStrip true 0 3) : ℤ) =
      Nat.card (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.literalStrip true 1 3) at hh
    rw [(four_class_result 0).2,(four_class_result 1).2] at hh
    norm_num [sourceV,M,r,Fin.sum_univ_succ] at hh

/-- Exact source occurrence selection remains unresolved; no validated registration is asserted. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@four_class_result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinSourceContinuations.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinSourceContinuations.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m =>
    (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthV
      (fun c => _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.proper
        (fun j => _root_.D5.S3.Observer.Separation.BooleanRankThreeK4.beta (c j)))
      (fun c j => _root_.D5.S3.Observer.Separation.BooleanRankThreeK4.beta (c j))
      (fun p c => _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.compatible
        true p (fun j => _root_.D5.S3.Observer.Separation.BooleanRankThreeK4.beta (c j))) m,
     (Nat.card (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.literalStrip true m 3) : ℤ)))
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
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinSourceContinuations
