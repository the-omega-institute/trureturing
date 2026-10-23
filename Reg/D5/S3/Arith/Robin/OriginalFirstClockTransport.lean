import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalFirstClockTransport
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.OriginalFirstClockTransport

open _root_.D5.S3.Arith.Robin.OriginalFirstClockTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace ErrorDecay

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => firstError t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := StrictAntiOn (R.readout () ()) (Set.Ici 243) ∧
    Filter.Tendsto (R.readout () ()) Filter.atTop (nhds 0)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h.1 (show (243 : ℝ) ∈ Set.Ici 243 from by norm_num)
    (show (244 : ℝ) ∈ Set.Ici 243 from by norm_num) (by norm_num : (243 : ℝ) < 244)
  exact (lt_irrefl (0 : ℝ)) hf

def family : Registration arena (type_of% @first_error_decay) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨first_error_decay, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 243, 244, ?_⟩
    have hf := first_error_decay.1 (show (243 : ℝ) ∈ Set.Ici 243 from by norm_num)
      (show (244 : ℝ) ∈ Set.Ici 243 from by norm_num) (by norm_num : (243 : ℝ) < 244)
    exact (ne_of_gt hf)

/-- Kernel-checked family evidence. Raw higher-order source occurrence
reconstruction through StrictAntiOn and Tendsto is not supplied; sourceSelection
is explicitly missing, so this is not a declared_validated audit. The source
binding gap belongs to https://github.com/the-omega-institute/trureturing/issues/5214. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@first_error_decay) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.Robin.OriginalFirstClockTransport.ErrorDecay.unit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalFirstClockTransport.ErrorDecay.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end ErrorDecay
end
end Reg.D5.S3.Arith.Robin.OriginalFirstClockTransport
