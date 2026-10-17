import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.SchroderRatioLimit
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.Recurrence.Algebraic.SchroderRatioLimit

open _root_.D5.S1.Recurrence.Algebraic.SchroderRatioLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped Topology

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ k m => (Nat.largeSchroder m : ℝ) / (Nat.largeSchroder (m + k) : ℝ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The whole all-shifts limit statement is the law; both its natural indices
and its real output remain infinite. -/
def arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, Tendsto (fun m : ℕ => R.readout () k m) atTop
    (nhds ((Real.sqrt (2 : ℝ) - 1) ^ (2 * k)))

theorem rejected_not_law : ¬arena.Law rejected := by
  intro h
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (1 : ℝ)) := by
    simpa [arena, rejected, realize] using h 0
  have bad : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds h0
  norm_num at bad

def family : Registration arena (type_of% schroder_ratio_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨schroder_ratio_limit, rejected, rejected_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_not_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), ?_⟩
    change (Nat.largeSchroder 0 : ℝ) / (Nat.largeSchroder 1 : ℝ) ≠
      (Nat.largeSchroder 1 : ℝ) / (Nat.largeSchroder 2 : ℝ)
    norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    schroder_ratio_limit (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Algebraic.SchroderRatioLimit.schroder_ratio_limit
    "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.SchroderRatioLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.SchroderRatioLimit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "fn", "arg", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S1.Recurrence.Algebraic.SchroderRatioLimit
