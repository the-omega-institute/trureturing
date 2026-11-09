import D5.S3.ConceptDynamics.Representation.PrimitiveGeneratorComparisonArithmetic
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.ConceptDynamics.Representation.PrimitiveGeneratorComparisonArithmetic

open _root_.D5.S3.ConceptDynamics.Representation.PrimitiveGeneratorComparisonArithmetic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
open Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (ℚ × ℚ × ℚ) (fun _ => Bool) (fun _ => Bool)

def sourceConclusion (n m d : ℚ) : Prop :=
    (n - 2) * d - n * (n + 1) / 2 ≤
        generatorComparisonCount m d - pairComparisonCount d ∧
      n * (n + 1) * (n - 3) / 2 ≤
        generatorComparisonCount m d - pairComparisonCount d ∧
      0 < generatorComparisonCount m d - pairComparisonCount d

def actual : Realization signature :=
  realize signature
    (fun _ p b => if b then if sourceConclusion p.1 p.2.1 p.2.2 then true else false else false)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ (n m d : ℚ),
    4 ≤ n → n ≤ m → m ≤ n + 2 → n * (n + 1) / 2 ≤ d →
      F.readout () (n, m, d) true = true

private theorem actual_law : arena.Law actual := by
  intro n m d hn hnm hmn2 hd
  have h := explicit_comparison_strict_reduction hn hnm hmn2 hd
  have hs : sourceConclusion n m d := h
  simp only [actual, realize, if_pos hs, ite_true, ite_false]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (4 : ℚ) 4 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa [rejected, realize] using hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(4, 4, 10), true, false, ?_⟩
  have hs : sourceConclusion (4 : ℚ) 4 10 := by
    norm_num [sourceConclusion, generatorComparisonCount, pairComparisonCount]
  simp [actual, realize, hs]

def evidence : Registration arena (type_of% @explicit_comparison_strict_reduction) where
  actual := actual
  bridge := by
    constructor
    · intro h n m d hn hnm hmn2 hd
      have hc := @h n m d hn hnm hmn2 hd
      have hs : sourceConclusion n m d := hc
      simp only [actual, realize, if_pos hs, ite_true, ite_false]
    · intro h n m d hn hnm hmn2 hd
      have hc := h n m d hn hnm hmn2 hd
      by_cases hs : sourceConclusion n m d
      · exact hs
      · have hfalse : false = true := by
          simpa only [actual, realize, if_neg hs, ite_true, ite_false] using hc
        cases hfalse
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.ConceptDynamics.Representation.PrimitiveGeneratorComparisonArithmetic.explicit_comparison_strict_reduction)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Representation.PrimitiveGeneratorComparisonArithmetic.explicit_comparison_strict_reduction
  realizationName := `Reg.D5.S3.ConceptDynamics.Representation.PrimitiveGeneratorComparisonArithmetic.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.ConceptDynamics.Representation.PrimitiveGeneratorComparisonArithmetic
