import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.Hypergraphs.CircularOrientationEntropyLowerBound

namespace Reg.D5.S3.Entropy.Hypergraphs.CircularOrientationEntropyLowerBound

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.Hypergraphs.CircularOrientationEntropyLowerBound
open _root_.D5.S0.Certificates.Hypergraphs
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r n : ℕ) (_hr : 3 ≤ r) (_hn : r < n),
    R.readout () () ((1 / 2 : ℝ) * Real.logb 2 ((n : ℝ) / r) - K r)
      (OrientationEntropyBalance.entropyX r (CircularOrientationEntropy.circular n r))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 4 (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hh

def source_registration : Registration arena (type_of% whole_theorem_one_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_theorem_one_two, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Entropy.Hypergraphs.CircularOrientationEntropyLowerBound.whole_theorem_one_two)
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.Hypergraphs.CircularOrientationEntropyLowerBound.whole_theorem_one_two_unit
  realizationName := `Reg.D5.S3.Entropy.Hypergraphs.CircularOrientationEntropyLowerBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.Hypergraphs.CircularOrientationEntropyLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Entropy.Hypergraphs.CircularOrientationEntropyLowerBound
