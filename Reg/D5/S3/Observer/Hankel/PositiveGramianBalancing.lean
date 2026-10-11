import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Hankel.PositiveGramianBalancing
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Hankel.PositiveGramianBalancing (diagonal_scalings)

noncomputable section
namespace Reg.D5.S3.Observer.Hankel.PositiveGramianBalancing
namespace DiagonalScalings

abbrev signature : Signature where
  Params := Type
  State ι := ι → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ ι := ι → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w i => Real.sqrt (w i)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (_hw : ∀ i, 0 < w i),
    let D := diagonal w
    let H := diagonal (R.readout () ι w)
    let I := diagonal (fun i => (Real.sqrt (w i))⁻¹)
    H * I = 1 ∧ I * H = 1 ∧ I * D * I = 1 ∧
      I * diagonal (fun i => (w i) ^ 2) * I = D

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h (ι := Fin 1) (fun _ => 1) (fun _ => zero_lt_one)).1
  have entry := congrFun (congrFun bad 0) 0
  norm_num [rejected, realize, Matrix.mul_apply, diagonal] at entry

def family : Registration arena (type_of% @diagonal_scalings) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨diagonal_scalings, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨Fin 1, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have entry := congrFun h 0
    norm_num [actual, realize] at entry

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Observer.Hankel.PositiveGramianBalancing.diagonal_scalings)
      (type_of% (realize signature (fun _ _ w i => Real.sqrt (w i))
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Hankel.PositiveGramianBalancing.diagonal_scalings.__information_unit
  realizationName := `Reg.D5.S3.Observer.Hankel.PositiveGramianBalancing.DiagonalScalings.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w i => Real.sqrt (w i))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Hankel.PositiveGramianBalancing
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end DiagonalScalings
end Reg.D5.S3.Observer.Hankel.PositiveGramianBalancing
