import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
open _root_.D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.TotalVariation.CycleSingleCutMinimax
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe a matrix acting on a vector, retaining its dimension and all entries. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ N : ℕ, Matrix (Fin N) (Fin N) ℝ)
    (fun p => Fin p.1 → ℝ)
    (fun p => Fin p.1 → ℝ)

def actual : Realization signature :=
  realize signature (fun _ p v => p.2.mulVec v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Every nonnegative column-stochastic matrix preserves probability vectors. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {N : ℕ} {P : Matrix (Fin N) (Fin N) ℝ} {p : Fin N → ℝ},
    (∀ i j, 0 ≤ P i j) → (∀ j, (∑ i, P i j) = 1) →
    Probability p → Probability (r.readout () ⟨N, P⟩ p)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : Probability (fun _ : Fin 1 => (1 : ℝ)) := by
    constructor
    · intro i
      norm_num
    · norm_num
  have he := h (N := 1) (P := fun _ _ => 1) (p := fun _ => 1)
    (by intro i j; norm_num) (by intro j; norm_num) hp
  have hs := he.2
  norm_num [rejected, realize] at hs

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, fun _ _ => 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hc := congrArg (fun v : Fin 1 → ℝ => v 0) he
  norm_num [actual, realize, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hc

def source_registration : Registration arena (type_of% @probability_mulVec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨probability_mulVec, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@probability_mulVec) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => p.2.mulVec v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
