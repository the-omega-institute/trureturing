import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.BojicThreeTerm
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Native dependent observation for the three-distinct-offset cyclic branch. -/

noncomputable section

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicThreeTerm

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.BojicThreeTerm
open LeanInformationAudit Polynomial

private abbrev Parameters := Σ q : ℕ, Σ m : ℕ, Σ a : ℕ, Σ b : ℕ, Σ c : ℕ, P

abbrev signature : Signature where
  Params := Parameters
  State := fun _ => Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p state =>
      state = true ∧
        type_of% (@piecewise_trinomial_interface
          p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
          )
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q m a b c : ℕ) (f : P),
    R.readout () ⟨q, m, a, b, c, f⟩
      true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0 1 2 X

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0, 0, 1, 2, X⟩, true, false, ?_⟩
  have htarget :
      type_of% (@piecewise_trinomial_interface 0 0 0 1 2 X) := by
    intro hq ha hb hc hab hac hbc hm hi hf hG
    exact piecewise_trinomial_interface hq ha hb hc hab hac hbc hm hi hf hG
  dsimp [actual, realize]
  intro hEq
  have hleft := (⟨rfl, htarget⟩ :
    true = true ∧ type_of% (@piecewise_trinomial_interface 0 0 0 1 2 X))
  have hright := hEq ▸ hleft
  exact Bool.noConfusion hright.1

def evidence : Registration arena (type_of% @piecewise_trinomial_interface) where
  actual := actual
  bridge := by
    constructor
    · intro h q m a b c f
      exact ⟨rfl, h⟩
    · intro h q m a b c f
      exact (h q m a b c f).2
  variation := ⟨by
    intro q m a b c f
    exact ⟨rfl, @piecewise_trinomial_interface q m a b c f⟩,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@piecewise_trinomial_interface)
    (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicThreeTerm.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicThreeTerm.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.BojicThreeTerm
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.StatisticalMechanics.CellularAutomata.BojicThreeTerm
