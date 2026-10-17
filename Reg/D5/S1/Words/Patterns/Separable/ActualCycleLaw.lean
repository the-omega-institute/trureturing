import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.ActualCycleLaw
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.Patterns.Separable.ActualCycleLaw
open _root_.D5.S1.Words.Patterns.Separable.ActualCycleLaw
open _root_.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Filter Topology
open scoped BigOperators ENNReal
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => nhds z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    Countable MarkedCycle ∧
    IsProbabilityMeasure streamMeasure ∧
    (∀ k, Function.Bijective (Prefix.nth (k := k))) ∧
    (∀ sign r, (∑' c : Fixed sign r, ENNReal.ofReal (rho ^ c.size)) =
      ENNReal.ofReal (ceiling * b ^ r)) ∧
    (∑' c : MarkedCycle, ENNReal.ofReal (rho ^ c.2.size)) = 1 ∧
    (∀ k (tuple : UnboundedTuple k), MeasurableSet (Prefix.cylinder tuple) ∧
      streamMeasure (Prefix.cylinder tuple) = ENNReal.ofReal (rho ^ tuple.size)) ∧
    (∀ k (tuple : UnboundedTuple k),
      ∃ K H : ℕ, ∃ bounded : Tuple K H k, bounded.erase = tuple ∧
        Tendsto bounded.probability atTop
          (R.readout () () ((streamMeasure (Prefix.cylinder tuple)).toReal))) ∧
    ProbabilityTheory.iIndepFun (fun (j : ℕ) (ω : Stream) => ω j) streamMeasure ∧
    (∀ I : Finset ℕ, streamMeasure.map I.restrict =
      Measure.pi (fun _ : I => cyclePMF.toMeasure))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨K, H, bounded, erased, limit⟩ := law.2.2.2.2.2.2.1 0 ()
  exact Filter.atTop_neBot.ne (Filter.tendsto_bot_right_iff.mp limit)

def family : Registration arena (type_of% @actual_countable_cycle_law) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_countable_cycle_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    exact nhds_injective.ne (by norm_num)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_countable_cycle_law) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.ActualCycleLaw.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.ActualCycleLaw.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => nhds z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.ActualCycleLaw
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S1.Words.Patterns.Separable.ActualCycleLaw
