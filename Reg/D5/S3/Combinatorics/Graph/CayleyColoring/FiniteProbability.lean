import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Graph.CayleyColoring.FiniteProbability

open MeasureTheory ProbabilityTheory
open CayleyFiniteLaw CayleyTreeProbability DiscardedOccupancy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.CayleyColoring.FiniteProbability

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ)
    (fun p => Fin p.1 × ZMod p.2) (fun p => Option (Fin p.1))

def arena : Arena where
  signature := signature
  Law R := ∀ {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) [NeZero k] (m : ℕ),
    (uniform (Fin m → Fin n × ZMod k)).map (fun w i => R.readout () (n, k) (w i)) =
      literalMeasure hn hk m

def actual : Realization signature :=
  realize signature (fun _ _ x => bin x) (fun e => nomatch e)

def discardAll : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

private theorem discardAll_rejected : ¬ arena.Law discardAll := by
  intro h
  have equality := @h 1 2 (by decide) (by decide) (by infer_instance) 1
  let target : Fin 1 → Option (Fin 1) := fun _ => some 0
  have hleft :
      ((uniform (Fin 1 → Fin 1 × ZMod 2)).map
        (fun (_ : Fin 1 → Fin 1 × ZMod 2) (_ : Fin 1) => (none : Option (Fin 1)))) {target} =
      0 := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton target)]
    have empty_preimage :
        (fun (_ : Fin 1 → Fin 1 × ZMod 2) (_ : Fin 1) => (none : Option (Fin 1))) ⁻¹'
          ({target} : Set (Fin 1 → Option (Fin 1))) = ∅ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact Option.noConfusion (congrFun heq 0)
    rw [empty_preimage, measure_empty]
  have hright : literalMeasure (by decide : 0 < 1) (by decide : 2 ≤ 2) 1 {target} ≠ 0 := by
    unfold literalMeasure
    rw [Measure.pi_singleton]
    simp only [Fin.prod_univ_one, target]
    rw [(palette_throw_mass (by decide : 0 < 1) (by decide : 2 ≤ 2)).2 0]
    norm_num
  change _ = literalMeasure (by decide : 0 < 1) (by decide : 2 ≤ 2) 1 at equality
  exact hright ((congrArg (fun μ : Measure (Fin 1 → Option (Fin 1)) => μ {target}) equality).symm.trans hleft)

def realization : Registration arena (type_of% (@microstate_word_law)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@microstate_word_law, discardAll, discardAll_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual discardAll discardAll_rejected
  dependence := by
    intro i
    cases i
    refine ⟨(1, 2), (0, 0), (0, 1), ?_⟩
    change bin (0, 0 : Fin 1 × ZMod 2) ≠ bin (0, 1 : Fin 1 × ZMod 2)
    rw [(bin_some_iff (0, 0 : Fin 1 × ZMod 2) 0).2 ⟨rfl, rfl⟩,
      (bin_none_iff (0, 1 : Fin 1 × ZMod 2)).2 (by decide)]
    exact Option.some_ne_none _

def markPushforwardRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@microstate_word_law) (Realization signature) Unit Unit where
  unitName := `CayleyTreeProbability.microstate_word_law.mark_word_readout
  realizationName := `Reg.D5.S3.Combinatorics.Graph.CayleyColoring.FiniteProbability.realization
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨realization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => bin x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.CayleyColoring.FiniteProbability
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.CayleyColoring.FiniteProbability
