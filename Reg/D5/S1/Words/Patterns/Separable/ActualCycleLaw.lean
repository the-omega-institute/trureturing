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

namespace PrefixBox

open _root_.D5.S1.Words.Patterns.Separable.EndpointHistoryKernel (indecomposableWitness)

abbrev signature : Signature where
  Params := ℕ
  State k := UnboundedTuple k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set Stream
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => Prefix.cylinder p) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ} (p : UnboundedTuple k),
    R.readout () k p = Set.pi (Finset.range k : Set ℕ)
      (fun i => {c | ∀ h : i < k, c = Prefix.nth p ⟨i, h⟩})

private def singleton (sign : Bool) : MarkedCycle :=
  ⟨sign, .terminal 0 (indecomposableWitness sign 1)⟩

private def oneTuple (sign : Bool) : UnboundedTuple 1 := (singleton sign, ())

private def directStream : Stream := fun _ => singleton false

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (k := 0) ()
  change (∅ : Set Stream) =
    Set.pi (Finset.range 0 : Set ℕ)
      (fun i => {c | ∀ h : i < 0, c = Prefix.nth (k := 0) () ⟨i, h⟩}) at he
  have hn : directStream ∈ Set.pi (Finset.range 0 : Set ℕ)
      (fun i => {c | ∀ h : i < 0, c = Prefix.nth (k := 0) () ⟨i, h⟩}) := by
    simp
  exact Set.notMem_empty _ (he.symm ▸ hn)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨1, oneTuple false, oneTuple true, ?_⟩
  intro h
  change Prefix.cylinder (oneTuple false) = Prefix.cylinder (oneTuple true) at h
  have hd : directStream ∈ Prefix.cylinder (oneTuple false) := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
    rfl
  have hs : directStream ∈ Prefix.cylinder (oneTuple true) := h ▸ hd
  have he : singleton false = singleton true := hs (0 : Fin 1)
  exact Bool.false_ne_true (congrArg Sigma.fst he)

def family : Registration arena (type_of% @Prefix.box) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Prefix.box, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Prefix.box) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.ActualCycleLaw.PrefixBox.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.ActualCycleLaw.PrefixBox.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => Prefix.cylinder p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.ActualCycleLaw
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end PrefixBox

namespace FixedDecodeSize

open _root_.D5.S1.Words.Patterns.Separable.EndpointHistoryKernel (indecomposableWitness)

abbrev signature : Signature where
  Params := Σ _ : Bool, ℕ
  State a := Fixed a.1 a.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := UnboundedCycle a.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => Fixed.decode p) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ a _ => .terminal 0 (indecomposableWitness a.1 1))
    (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ {s : Bool} {k : ℕ} (p : Fixed s k),
    (R.readout () ⟨s, k⟩ p).size = p.size

private def terminalFixed (n : ℕ) : Fixed false 0 :=
  ⟨n, indecomposableWitness false (n + 1)⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (terminalFixed 1)
  change (1 : ℕ) = 2 at he
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨false, 0⟩, terminalFixed 0, terminalFixed 1, ?_⟩
  intro h
  have he := congrArg UnboundedCycle.size h
  change (1 : ℕ) = 2 at he
  omega

def family : Registration arena (type_of% @Fixed.decode_size) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Fixed.decode_size, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Fixed.decode_size) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.ActualCycleLaw.FixedDecodeSize.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.ActualCycleLaw.FixedDecodeSize.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => Fixed.decode p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.ActualCycleLaw
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end FixedDecodeSize

#print axioms audit
end
end Reg.D5.S1.Words.Patterns.Separable.ActualCycleLaw
