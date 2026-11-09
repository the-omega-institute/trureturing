import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden
import D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill

/-! Source-bound families for subshift configurations, memory and relative languages. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
open SymbolicDynamics.FullShift Set Function MeasureTheory Filter
open scoped Pointwise Topology

namespace Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill

abbrev BaseInputs := Σ G : Type u, Σ group : Group G, Σ A : Type v,
  Σ topology : TopologicalSpace A, @MulSubshift A topology G group.toMonoid

abbrev Config (P : BaseInputs.{u,v}) :=
  @Cfg P.1 P.2.1 P.2.2.1 P.2.2.2.1 P.2.2.2.2

abbrev CodeInputs := Σ G : Type u, Σ group : Group G, Σ A : Type v,
  Σ topology : TopologicalSpace A, Σ X : @MulSubshift A topology G group.toMonoid,
    @Cfg G group A topology X → @Cfg G group A topology X

abbrev codeBase (P : CodeInputs.{u,v}) : BaseInputs.{u,v} :=
  ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1, P.2.2.2.2.1⟩

abbrev codeSignature : Signature where
  Params := CodeInputs.{u,v}
  State P := Config (codeBase P)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Config (codeBase P)
  Anchor := Empty
  finiteAnchor := inferInstance

def codeActual : Realization codeSignature.{u,v} :=
  realize codeSignature (fun _ P => P.2.2.2.2.2) (fun e => nomatch e)

def codeConstant : Realization codeSignature.{u,v} :=
  realize codeSignature
    (fun _ P x => if h : Nonempty (Config (codeBase P)) then Classical.choice h else x)
    (fun e => nomatch e)

def codeArena : Arena where
  signature := codeSignature.{u,v}
  Law R := ∀ {G : Type u} [group : Group G] {A : Type v} [topology : TopologicalSpace A]
    [Finite A] [DiscreteTopology A]
    (_ham : letI : MeasurableSpace G := ⊤
      NeBot (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)))
    (X : MulSubshift A G) (_hX : X.carrier.Nonempty)
    (_hSI : ∃ Delta : Finset G, SI X Delta)
    (tau : Cfg X → Cfg X) (_htau : Continuous tau)
    (_hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (_hpre : ∀ x y : Cfg X, {g | x.val g ≠ y.val g}.Finite → tau x = tau y → x = y),
    Surjective (R.readout () ⟨G, group, A, topology, X, tau⟩)

private abbrev SmallGroup := ULift.{u} Unit
private abbrev SmallAlphabet := ULift.{v} Bool
private instance : TopologicalSpace SmallAlphabet.{v} := ⊥
private instance : DiscreteTopology SmallAlphabet.{v} := ⟨rfl⟩

private def full : MulSubshift SmallAlphabet.{v} SmallGroup.{u} :=
  mulFullShift _ _

private def zero : Cfg full.{u,v} := ⟨fun _ => ⟨false⟩, trivial⟩
private def one : Cfg full.{u,v} := ⟨fun _ => ⟨true⟩, trivial⟩

private theorem zero_ne_one : zero.{u,v} ≠ one := by
  intro h
  have hh := congrArg ULift.down (congrArg (fun x : Cfg full.{u,v} => x.val 1) h)
  cases hh

private theorem full_si : SI full.{u,v} {1} := by
  classical
  intro F K hsep x y
  let z : SmallGroup.{u} → SmallAlphabet.{v} := fun g => if g ∈ F then x.val g else y.val g
  refine ⟨⟨z, trivial⟩, ?_, ?_⟩
  · intro g hg
    simp [z, hg]
  · intro g hg
    have hn : g ∉ F := by
      intro hf
      apply Set.disjoint_left.mp hsep ?_ hg
      simpa only [inv_one, mul_one] using Set.mul_mem_mul hf
        (show (1 : SmallGroup.{u}) ∈ (({1} : Finset SmallGroup.{u}) : Set SmallGroup.{u})⁻¹ by simp)
    simp [z, hn]

private theorem codeConstant_rejected : ¬ codeArena.{u,v}.Law codeConstant := by
  classical
  intro hlaw
  have hsurj := @hlaw SmallGroup.{u} inferInstance SmallAlphabet.{v} inferInstance
    inferInstance inferInstance
    (_root_.Reg.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden.finite_amenable SmallGroup.{u})
    full ⟨zero.val, zero.property⟩ ⟨{1}, full_si⟩ id continuous_id
    (fun _ _ => rfl) (fun _ _ _ h => h)
  let P : CodeInputs.{u,v} := ⟨SmallGroup, inferInstance, SmallAlphabet, inferInstance, full, id⟩
  obtain ⟨x, hx⟩ := hsurj zero
  obtain ⟨y, hy⟩ := hsurj one
  have hN : Nonempty (Config (codeBase P)) := ⟨zero⟩
  have hxy : codeConstant.readout () P x = codeConstant.readout () P y := by
    simp only [codeConstant, realize, dite_eq_left hN]
  exact zero_ne_one (hx.symm.trans (hxy.trans hy))

def codeFamily : Registration codeArena.{u,v} (type_of% (@myhill.{u,v})) where
  actual := codeActual
  bridge := Iff.rfl
  variation := ⟨@myhill.{u,v}, codeConstant, codeConstant_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨codeConstant, ?_, rfl, codeConstant_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let P : CodeInputs.{u,v} := ⟨SmallGroup, inferInstance, SmallAlphabet, inferInstance, full, id⟩
    exact ⟨P, zero, one, zero_ne_one⟩

def registration_myhill : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@myhill.{u,v}) (Realization codeSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill.code
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill.codeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨codeArena.{u,v}⟩
  objectArena := .source ⟨codeArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source codeArena.{u,v} ⟨codeFamily.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize codeSignature.{u,v} (fun _ P => P.2.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
    definition := none
    coordinates := #[0, 1, 2, 3, 7, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev EvalInputs := Σ G : Type u, Σ group : Group G, Σ A : Type v,
  Σ topology : TopologicalSpace A, Σ X : @MulSubshift A topology G group.toMonoid,
    Σ _x0 : @Cfg G group A topology X, G

abbrev evalBase (P : EvalInputs.{u,v}) : BaseInputs.{u,v} :=
  ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1, P.2.2.2.2.1⟩

abbrev evalSignature : Signature where
  Params := EvalInputs.{u,v}
  State P := Config (evalBase P)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def evalActual : Realization evalSignature.{u,v} :=
  realize evalSignature (fun _ P z => z.val P.2.2.2.2.2.2) (fun e => nomatch e)

def evalBackground : Realization evalSignature.{u,v} :=
  realize evalSignature
    (fun _ P _ => P.2.2.2.2.2.1.val P.2.2.2.2.2.2) (fun e => nomatch e)

def exteriorArena : Arena where
  signature := evalSignature.{u,v}
  Law R := ∀ {G : Type u} [group : Group G] {A : Type v} [topology : TopologicalSpace A]
    [Finite A] [DiscreteTopology A]
    (X : MulSubshift A G) (Delta F : Finset G) (_hSI : SI X Delta)
    (x x0 : Cfg X), ∃ z : Cfg X,
      (∀ g ∈ F, R.readout () ⟨G, group, A, topology, X, x0, g⟩ z = x.val g) ∧
      (∀ g ∉ (F : Set G) * (Delta : Set G)⁻¹, z.val g = x0.val g)

private theorem evalBackground_rejected : ¬ exteriorArena.{u,v}.Law evalBackground := by
  intro hlaw
  obtain ⟨z, hz, _⟩ := @hlaw SmallGroup.{u} inferInstance SmallAlphabet.{v} inferInstance
    inferInstance inferInstance full {1} {1} full_si one zero
  have hh := congrArg ULift.down (hz 1 (Finset.mem_singleton_self _))
  cases hh

def exteriorFamily : Registration exteriorArena.{u,v} (type_of% (@common_exterior.{u,v})) where
  actual := evalActual
  bridge := Iff.rfl
  variation := ⟨@common_exterior.{u,v}, evalBackground, evalBackground_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨evalBackground, ?_, rfl, evalBackground_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let P : EvalInputs.{u,v} := ⟨SmallGroup, inferInstance, SmallAlphabet, inferInstance, full, zero, 1⟩
    refine ⟨P, zero, one, ?_⟩
    intro h
    have hh := congrArg ULift.down h
    cases hh

def registration_common_exterior : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_exterior.{u,v}) (Realization evalSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill.exterior
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill.exteriorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨exteriorArena.{u,v}⟩
  objectArena := .source ⟨exteriorArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exteriorArena.{u,v} ⟨exteriorFamily.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize evalSignature.{u,v}
    (fun _ P z => z.val P.2.2.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
    definition := none
    coordinates := #[0, 1, 2, 3, 6, 11, 13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev WindowInputs := Σ G : Type u, Σ group : Group G, Σ A : Type v,
  Σ topology : TopologicalSpace A, Σ _X : @MulSubshift A topology G group.toMonoid, Finset G

abbrev windowBase (P : WindowInputs.{u,v}) : BaseInputs.{u,v} :=
  ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1, P.2.2.2.2.1⟩

abbrev memorySignature : Signature where
  Params := WindowInputs.{u,v}
  State P := Config (windowBase P) → Config (windowBase P)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def memoryActual : Realization memorySignature.{u,v} :=
  realize memorySignature (fun _ P tau => decide
    (@HasMemory P.1 P.2.1 P.2.2.1 P.2.2.2.1 P.2.2.2.2.1 tau P.2.2.2.2.2))
    (fun e => nomatch e)

def memoryNever : Realization memorySignature.{u,v} :=
  realize memorySignature (fun _ _ _ => false) (fun e => nomatch e)

def memoryArena : Arena where
  signature := memorySignature.{u,v}
  Law R := ∀ {G : Type u} [group : Group G] {A : Type v} [topology : TopologicalSpace A]
    [Finite A] [DiscreteTopology A] (X : MulSubshift A G)
    (tau : Cfg X → Cfg X), Continuous tau →
      ∃ M : Finset G, R.readout () ⟨G, group, A, topology, X, M⟩ tau = true

private theorem memory_actual_law : memoryArena.{u,v}.Law memoryActual := by
  intro G group A topology finite discrete X tau htau
  obtain ⟨M, hM⟩ := finite_memory X tau htau
  exact ⟨M, by simpa [memoryActual, realize] using hM⟩

private theorem memoryNever_rejected : ¬ memoryArena.{u,v}.Law memoryNever := by
  intro hlaw
  obtain ⟨M, hM⟩ := @hlaw SmallGroup.{u} inferInstance SmallAlphabet.{v} inferInstance
    inferInstance inferInstance full id continuous_id
  cases hM

private theorem memory_dependence : ObservationalDependence memorySignature.{u,v} memoryActual := by
  intro i
  let P : WindowInputs.{u,v} := ⟨SmallGroup, inferInstance, SmallAlphabet, inferInstance, full, ∅⟩
  have hc : HasMemory full.{u,v} (fun _ => zero) ∅ := by intro x y hxy; rfl
  have hn : ¬ HasMemory full.{u,v} id ∅ := by
    intro h
    have hh := congrArg ULift.down (h zero one (by simp))
    cases hh
  refine ⟨P, (fun _ => zero), id, ?_⟩
  change decide (HasMemory full (fun _ => zero) ∅) ≠ decide (HasMemory full id ∅)
  simp only [hc, hn, decide_true, decide_false, ne_eq, Bool.true_eq_false, not_false_eq_true]

def memoryFamily : Registration memoryArena.{u,v} (type_of% (@finite_memory.{u,v})) where
  actual := memoryActual
  bridge := by
    constructor
    · intro h G group A topology finite discrete X tau htau
      obtain ⟨M, hM⟩ := @h G group A topology finite discrete X tau htau
      exact ⟨M, by simpa [memoryActual, realize] using hM⟩
    · intro h G group A topology finite discrete X tau htau
      obtain ⟨M, hM⟩ := @h G group A topology finite discrete X tau htau
      exact ⟨M, by simpa [memoryActual, realize] using hM⟩
  variation := ⟨memory_actual_law, memoryNever, memoryNever_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨memoryNever, ?_, rfl, memoryNever_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := memory_dependence

def registration_finite_memory : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_memory.{u,v}) (Realization memorySignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill.memory
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill.memoryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨memoryArena.{u,v}⟩
  objectArena := .source ⟨memoryArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source memoryArena.{u,v} ⟨memoryFamily.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize memorySignature.{u,v} (fun _ P tau => decide
    (@HasMemory P.1 P.2.1 P.2.2.1 P.2.2.2.1 P.2.2.2.2.1 tau P.2.2.2.2.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
    definition := none
    coordinates := #[0, 1, 2, 3, 6, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
