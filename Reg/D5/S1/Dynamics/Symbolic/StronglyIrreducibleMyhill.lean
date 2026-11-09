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

abbrev SmallGroup := ULift.{u} Unit
abbrev SmallAlphabet := ULift.{v} Bool
private instance : TopologicalSpace SmallAlphabet.{v} := ⊥
private instance : DiscreteTopology SmallAlphabet.{v} := ⟨rfl⟩

def full : MulSubshift SmallAlphabet.{v} SmallGroup.{u} :=
  mulFullShift _ _

def zero : Cfg full.{u,v} := ⟨fun _ => ⟨false⟩, trivial⟩
def one : Cfg full.{u,v} := ⟨fun _ => ⟨true⟩, trivial⟩

theorem zero_ne_one : zero.{u,v} ≠ one := by
  intro h
  have hh := congrArg ULift.down (congrArg (fun x : Cfg full.{u,v} => x.val 1) h)
  cases hh

theorem full_si : SI full.{u,v} {1} := by
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

abbrev imageSignature : Signature where
  Params := WindowInputs.{u,v}
  State P := Config (windowBase P) → Config (windowBase P)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def imageActual : Realization imageSignature.{u,v} :=
  realize imageSignature (fun _ P tau => Nat.card
    (@ImagePat P.1 P.2.1 P.2.2.1 P.2.2.2.1 P.2.2.2.2.1 tau P.2.2.2.2.2))
    (fun e => nomatch e)

def imageZero : Realization imageSignature.{u,v} :=
  realize imageSignature (fun _ _ _ => 0) (fun e => nomatch e)

def imageArena : Arena where
  signature := imageSignature.{u,v}
  Law R := ∀ {G : Type u} [group : Group G] {A : Type v} [topology : TopologicalSpace A]
    [Finite A] [DiscreteTopology A]
    (X : MulSubshift A G) (Delta F M U : Finset G) (_hSI : SI X Delta)
    (_x0 : Cfg X) (tau : Cfg X → Cfg X) (_hmem : HasMemory X tau M)
    (_hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (_hpre : ∀ x y : Cfg X, {g | x.val g ≠ y.val g}.Finite → tau x = tau y → x = y)
    (_hU : (F * Delta⁻¹) * M⁻¹ ⊆ U),
    Nat.card (PatX X F) ≤ R.readout () ⟨G, group, A, topology, X, U⟩ tau

private theorem small_pattern_count : Nat.card (PatX full.{u,v} {1}) = 2 := by
  classical
  have hfull : PatX full.{u,v} {1} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    refine ⟨⟨fun _ => p ⟨1, by simp⟩, trivial⟩, ?_⟩
    funext g
    exact congrArg p (Subsingleton.elim _ _)
  rw [hfull, Nat.card_univ, Nat.card_fun]
  simp

private theorem imageZero_rejected : ¬ imageArena.{u,v}.Law imageZero := by
  classical
  intro hlaw
  have hh := @hlaw SmallGroup.{u} inferInstance SmallAlphabet.{v} inferInstance
    inferInstance inferInstance full {1} {1} {1} {1} full_si zero id
    (by intro x y hxy; exact hxy 1 (by simp))
    (fun _ _ => rfl) (fun _ _ _ h => h) (by simp)
  change Nat.card (PatX full {1}) ≤ 0 at hh
  rw [small_pattern_count] at hh
  omega

def imageFamily : Registration imageArena.{u,v} (type_of% (@preinjective_pattern_lower.{u,v})) where
  actual := imageActual
  bridge := Iff.rfl
  variation := ⟨@preinjective_pattern_lower.{u,v}, imageZero, imageZero_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨imageZero, ?_, rfl, imageZero_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let P : WindowInputs.{u,v} := ⟨SmallGroup, inferInstance, SmallAlphabet, inferInstance, full, {1}⟩
    refine ⟨P, id, (fun _ => zero), ?_⟩
    change Nat.card (ImagePat full id {1}) ≠ Nat.card (ImagePat full (fun _ => zero) {1})
    have hi : ImagePat full.{u,v} id {1} = PatX full {1} := rfl
    letI : Nonempty (Cfg full.{u,v}) := ⟨zero⟩
    have hc : Nat.card (ImagePat full.{u,v} (fun _ => zero) {1}) = 1 := by
      simp [ImagePat]
    rw [hi, small_pattern_count, hc]
    omega

def registration_preinjective_pattern_lower : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@preinjective_pattern_lower.{u,v}) (Realization imageSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill.image
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill.imageFamily
  realizationSource := none
  generated := false
  arena := .source ⟨imageArena.{u,v}⟩
  objectArena := .source ⟨imageArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source imageArena.{u,v} ⟨imageFamily.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize imageSignature.{u,v} (fun _ P tau => Nat.card
    (@ImagePat P.1 P.2.1 P.2.2.1 P.2.2.2.1 P.2.2.2.2.1 tau P.2.2.2.2.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
    definition := none
    coordinates := #[0, 1, 2, 3, 6, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev PatternInputs := Σ G : Type u, Σ group : Group G, Σ A : Type v,
  Σ _topology : TopologicalSpace A, Finset G

abbrev patternSignature : Signature where
  Params := PatternInputs.{u,v}
  State P := @MulSubshift P.2.2.1 P.2.2.2.1 P.1 P.2.1.toMonoid
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def patternActual : Realization patternSignature.{u,v} :=
  realize patternSignature (fun _ P X => Nat.card
    (@PatX P.1 P.2.1 P.2.2.1 P.2.2.2.1 X P.2.2.2.2)) (fun e => nomatch e)

def patternLarger : Realization patternSignature.{u,v} :=
  realize patternSignature (fun _ P X => Nat.card
    (@PatX P.1 P.2.1 P.2.2.1 P.2.2.2.1 X P.2.2.2.2) + 1) (fun e => nomatch e)

def patternArena : Arena where
  signature := patternSignature.{u,v}
  Law R := ∀ {G : Type u} [group : Group G] {A : Type v} [topology : TopologicalSpace A]
    [Finite A] (X : MulSubshift A G) (Delta C E F T : Finset G) (w : T → C → A)
    (_hX : X.carrier.Nonempty) (_h1 : 1 ∈ Delta) (_hSI : SI X Delta)
    (_hCE : (C : Set G) * (Delta : Set G)⁻¹ ⊆ (E : Set G))
    (_hin : ∀ t ∈ T, tile t E ⊆ (F : Set G))
    (_hdis : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → Disjoint (tile t E) (tile s E))
    (_hw : ∀ t : T, ∃ x : Cfg X, ∀ c : C, x.val (t.val * c.val) = w t c),
    Nat.card (AvoidPatX X C F T w) * (R.readout () ⟨G, group, A, topology, E⟩ X) ^ T.card ≤
      Nat.card (PatX X F) * (Nat.card (PatX X E) - 1) ^ T.card

private theorem patternLarger_rejected : ¬ patternArena.{u,v}.Law patternLarger := by
  classical
  intro hlaw
  let F : Finset SmallGroup.{u} := {1}
  let w : F → F → SmallAlphabet.{v} := fun _ _ => ⟨false⟩
  have hcol : (F : Set SmallGroup) * (F : Set SmallGroup)⁻¹ ⊆ (F : Set SmallGroup) := by
    simp [F]
  have hin : ∀ t ∈ F, tile t F ⊆ (F : Set SmallGroup) := by
    intro t ht
    have ht' : t = 1 := Finset.mem_singleton.mp ht
    subst t
    simpa [tile] using (Set.Subset.rfl : (F : Set SmallGroup) ⊆ (F : Set SmallGroup))
  have hdis : ∀ t ∈ F, ∀ s ∈ F, t ≠ s → Disjoint (tile t F) (tile s F) := by
    simp only [F, Finset.mem_singleton]
    intro t ht s hs hne
    exact (hne (ht.trans hs.symm)).elim
  have hw : ∀ t : F, ∃ x : Cfg full.{u,v}, ∀ c : F, x.val (t.val * c.val) = w t c :=
    fun _ => ⟨zero, fun _ => rfl⟩
  have hh := @hlaw SmallGroup.{u} inferInstance SmallAlphabet.{v} inferInstance
    inferInstance full F F F F F w ⟨zero.val, zero.property⟩ (by simp [F]) full_si hcol hin hdis hw
  have hN : Nonempty (AvoidPatX full F F F w) := by
    refine ⟨⟨fun _ => one.val 1, ?_⟩⟩
    refine ⟨⟨one, ?_⟩, rfl⟩
    intro t
    refine ⟨⟨1, by simp [F]⟩, ?_⟩
    intro he
    have hc := congrArg ULift.down he
    cases hc
  letI : Nonempty (AvoidPatX full F F F w) := hN
  have hp : 0 < Nat.card (AvoidPatX full F F F w) := Nat.card_pos
  change Nat.card (AvoidPatX full F F F w) * (Nat.card (PatX full F) + 1) ^ F.card ≤
    Nat.card (PatX full F) * (Nat.card (PatX full F) - 1) ^ F.card at hh
  have hcount : Nat.card (PatX full F) = 2 := small_pattern_count
  rw [hcount] at hh
  norm_num only [F, Finset.card_singleton, pow_one, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul] at hh
  omega

private def singletonShift : MulSubshift SmallAlphabet.{v} SmallGroup.{u} where
  carrier := {fun _ => ⟨false⟩}
  isClosed := isClosed_singleton
  mapsTo := by
    intro g x hx
    have hx' : x = fun _ => ULift.up false := hx
    rw [hx']
    exact rfl

private theorem singleton_pattern_count : Nat.card (PatX singletonShift.{u,v} {1}) = 1 := by
  have he : PatX singletonShift.{u,v} {1} = {fun _ => ULift.up false} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      have hx : x.val = fun _ => ULift.up false := x.property
      simp only [hx, Set.mem_singleton_iff]
    · rintro rfl
      exact ⟨⟨fun _ => ULift.up false, rfl⟩, rfl⟩
  simp [he]

def patternFamily : Registration patternArena.{u,v} (type_of% (@relative_pattern_bound.{u,v})) where
  actual := patternActual
  bridge := Iff.rfl
  variation := ⟨@relative_pattern_bound.{u,v}, patternLarger, patternLarger_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨patternLarger, ?_, rfl, patternLarger_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let P : PatternInputs.{u,v} := ⟨SmallGroup, inferInstance, SmallAlphabet, inferInstance, {1}⟩
    refine ⟨P, full, singletonShift, ?_⟩
    change Nat.card (PatX full {1}) ≠ Nat.card (PatX singletonShift {1})
    rw [small_pattern_count, singleton_pattern_count]
    omega

def registration_relative_pattern_bound : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@relative_pattern_bound.{u,v}) (Realization patternSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill.pattern
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill.patternFamily
  realizationSource := none
  generated := false
  arena := .source ⟨patternArena.{u,v}⟩
  objectArena := .source ⟨patternArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source patternArena.{u,v} ⟨patternFamily.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize patternSignature.{u,v} (fun _ P X => Nat.card
    (@PatX P.1 P.2.1 P.2.2.1 P.2.2.2.1 X P.2.2.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
    definition := none
    coordinates := #[0, 1, 2, 3, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
