import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
import D5.S1.Dynamics.Symbolic.FiniteTypeMoore

/-! Source-bound replacement and Moore families on the original configuration carrier. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
open _root_.D5.S1.Dynamics.Symbolic.FiniteTypeMoore
open _root_.Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
open SymbolicDynamics.FullShift Set Function MeasureTheory Filter
open scoped Pointwise Topology

namespace Reg.D5.S1.Dynamics.Symbolic.FiniteTypeMoore

private theorem full_finite_type : IsFiniteType full.{u,v} := by
  refine ⟨⟨false⟩, ∅, ?_⟩
  ext x
  simp [full, mulFullShift, mulForbidden]

def mooreArena : Arena where
  signature := codeSignature.{u,v}
  Law R := ∀ {G : Type u} [group : Group G] {A : Type v} [topology : TopologicalSpace A]
    [Finite A] [DiscreteTopology A]
    (_ham : letI : MeasurableSpace G := ⊤
      NeBot (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)))
    (X : MulSubshift A G) (_hX : X.carrier.Nonempty)
    (_hSI : ∃ Delta : Finset G, SI X Delta) (_hft : IsFiniteType X)
    (tau : Cfg X → Cfg X) (_htau : Continuous tau)
    (_hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (_hsurj : Surjective tau),
    ∀ x y : Cfg X, {g | x.val g ≠ y.val g}.Finite →
      R.readout () ⟨G, group, A, topology, X, tau⟩ x = tau y → x = y

private theorem mooreConstant_rejected : ¬ mooreArena.{u,v}.Law codeConstant := by
  classical
  intro hlaw
  let P : CodeInputs.{u,v} := ⟨SmallGroup, inferInstance, SmallAlphabet, inferInstance, full, id⟩
  have he : codeConstant.readout () P zero = codeConstant.readout () P one := by
    have hN : Nonempty (Config (codeBase P)) := ⟨zero⟩
    simp only [codeConstant, realize, dite_eq_left hN]
  have hpre := @hlaw SmallGroup.{u} inferInstance SmallAlphabet.{v} inferInstance
    inferInstance inferInstance
    (_root_.Reg.D5.S1.Dynamics.Symbolic.AmenableGardenOfEden.finite_amenable SmallGroup.{u})
    full ⟨zero.val, zero.property⟩ ⟨{1}, full_si⟩ full_finite_type id continuous_id
    (fun _ _ => rfl) Function.surjective_id
  exact zero_ne_one ((hpre zero (codeConstant.readout () P zero) (Set.toFinite _) rfl).trans
    (hpre one (codeConstant.readout () P zero) (Set.toFinite _) he.symm).symm)

def mooreFamily : Registration mooreArena.{u,v} (type_of% (@moore.{u,v})) where
  actual := codeActual
  bridge := Iff.rfl
  variation := ⟨@moore.{u,v}, codeConstant, mooreConstant_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨codeConstant, ?_, rfl, mooreConstant_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let P : CodeInputs.{u,v} := ⟨SmallGroup, inferInstance, SmallAlphabet, inferInstance, full, id⟩
    exact ⟨P, zero, one, zero_ne_one⟩

def registration_moore : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moore.{u,v}) (Realization codeSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.FiniteTypeMoore.moore
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.FiniteTypeMoore.mooreFamily
  realizationSource := none
  generated := false
  arena := .source ⟨mooreArena.{u,v}⟩
  objectArena := .source ⟨mooreArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source mooreArena.{u,v} ⟨mooreFamily.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize codeSignature.{u,v} (fun _ P => P.2.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.FiniteTypeMoore
    definition := none
    coordinates := #[0, 1, 2, 3, 7, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev ReplacementInputs := Σ G : Type u, Σ group : Group G, Σ A : Type v,
  Σ topology : TopologicalSpace A, Σ X : @MulSubshift A topology G group.toMonoid,
    Σ C : Finset G, Σ _t : G, Σ _z : @Cfg G group A topology X, C

abbrev replacementBase (P : ReplacementInputs.{u,v}) : BaseInputs.{u,v} :=
  ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1, P.2.2.2.2.1⟩

abbrev replacementSignature : Signature where
  Params := ReplacementInputs.{u,v}
  State P := Config (replacementBase P)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def replacementActual : Realization replacementSignature.{u,v} :=
  realize replacementSignature (fun _ P z => letI : Group P.1 := P.2.1
    z.val (P.2.2.2.2.2.2.1 * P.2.2.2.2.2.2.2.2.val)) (fun e => nomatch e)

def replacementBackground : Realization replacementSignature.{u,v} :=
  realize replacementSignature (fun _ P _ => letI : Group P.1 := P.2.1
    P.2.2.2.2.2.2.2.1.val (P.2.2.2.2.2.2.1 * P.2.2.2.2.2.2.2.2.val))
    (fun e => nomatch e)

def replacementArena : Arena where
  signature := replacementSignature.{u,v}
  Law R := ∀ {G : Type u} [group : Group G] {A : Type v} [topology : TopologicalSpace A]
    [Finite A] [DiscreteTopology A]
    (X : MulSubshift A G) (_hft : IsFiniteType X)
    (tau : Cfg X → Cfg X) (_htau : Continuous tau)
    (_hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (x y : Cfg X) (_hne : x ≠ y) (_hf : Set.Finite {g | x.val g ≠ y.val g})
    (_hi : tau x = tau y),
    ∃ C : Finset G, C.Nonempty ∧ ∃ p q : C → A,
      p ≠ q ∧ p ∈ PatX X C ∧ q ∈ PatX X C ∧
      ∀ (t : G) (z : Cfg X), (∀ c : C, z.val (t * c) = p c) →
        ∃ z' : Cfg X,
          (∀ c : C, R.readout () ⟨G, group, A, topology, X, C, t, z, c⟩ z' = q c) ∧
          (∀ g, g ∉ tile t C → z'.val g = z.val g) ∧ tau z' = tau z

private theorem replacementBackground_rejected :
    ¬ replacementArena.{u,v}.Law replacementBackground := by
  classical
  intro hlaw
  obtain ⟨C, _hC, p, q, hpq, hp, _hq, hr⟩ :=
    @hlaw SmallGroup.{u} inferInstance SmallAlphabet.{v} inferInstance
      inferInstance inferInstance full full_finite_type (fun _ => zero) continuous_const
      (by intro g x; apply Subtype.ext; funext h; rfl)
      zero one zero_ne_one (Set.toFinite _) rfl
  obtain ⟨z, hz⟩ := hp
  have hz1 : ∀ c : C, z.val (1 * c) = p c := by
    intro c
    simpa only [one_mul] using congrFun hz c
  obtain ⟨w, hw, _⟩ := hr 1 z hz1
  apply hpq
  funext c
  exact (hz1 c).symm.trans (hw c)

def replacementFamily : Registration replacementArena.{u,v}
    (type_of% (@collision_replacement.{u,v})) where
  actual := replacementActual
  bridge := Iff.rfl
  variation := ⟨@collision_replacement.{u,v}, replacementBackground, replacementBackground_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨replacementBackground, ?_, rfl, replacementBackground_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let P : ReplacementInputs.{u,v} :=
      ⟨SmallGroup, inferInstance, SmallAlphabet, inferInstance, full, {1}, 1, zero, ⟨1, by simp⟩⟩
    refine ⟨P, zero, one, ?_⟩
    intro h
    have hh := congrArg ULift.down h
    cases hh

def registration_collision_replacement : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@collision_replacement.{u,v}) (Realization replacementSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.FiniteTypeMoore.replacement
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.FiniteTypeMoore.replacementFamily
  realizationSource := none
  generated := false
  arena := .source ⟨replacementArena.{u,v}⟩
  objectArena := .source ⟨replacementArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source replacementArena.{u,v} ⟨replacementFamily.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize replacementSignature.{u,v}
    (fun _ P z => letI : Group P.1 := P.2.1
      z.val (P.2.2.2.2.2.2.1 * P.2.2.2.2.2.2.2.2.val)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.FiniteTypeMoore
    definition := none
    coordinates := #[0, 1, 2, 3, 6, 16, 19, 20, 23]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "arg", "body", "arg", "arg", "arg",
        "body", "body", "body", "arg", "body", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.Symbolic.FiniteTypeMoore
