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

end Reg.D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
