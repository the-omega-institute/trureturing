import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.Dynamics.TopologicalFactorMinimality

/-! Dependent-family registrations for the two topological factor laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.Dynamics.TopologicalFactorMinimality

open Set Function
open _root_.D5.S3.Observer.Dynamics.TopologicalFactorMinimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

namespace Additive

universe u v w

structure Inputs where
  M : Type u
  addM : AddMonoid M
  X : Type v
  topX : TopologicalSpace X
  Y : Type w
  topY : TopologicalSpace Y
  actionX : AddAction M X
  actionY : AddAction M Y
  minimalX : @AddAction.IsMinimal M X addM topX actionX
  f : X → Y
  hf : @Continuous X Y topX topY f
  hsurj : Function.Surjective f
  hequiv :
    ∀ m x,
      f (@VAdd.vadd M X
        (@AddSemigroupAction.toVAdd M X _ actionX.toAddSemigroupAction) m x) =
      @VAdd.vadd M Y
        (@AddSemigroupAction.toVAdd M Y _ actionY.toAddSemigroupAction) m (f x)

def goal (p : Inputs.{u, v, w}) : Prop :=
  @AddAction.IsMinimal p.M p.Y p.addM p.topY p.actionY

abbrev signature : Signature where
  Params := Inputs.{u, v, w}
  State := fun _ => Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v, w} :=
  realize signature
    (fun _ p b => if b then goal p else ¬ goal p)
    (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{u, v, w}
  Law R := ∀ p, R.readout () p true

abbrev sourceScope := type_of% (@continuous_surjective_equivariant_minimality.{u, v, w})

theorem bridge : sourceScope.{u, v, w} ↔ arena.{u, v, w}.Law actual.{u, v, w} := by
  constructor
  · intro h p
    change goal p
    exact @h p.M p.X p.Y p.addM p.topX p.topY p.actionX p.actionY
      p.minimalX p.f p.hf p.hsurj p.hequiv
  · intro h M X Y addM topX topY actionX actionY minimalX f hf hsurj hequiv
    exact h ⟨M, addM, X, topX, Y, topY, actionX, actionY, minimalX,
      f, hf, hsurj, hequiv⟩

theorem actual_positive : arena.{u, v, w}.Law actual.{u, v, w} :=
  bridge.mp (@continuous_surjective_equivariant_minimality.{u, v, w})

def trivialInputs : Inputs.{u, v, w} := by
  let actX : AddAction (ULift.{u} ℕ) (ULift.{v} PUnit.{1}) := {
    vadd := fun _ x => x
    zero_vadd := fun _ => rfl
    add_vadd := fun _ _ _ => rfl }
  let actY : AddAction (ULift.{u} ℕ) (ULift.{w} PUnit.{1}) := {
    vadd := fun _ x => x
    zero_vadd := fun _ => rfl
    add_vadd := fun _ _ _ => rfl }
  have min : @AddAction.IsMinimal (ULift.{u} ℕ) (ULift.{v} PUnit.{1})
      inferInstance ULift.topologicalSpace actX := by
    refine ⟨?_⟩
    intro x
    rw [show AddAction.orbit (ULift.{u} ℕ) x = Set.univ by
      ext z
      constructor
      · intro hz
        trivial
      · intro hz
        refine ⟨0, ?_⟩
        exact Subsingleton.elim _ _]
    exact dense_univ
  exact {
    M := ULift.{u} ℕ
    addM := inferInstance
    X := ULift.{v} PUnit.{1}
    topX := ULift.topologicalSpace
    Y := ULift.{w} PUnit.{1}
    topY := ULift.topologicalSpace
    actionX := actX
    actionY := actY
    minimalX := min
    f := fun x => (⟨x.down⟩ : ULift.{w} PUnit.{1})
    hf := continuous_of_const (by intro x y; cases x; cases y; rfl)
    hsurj := by
      intro y
      refine ⟨(⟨y.down⟩ : ULift.{v} PUnit.{1}), ?_⟩
      cases y
      rfl
    hequiv := by intro m x; rfl }

def rejected : Realization signature.{u, v, w} :=
  realize signature (fun _ _ _ => False) (fun a => nomatch a)

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  have hp := h (trivialInputs.{u, v, w})
  simpa [rejected, realize] using hp

private theorem dependence :
    ObservationalDependence signature.{u, v, w} actual.{u, v, w} := by
  intro i
  refine ⟨trivialInputs.{u, v, w}, true, false, ?_⟩
  by_cases hp : goal (trivialInputs.{u, v, w})
  · simp [actual, realize, hp]
  · simp [actual, realize, hp]

def evidence : Registration arena.{u, v, w} sourceScope.{u, v, w} :=
  { actual := actual
    bridge := bridge
    variation := ⟨actual_positive, rejected, rejected_law⟩
    sensitivity := by
      constructor
      · intro i
        refine ⟨rejected, ?_, rfl, rejected_law⟩
        intro j hji
        exact False.elim (hji (@Subsingleton.elim Unit _ j i))
      · intro a
        exact Empty.elim a
    dependence := dependence }

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@continuous_surjective_equivariant_minimality.{u, v, w})
      (Realization signature.{u, v, w}) Unit Unit where
  unitName := `Reg.D5.S3.Observer.Dynamics.TopologicalFactorMinimality.continuous_surjective_equivariant_minimality__information_unit
  realizationName := `Reg.D5.S3.Observer.Dynamics.TopologicalFactorMinimality.Additive.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ trivial
  readout := some actual
  variation := .evidence ⟨True.intro⟩ trivial
  sensitivity := .evidence ⟨True.intro⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Additive

namespace Forward

universe u v

structure Inputs where
  X : Type u
  topX : TopologicalSpace X
  Y : Type v
  topY : TopologicalSpace Y
  f : X → X
  g : Y → Y
  factor : X → Y
  hfactor : @Continuous X Y topX topY factor
  hsurj : Function.Surjective factor
  hsemiconj : @Function.Semiconj X Y factor f g
  hminimal : ∀ x : X, Dense (Set.range fun n : ℕ => (f^[n]) x)

attribute [instance] Inputs.topX Inputs.topY

def goal (p : Inputs.{u, v}) : Prop :=
  ∀ y : p.Y, Dense (Set.range fun n : ℕ => (p.g^[n]) y)

abbrev signature : Signature where
  Params := Inputs.{u, v}
  State := fun _ => Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature
    (fun _ p b => if b then goal p else ¬ goal p)
    (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ p, R.readout () p true

abbrev sourceScope := type_of% (@dense_forward_orbit_of_continuous_surjective_semiconj.{u, v})

theorem bridge : sourceScope.{u, v} ↔ arena.{u, v}.Law actual.{u, v} := by
  constructor
  · intro h p
    change goal p
    exact @h p.X p.Y p.topX p.topY p.f p.g p.factor
      p.hfactor p.hsurj p.hsemiconj p.hminimal
  · intro h X Y topX topY f g factor hfactor hsurj hsemiconj hminimal
    exact h ⟨X, topX, Y, topY, f, g, factor, hfactor, hsurj, hsemiconj, hminimal⟩

theorem actual_positive : arena.{u, v}.Law actual.{u, v} :=
  bridge.mp (@dense_forward_orbit_of_continuous_surjective_semiconj.{u, v})

def trivialInputs : Inputs.{u, v} := {
  X := ULift.{u} PUnit.{1}
  topX := ULift.topologicalSpace
  Y := ULift.{v} PUnit.{1}
  topY := ULift.topologicalSpace
  f := id
  g := id
  factor := fun x => (⟨x.down⟩ : ULift.{v} PUnit.{1})
  hfactor := continuous_of_const (by intro x y; cases x; cases y; rfl)
  hsurj := by
    intro y
    refine ⟨(⟨y.down⟩ : ULift.{u} PUnit.{1}), ?_⟩
    cases y
    rfl
  hsemiconj := by intro x; rfl
  hminimal := by
    intro x
    rw [show Set.range (fun n : ℕ => (id^[n]) x) = Set.univ by
      ext z
      simp [Subsingleton.elim z x]]
    exact dense_univ }

def rejected : Realization signature.{u, v} :=
  realize signature (fun _ _ _ => False) (fun a => nomatch a)

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hp := h (trivialInputs.{u, v})
  simpa [rejected, realize] using hp

private theorem dependence :
    ObservationalDependence signature.{u, v} actual.{u, v} := by
  intro i
  refine ⟨trivialInputs.{u, v}, true, false, ?_⟩
  by_cases hp : goal (trivialInputs.{u, v})
  · simp [actual, realize, hp]
  · simp [actual, realize, hp]

def evidence : Registration arena.{u, v} sourceScope.{u, v} :=
  { actual := actual
    bridge := bridge
    variation := ⟨actual_positive, rejected, rejected_law⟩
    sensitivity := by
      constructor
      · intro i
        refine ⟨rejected, ?_, rfl, rejected_law⟩
        intro j hji
        exact False.elim (hji (@Subsingleton.elim Unit _ j i))
      · intro a
        exact Empty.elim a
    dependence := dependence }

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@dense_forward_orbit_of_continuous_surjective_semiconj.{u, v})
      (Realization signature.{u, v}) Unit Unit where
  unitName := `Reg.D5.S3.Observer.Dynamics.TopologicalFactorMinimality.dense_forward_orbit_of_continuous_surjective_semiconj__information_unit
  realizationName := `Reg.D5.S3.Observer.Dynamics.TopologicalFactorMinimality.Forward.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ trivial
  readout := some actual
  variation := .evidence ⟨True.intro⟩ trivial
  sensitivity := .evidence ⟨True.intro⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Forward

end
end Reg.D5.S3.Observer.Dynamics.TopologicalFactorMinimality
