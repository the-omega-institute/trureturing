/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnDecidableEquivalence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnDecidableEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite-carrier weak Pareto symmetric kernel is a decidable equivalence. -/

import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.ParetoWeakPreorder
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Basic

/- Library-search audit trail (2026-08-27):
   * Two collision searches for `ParetoEqOn`, `ParetoWeakOn`, `ParetoCarrier`,
     `carrierEnum`, and the planned declaration names found no D5 definitions.
   * Searches for symmetric kernels and equivalence relations found several
     `Setoid.ker` uses, but those concern equality kernels of functions rather
     than the symmetric kernel of an arbitrary preorder relation.
   * The frozen `pareto_weak_reflexive_transitive` theorem is the exact source
     for the required reflexivity and transitivity arguments and is reused below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u

/-- The finite carrier cut out by an action finset. -/
abbrev ParetoCarrier {Action : Type u} [DecidableEq Action]
    (F : Finset Action) := {action : Action // action ∈ F}

/-- The explicit enumeration of every member of the finite Pareto carrier. -/
def carrierEnum {Action : Type u} [DecidableEq Action]
    (F : Finset Action) : Finset (ParetoCarrier F) :=
  F.attach

/-- Weak Pareto dominance restricted to the finite carrier `F`. -/
def ParetoWeakOn
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (x y : ParetoCarrier F) : Prop :=
  ParetoWeak value x.1 y.1

/-- The symmetric kernel of weak Pareto dominance on the finite carrier. -/
def ParetoEqOn
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (x y : ParetoCarrier F) : Prop :=
  ParetoWeakOn value F x y ∧ ParetoWeakOn value F y x

/-- Five decidable coordinate comparisons decide the symmetric Pareto kernel. -/
def paretoEqOnDecidable
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    [DecidableRel ((· ≤ ·) : Information → Information → Prop)]
    [DecidableRel ((· ≤ ·) : Residual → Residual → Prop)]
    [DecidableRel ((· ≤ ·) : Transfer → Transfer → Prop)]
    [DecidableRel ((· ≤ ·) : Cost → Cost → Prop)]
    [DecidableRel ((· ≤ ·) : Risk → Risk → Prop)]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (x y : ParetoCarrier F) :
    Decidable (ParetoEqOn value F x y) := by
  unfold ParetoEqOn ParetoWeakOn ParetoWeak
  infer_instance

/-- The symmetric kernel is reflexive, symmetric, and transitive. -/
theorem pareto_eq_on_equivalence_laws
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [Preorder Information] [Preorder Residual] [Preorder Transfer]
    [Preorder Cost] [Preorder Risk]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) :
    (∀ x : ParetoCarrier F, ParetoEqOn value F x x) ∧
      (∀ x y : ParetoCarrier F,
        ParetoEqOn value F x y → ParetoEqOn value F y x) ∧
      (∀ x y z : ParetoCarrier F,
        ParetoEqOn value F x y → ParetoEqOn value F y z →
          ParetoEqOn value F x z) := by
  rcases pareto_weak_reflexive_transitive value with ⟨hreflexive, htransitive⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨hreflexive x.1, hreflexive x.1⟩
  · intro x y hxy
    exact ⟨hxy.2, hxy.1⟩
  · intro x y z hxy hyz
    exact
      ⟨htransitive hxy.1 hyz.1,
        htransitive hyz.2 hxy.2⟩

/-- A checked inhabited finite carrier with satisfiable decidable-preorder
hypotheses where the symmetric kernel distinguishes two actions. -/
example :
    let F : Finset Bool := {false, true}
    let value : Bool → GainVector Nat Nat Nat Nat Nat := fun action =>
      if action then
        { information := 1
          residualCapture := 1
          transfer := 1
          lifecycleCost := 0
          risk := 0 }
      else
        { information := 0
          residualCapture := 0
          transfer := 0
          lifecycleCost := 1
          risk := 1 }
    ∃ x y : ParetoCarrier F,
      ParetoEqOn value F x x ∧ ¬ ParetoEqOn value F x y := by
  dsimp
  refine ⟨⟨false, by simp⟩, ⟨true, by simp⟩, ?_, ?_⟩
  · exact (pareto_eq_on_equivalence_laws _ _).1 _
  · simp [ParetoEqOn, ParetoWeakOn, ParetoWeak]

#print axioms pareto_eq_on_equivalence_laws

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
