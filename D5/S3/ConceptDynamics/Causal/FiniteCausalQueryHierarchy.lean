/- GID: D5/S3/ConceptDynamics/Causal/FiniteCausalQueryHierarchy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/FiniteCausalQueryHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Genuine causal query profiles form a strict hierarchy on one finite Boolean SCM class. -/

import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation

/- Library-search audit trail (2026-08-26):
   * The withdrawn chain was not reused: it defines observation as one treatment
     slice and therefore does not encode the source's passive joint law.
   * `ObservationInterventionSeparation` contains the genuine section-258
     direction witness and supplies the canonical causal-direction type.
   * `InterventionCounterfactualSeparation` contains the section-285 witness on
     a different carrier. Body-shape searches found no common carrier capable of
     representing both reverse direction and independent child noise.
   * The existing four-point `endogenousLaw` is tied to that section-285 carrier
     and has no empty-intervention regime, so it cannot be instantiated here.
   * Pinned Mathlib searches for structural causal models, interventions, and
     counterfactuals returned no formal theorem or reusable causal carrier.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.FiniteCausalQueryHierarchy

open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation

/-- A two-node recursive Boolean SCM. The first mechanism generates the root;
the second generates the child from the same exogenous state and the root. -/
structure FiniteBoolSCM where
  direction : CausalDirection
  root : Bool × Bool -> Bool
  child : Bool × Bool -> Bool -> Bool

/-- The empty intervention and every single-node perfect intervention. -/
inductive QueryRegime where
  | observe
  | setX : Bool -> QueryRegime
  | setY : Bool -> QueryRegime

/-- Structural evaluation after replacing exactly the mechanism named by the
query regime. The observational branch replaces no mechanism. -/
def response (model : FiniteBoolSCM) (regime : QueryRegime)
    (exogenous : Bool × Bool) : Bool × Bool :=
  match regime, model.direction with
  | .observe, .xCausesY =>
      let x := model.root exogenous
      (x, model.child exogenous x)
  | .observe, .yCausesX =>
      let y := model.root exogenous
      (model.child exogenous y, y)
  | .setX x, .xCausesY => (x, model.child exogenous x)
  | .setX x, .yCausesX => (x, model.root exogenous)
  | .setY y, .xCausesY => (model.root exogenous, y)
  | .setY y, .yCausesX => (model.child exogenous y, y)

/-- The joint count law on the uniform four-point exogenous population. -/
def jointLaw (model : FiniteBoolSCM) (regime : QueryRegime)
    (result : Bool × Bool) : Nat :=
  (if response model regime (false, false) = result then 1 else 0) +
    (if response model regime (false, true) = result then 1 else 0) +
    (if response model regime (true, false) = result then 1 else 0) +
    if response model regime (true, true) = result then 1 else 0

/-- The genuine passive joint law: no structural mechanism is replaced. -/
def Obs (model : FiniteBoolSCM) : Bool × Bool -> Nat :=
  jointLaw model .observe

/-- The full single-world profile, including the empty intervention. -/
def Int (model : FiniteBoolSCM) : QueryRegime -> Bool × Bool -> Nat :=
  jointLaw model

/-- The unit-preserving response profile, retaining cross-world coupling. -/
def CF (model : FiniteBoolSCM) : QueryRegime -> Bool × Bool -> Bool × Bool :=
  response model

/-- Section 258.A: `X` is the root and `Y` copies `X`. -/
def observationalForwardModel : FiniteBoolSCM where
  direction := .xCausesY
  root := fun exogenous => exogenous.1
  child := fun _exogenous x => x

/-- Section 258.B: `Y` is the root and `X` copies `Y`. -/
def observationalReverseModel : FiniteBoolSCM where
  direction := .yCausesX
  root := fun exogenous => exogenous.1
  child := fun _exogenous y => y

/-- Section 285.S: randomized `X` and independent stable outcome noise. -/
def stableCouplingModel : FiniteBoolSCM where
  direction := .xCausesY
  root := fun exogenous => exogenous.1
  child := fun exogenous _x => exogenous.2

/-- Section 285.F: randomized `X` flips the independent outcome noise. -/
def flipCouplingModel : FiniteBoolSCM where
  direction := .xCausesY
  root := fun exogenous => exogenous.1
  child := fun exogenous x => if x then !exogenous.2 else exogenous.2

/-- On one finite SCM class, counterfactual equality refines full single-world
intervention equality, which refines genuine observational equality; the exact
source pairs witness that both refinements are strict. -/
theorem finite_causal_query_hierarchy :
    (forall M N : FiniteBoolSCM, CF M = CF N -> Int M = Int N) ∧
      (forall M N : FiniteBoolSCM, Int M = Int N -> Obs M = Obs N) ∧
      (Obs observationalForwardModel = Obs observationalReverseModel ∧
        Int observationalForwardModel ≠ Int observationalReverseModel) ∧
      (Int stableCouplingModel = Int flipCouplingModel ∧
        CF stableCouplingModel ≠ CF flipCouplingModel) := by
  constructor
  · intro M N counterfactualsEqual
    funext regime result
    have responseEqual : forall exogenous : Bool × Bool,
        response M regime exogenous = response N regime exogenous := by
      intro exogenous
      exact congrFun (congrFun counterfactualsEqual regime) exogenous
    simp only [Int, jointLaw]
    rw [responseEqual (false, false), responseEqual (false, true),
      responseEqual (true, false), responseEqual (true, true)]
  constructor
  · intro M N interventionsEqual
    exact congrFun interventionsEqual .observe
  constructor
  · constructor
    · funext result
      rcases result with ⟨x, y⟩
      cases x <;> cases y <;> rfl
    · intro interventionsEqual
      have countEqual := congrFun
        (congrFun interventionsEqual (.setX false)) (false, false)
      simp [Int, jointLaw, response, observationalForwardModel,
        observationalReverseModel] at countEqual
  · constructor
    · funext regime result
      rcases result with ⟨x, y⟩
      cases regime with
      | observe => cases x <;> cases y <;> rfl
      | setX treatment => cases treatment <;> cases x <;> cases y <;> rfl
      | setY outcome => cases outcome <;> cases x <;> cases y <;> rfl
    · intro counterfactualsEqual
      have responseEqual := congrFun
        (congrFun counterfactualsEqual (.setX true)) (false, false)
      have falseEqualTrue : false = true := by
        simpa [CF, response, stableCouplingModel, flipCouplingModel] using
          congrArg Prod.snd responseEqual
      exact Bool.false_ne_true falseEqualTrue

#print axioms finite_causal_query_hierarchy

end D5.S3.ConceptDynamics.Causal.FiniteCausalQueryHierarchy
