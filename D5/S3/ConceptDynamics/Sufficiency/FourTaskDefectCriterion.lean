/- GID: D5/S3/ConceptDynamics/Sufficiency/FourTaskDefectCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/FourTaskDefectCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite four-task defect vanishes exactly under target, flow, admit, and anchor descent. -/

import Mathlib.Data.Set.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * Exact-name searches for a four-task defect and the target/flow/admit/anchor conjunction
     found no D5 theorem. `UniversalSufficiencyFactorization` treats one target, while
     `SufficiencyEscapeEquivalence` relates one canonical defect to one factorization; neither
     includes transported flow, propositional admissibility, or a singleton anchor fiber.
   * Symbol and spelling searches covered `FactorsThrough`, `factorization`, `descent`,
     `defectRelation`, `residual`, `fiber`, `admissible`, and `anchor`, with snake_case and
     camelCase variants. The residual, digest, and raw declaration indexes have no equivalent.
   * Generalized searches for simultaneous finite obstruction counts and product-task descent
     found only single-target criteria and no theorem deriving all four public clauses from one
     numeric defect.
   * The in-flight module and branch logs contain no candidate for this result, and the proposed
     module path is absent from `origin/dev`.
   * Pinned Mathlib provides `Set.ncard_eq_zero` and `Function.factorsThrough_iff`; both are used
     directly. The state carrier is explicitly finite because `Set.ncard` is zero on infinite
     sets. The anchor supplies the nonempty target codomains required for total factor maps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.FourTaskDefectCriterion

private def targetDefect
    {X Coordinate Target : Type*}
    (cut : X -> Coordinate) (target : X -> Target) : Set (X × X) :=
  {pair | cut pair.1 = cut pair.2 /\ target pair.1 ≠ target pair.2}

private def flowDefect
    {X Coordinate StateY FlowCoordinate : Type*}
    (cut : X -> Coordinate) (targetCut : StateY -> FlowCoordinate)
    (flow : X -> StateY) : Set (X × X) :=
  {pair |
    cut pair.1 = cut pair.2 /\
      targetCut (flow pair.1) ≠ targetCut (flow pair.2)}

private def admitDefect
    {X Coordinate : Type*}
    (cut : X -> Coordinate) (admit : X -> Prop) : Set (X × X) :=
  {pair | cut pair.1 = cut pair.2 /\ ¬(admit pair.1 ↔ admit pair.2)}

private def anchorDefect
    {X Coordinate : Type*}
    (cut : X -> Coordinate) (anchor : X) : Set X :=
  {state | cut state = cut anchor /\ state ≠ anchor}

/-- The four-task defect counts, on a finite state carrier, target disagreements,
transported-flow disagreements, admissibility disagreements, and non-anchor states
in the anchor fiber. Finiteness is part of the definition's interface so an infinite
defect set cannot silently receive `Set.ncard = 0`. -/
noncomputable def fourTaskDefect
    {X Coordinate StateY FlowCoordinate Target : Type*} [Finite X]
    (cut : X -> Coordinate) (target : X -> Target)
    (targetCut : StateY -> FlowCoordinate) (flow : X -> StateY)
    (admit : X -> Prop) (anchor : X) : Nat :=
  (targetDefect cut target).ncard +
    (flowDefect cut targetCut flow).ncard +
    (admitDefect cut admit).ncard +
    (anchorDefect cut anchor).ncard

/-- The finite four-task defect is zero exactly when the target and transported
flow factor through CUT, admissibility descends along CUT, and the anchor fiber is
a singleton. The conclusion is task-relative: it asserts only these four named
factorizations and no absolute completeness property. -/
theorem four_task_defect_zero_iff
    {X Coordinate StateY FlowCoordinate Target : Type*} [Finite X]
    (cut : X -> Coordinate) (target : X -> Target)
    (targetCut : StateY -> FlowCoordinate) (flow : X -> StateY)
    (admit : X -> Prop) (anchor : X) :
    fourTaskDefect cut target targetCut flow admit anchor = 0 ↔
      (exists descendedTarget : Coordinate -> Target,
        target = descendedTarget ∘ cut) /\
      (exists descendedFlow : Coordinate -> FlowCoordinate,
        targetCut ∘ flow = descendedFlow ∘ cut) /\
      (exists descendedAdmit : Coordinate -> Prop,
        forall state, admit state ↔ descendedAdmit (cut state)) /\
      (forall state, cut state = cut anchor -> state = anchor) := by
  classical
  letI : Nonempty Target := ⟨target anchor⟩
  letI : Nonempty FlowCoordinate := ⟨targetCut (flow anchor)⟩
  unfold fourTaskDefect
  constructor
  · intro defectZero
    have targetCardZero : (targetDefect cut target).ncard = 0 := by omega
    have flowCardZero : (flowDefect cut targetCut flow).ncard = 0 := by omega
    have admitCardZero : (admitDefect cut admit).ncard = 0 := by omega
    have anchorCardZero : (anchorDefect cut anchor).ncard = 0 := by omega
    have targetEmpty : targetDefect cut target = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).mp targetCardZero
    have flowEmpty : flowDefect cut targetCut flow = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).mp flowCardZero
    have admitEmpty : admitDefect cut admit = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).mp admitCardZero
    have anchorEmpty : anchorDefect cut anchor = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).mp anchorCardZero
    have targetFactors : target.FactorsThrough cut := by
      intro left right sameCut
      by_contra differentTarget
      have escaped : (left, right) ∈ targetDefect cut target :=
        ⟨sameCut, differentTarget⟩
      rw [targetEmpty] at escaped
      exact escaped
    have flowFactors : (targetCut ∘ flow).FactorsThrough cut := by
      intro left right sameCut
      by_contra differentFlow
      have escaped : (left, right) ∈ flowDefect cut targetCut flow :=
        ⟨sameCut, differentFlow⟩
      rw [flowEmpty] at escaped
      exact escaped
    have admitFactors : admit.FactorsThrough cut := by
      intro left right sameCut
      apply propext
      by_contra differentAdmit
      have escaped : (left, right) ∈ admitDefect cut admit :=
        ⟨sameCut, differentAdmit⟩
      rw [admitEmpty] at escaped
      exact escaped
    have anchorSingleton : forall state, cut state = cut anchor -> state = anchor := by
      intro state sameCut
      by_contra differentAnchor
      have escaped : state ∈ anchorDefect cut anchor :=
        ⟨sameCut, differentAnchor⟩
      rw [anchorEmpty] at escaped
      exact escaped
    obtain ⟨descendedTarget, targetEquation⟩ :=
      (Function.factorsThrough_iff (f := cut) target).mp targetFactors
    obtain ⟨descendedFlow, flowEquation⟩ :=
      (Function.factorsThrough_iff (f := cut) (targetCut ∘ flow)).mp flowFactors
    obtain ⟨descendedAdmit, admitEquation⟩ :=
      (Function.factorsThrough_iff (f := cut) admit).mp admitFactors
    have admitIff : forall state, admit state ↔ descendedAdmit (cut state) := by
      intro state
      simpa only [admitEquation, Function.comp_apply]
    exact ⟨⟨descendedTarget, targetEquation⟩,
      ⟨descendedFlow, flowEquation⟩,
      ⟨descendedAdmit, admitIff⟩, anchorSingleton⟩
  · rintro ⟨⟨descendedTarget, targetEquation⟩,
      ⟨descendedFlow, flowEquation⟩,
      ⟨descendedAdmit, admitIff⟩, anchorSingleton⟩
    have targetEmpty : targetDefect cut target = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨left, right⟩ ⟨sameCut, differentTarget⟩
      apply differentTarget
      rw [targetEquation]
      simpa only [Function.comp_apply] using congrArg descendedTarget sameCut
    have flowEmpty : flowDefect cut targetCut flow = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨left, right⟩ ⟨sameCut, differentFlow⟩
      apply differentFlow
      calc
        targetCut (flow left) = descendedFlow (cut left) := by
          simpa only [Function.comp_apply] using congrFun flowEquation left
        _ = descendedFlow (cut right) := congrArg descendedFlow sameCut
        _ = targetCut (flow right) := by
          simpa only [Function.comp_apply] using (congrFun flowEquation right).symm
    have admitEmpty : admitDefect cut admit = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨left, right⟩ ⟨sameCut, differentAdmit⟩
      apply differentAdmit
      calc
        admit left ↔ descendedAdmit (cut left) := admitIff left
        _ ↔ descendedAdmit (cut right) := by rw [sameCut]
        _ ↔ admit right := (admitIff right).symm
    have anchorEmpty : anchorDefect cut anchor = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro state
      rintro ⟨sameCut, differentAnchor⟩
      exact differentAnchor (anchorSingleton state sameCut)
    rw [targetEmpty, flowEmpty, admitEmpty, anchorEmpty]
    simp

#print axioms fourTaskDefect
#print axioms four_task_defect_zero_iff

end D5.S3.ConceptDynamics.Sufficiency.FourTaskDefectCriterion
