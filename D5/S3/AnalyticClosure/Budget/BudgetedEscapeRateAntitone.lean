/- GID: D5/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Budgeted escape rates lie in the unit interval and are antitone in budget. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'budgeted_escape_rate_bounds_and_antitone' D5
     Golden/Frozen/accepted` returned no matches (exit 1).
   * Type-shape search `rg -n 'Set \(X × X\)|Set \([^)]* × [^)]*\)'
     D5/S3 --glob '*.lean'` found the canonical `defectRelation` in
     `RefinementRiskCostTradeoff`, plus neighboring readout-kernel relations.
     This module imports and applies `defectRelation` instead of defining a
     second target-defect or escape-residual set.
   * Chinese/English synonym search `rg -n -i '预算逃逸|逃逸率|不可消除逃逸|残差率|
     预算下确界|可行集|budget(ed)? escape|escape rate|unavoidable escape|
     residual rate|cost-constrained|cost constrained|feasible set|budget.*inf|
     inf.*budget' D5 Blueprint Golden/Frozen/accepted` found this module's own
     new declarations, the unrelated finite `TransitiveEscapeRate`, and budget
     or feasible-set prose, but no pre-existing cost-constrained infimum of
     normalized target-defect mass.
   * Neighbor inspection `ls D5/S3/AnalyticClosure
     D5/S3/ConceptDynamics/{TargetRisk,DefinitionEscape}` and
     `git grep -n -E '^def |^  def |^noncomputable def ' --
     D5/S3/AnalyticClosure | head -60` found no reusable budgeted escape-rate
     definition; the sole AnalyticClosure definition hit was `metallicBeta`.
   * Weight-interface search `rg -n -i 'structure .*weight|def .*weight|
     mass.*∅|∅.*mass|nonnegative.*mass|measure.*weight|weight.*measure' D5
     --glob '*.lean'` found pointwise finite mass functions and standard
     `Measure` uses, but no real-valued set weight carrying zero-empty and
     nonnegativity laws. `EscapeWeight` below is the minimal interface for
     exactly those source-required laws; no unused monotonicity law is added.
   * The canonical `Concept`, `conceptJoin`, and `defectRelation` declarations
     are imported and used directly. Pinned Mathlib exact hit
     `csInf_le_csInf` supplies reversed infimum monotonicity, while
     `le_csInf_iff` and `csInf_le` supply the two bounds. `loogle` and
     `leansearch` were unavailable on PATH (both commands exited 1). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- A real-valued weight on sets: the empty set has zero mass, and every set
has nonnegative mass. These are exactly the weight laws used by this module. -/
structure EscapeWeight (Omega : Type*) where
  mass : Set Omega -> Real
  empty_mass : mass ∅ = 0
  mass_nonnegative : forall set, 0 <= mass set

/-- Normalized escape-mass values attained by supplements whose cost is at
most the supplied budget. The normalizer is definitionally the mass of the
base target-defect relation. -/
def budgetedEscapeValues
    {X Base Added Target Strategy : Type*}
    (base : Concept X Base) (supplement : Strategy -> Concept X Added)
    (target : Concept X Target) (cost : Strategy -> Real)
    (weight : EscapeWeight (X × X)) (budget : Real) : Set Real :=
  (fun strategy =>
      weight.mass
          (defectRelation (conceptJoin base (supplement strategy)) target) /
        weight.mass (defectRelation base target)) ''
    {strategy | cost strategy ≤ budget}

/-- The unavoidable escape rate at a budget is the infimum of the normalized
escape masses attainable by supplements feasible at that budget. -/
noncomputable def budgetedEscapeRate
    {X Base Added Target Strategy : Type*}
    (base : Concept X Base) (supplement : Strategy -> Concept X Added)
    (target : Concept X Target) (cost : Strategy -> Real)
    (weight : EscapeWeight (X × X)) (budget : Real) : Real :=
  sInf (budgetedEscapeValues
    base supplement target cost weight budget)

/-- When the base target-defect relation has positive mass and every
supplemented escape mass is bounded by that baseline, the budgeted escape rate
lies in the unit interval and is antitone as the feasible budget grows. -/
theorem budgeted_escape_rate_bounds_and_antitone
    {X Base Added Target Strategy : Type*}
    (base : Concept X Base) (supplement : Strategy -> Concept X Added)
    (target : Concept X Target) (cost : Strategy -> Real)
    (weight : EscapeWeight (X × X))
    {budget1 budget2 : Real}
    (baselineMassPositive : 0 < weight.mass (defectRelation base target))
    (escapeAtMostTotal : ∀ strategy,
      weight.mass
          (defectRelation (conceptJoin base (supplement strategy)) target) ≤
        weight.mass (defectRelation base target))
    (valuesNonempty1 : (budgetedEscapeValues
      base supplement target cost weight budget1).Nonempty) :
    (0 ≤ budgetedEscapeRate
        base supplement target cost weight budget1 ∧
      budgetedEscapeRate
          base supplement target cost weight budget1 ≤ 1) ∧
      (budget1 ≤ budget2 ->
        budgetedEscapeRate
            base supplement target cost weight budget2 ≤
          budgetedEscapeRate
            base supplement target cost weight budget1) := by
  have baselineMassNonnegative :
      0 ≤ weight.mass (defectRelation base target) :=
    weight.mass_nonnegative _
  have valuesBddBelow (budget : Real) : BddBelow (budgetedEscapeValues
      base supplement target cost weight budget) := by
    refine ⟨0, ?_⟩
    rintro value ⟨strategy, _, rfl⟩
    exact div_nonneg (weight.mass_nonnegative _) baselineMassNonnegative
  constructor
  · constructor
    · rw [budgetedEscapeRate]
      refine (le_csInf_iff (valuesBddBelow budget1) valuesNonempty1).2 ?_
      rintro value ⟨strategy, _, rfl⟩
      exact div_nonneg (weight.mass_nonnegative _) baselineMassNonnegative
    · rw [budgetedEscapeRate]
      rcases valuesNonempty1 with ⟨value, valueMem⟩
      refine (csInf_le (valuesBddBelow budget1) valueMem).trans ?_
      rcases valueMem with ⟨strategy, _, rfl⟩
      exact (div_le_iff₀ baselineMassPositive).2 (by
        simpa only [one_mul] using escapeAtMostTotal strategy)
  · intro budgetOrder
    rw [budgetedEscapeRate, budgetedEscapeRate]
    apply csInf_le_csInf (valuesBddBelow budget2) valuesNonempty1
    rintro value ⟨strategy, feasible, rfl⟩
    exact ⟨strategy, feasible.trans budgetOrder, rfl⟩

/-- On two states, a constant supplement leaves an actual target defect. A
two-atom counting weight gives that defect mass two and realizes escape rate
one with all infimum premises. -/
example :
    let base : Concept Bool Unit := fun _ => ()
    let supplement : Unit -> Concept Bool Unit := fun _ _ => ()
    let target : Concept Bool Bool := id
    let cost : Unit -> Real := fun _ => 0
    let weight : EscapeWeight (Bool × Bool) :=
      { mass := fun set => set.ncard
        empty_mass := by norm_num
        mass_nonnegative := by intro set; positivity }
    let values := budgetedEscapeValues
      base supplement target cost weight
    let rate := budgetedEscapeRate
      base supplement target cost weight
    (defectRelation (conceptJoin base (supplement ())) target).Nonempty ∧
      BddBelow (values 0) ∧ BddBelow (values 1) ∧
      (values 0).Nonempty ∧
      ((0 ≤ rate 0 ∧ rate 0 ≤ 1) ∧ (0 ≤ (1 : Real) -> rate 1 ≤ rate 0)) ∧
      rate 0 = 1 := by
  classical
  let base : Concept Bool Unit := fun _ => ()
  let supplement : Unit -> Concept Bool Unit := fun _ _ => ()
  let target : Concept Bool Bool := id
  let cost : Unit -> Real := fun _ => 0
  let weight : EscapeWeight (Bool × Bool) :=
    { mass := fun set => set.ncard
      empty_mass := by norm_num
      mass_nonnegative := by intro set; positivity }
  let values := budgetedEscapeValues
    base supplement target cost weight
  let rate := budgetedEscapeRate
    base supplement target cost weight
  change
    (defectRelation (conceptJoin base (supplement ())) target).Nonempty ∧
      BddBelow (values 0) ∧ BddBelow (values 1) ∧
      (values 0).Nonempty ∧
      ((0 ≤ rate 0 ∧ rate 0 ≤ 1) ∧ (0 ≤ (1 : Real) -> rate 1 ≤ rate 0)) ∧
      rate 0 = 1
  have residualEq (strategy : Unit) :
      defectRelation (conceptJoin base (supplement strategy)) target =
        {(false, true), (true, false)} := by
    ext pair
    rcases pair with ⟨first, second⟩
    cases first <;> cases second <;>
      simp [base, supplement, target, defectRelation, conceptJoin]
  have residualNonempty :
      (defectRelation (conceptJoin base (supplement ())) target).Nonempty := by
    rw [residualEq ()]
    simp
  have baselineEq : defectRelation base target =
      {(false, true), (true, false)} := by
    ext pair
    rcases pair with ⟨first, second⟩
    cases first <;> cases second <;>
      simp [base, target, defectRelation]
  have escapeAtMostTotal : ∀ strategy,
      weight.mass
          (defectRelation (conceptJoin base (supplement strategy)) target) ≤
        weight.mass (defectRelation base target) := by
    intro strategy
    rw [residualEq strategy, baselineEq]
  have valuesBddBelow : ∀ budget, BddBelow (values budget) := by
    intro budget
    refine ⟨0, ?_⟩
    rintro value ⟨strategy, _, rfl⟩
    exact div_nonneg (weight.mass_nonnegative _) (weight.mass_nonnegative _)
  have valuesNonempty : (values 0).Nonempty := by
    refine ⟨1, (), ?_, ?_⟩
    · norm_num [cost]
    · change weight.mass
          (defectRelation (conceptJoin base (supplement ())) target) /
            weight.mass (defectRelation base target) = 1
      rw [residualEq (), baselineEq]
      norm_num [weight]
  have package := budgeted_escape_rate_bounds_and_antitone
    base supplement target cost weight
    (budget1 := 0) (budget2 := 1) (by rw [baselineEq]; norm_num [weight])
    escapeAtMostTotal valuesNonempty
  refine ⟨residualNonempty, valuesBddBelow 0, valuesBddBelow 1,
    valuesNonempty, package, ?_⟩
  norm_num [rate, budgetedEscapeRate, values, budgetedEscapeValues, weight,
    residualEq, baselineEq, cost]

/-- Regression probe for baseline normalization: the public rate takes only a
budget after its weight, and its denominator is the zero baseline mass here. -/
example :
    let base : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    let weight : EscapeWeight (Bool × Bool) :=
      { mass := fun _ => 0
        empty_mass := rfl
        mass_nonnegative := by intro _; norm_num }
    let supplement : Unit -> Concept Bool Unit := fun _ _ => ()
    let cost : Unit -> Real := fun _ => 0
    (defectRelation base target).Nonempty ∧
      weight.mass (defectRelation base target) = 0 ∧
      budgetedEscapeRate base supplement target cost weight 0 = (0 : Real) := by
  classical
  let base : Concept Bool Unit := fun _ => ()
  let target : Concept Bool Bool := id
  let weight : EscapeWeight (Bool × Bool) :=
    { mass := fun _ => 0
      empty_mass := rfl
      mass_nonnegative := by intro _; norm_num }
  let supplement : Unit -> Concept Bool Unit := fun _ _ => ()
  let cost : Unit -> Real := fun _ => 0
  refine ⟨⟨(false, true), ?_⟩, by norm_num [weight], ?_⟩
  · simp [defectRelation]
  · simp [budgetedEscapeRate, budgetedEscapeValues]

/-- If the escape-mass upper bound is removed while every other displayed
premise holds, the unit upper bound can fail for a nonmonotone set weight. -/
example :
    let base : Concept (Bool × Bool) Unit := fun _ => ()
    let supplement : Unit -> Concept (Bool × Bool) Bool := fun _ state => state.1
    let target : Concept (Bool × Bool) (Bool × Bool) := id
    let cost : Unit -> Real := fun _ => 0
    let weight : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
      { mass := fun set =>
          if set = ∅ then 0 else if set = defectRelation base target then 1 else 2
        empty_mass := by simp
        mass_nonnegative := by
          intro set
          by_cases set = ∅ <;> by_cases set = defectRelation base target <;>
            simp_all }
    let values := budgetedEscapeValues
      base supplement target cost weight
    let rate := budgetedEscapeRate
      base supplement target cost weight
    (0 < weight.mass (defectRelation base target) ∧
      weight.mass ∅ = 0 ∧
      (∀ set, 0 ≤ weight.mass set) ∧
      BddBelow (values 0) ∧ (values 0).Nonempty) ∧
      ¬rate 0 ≤ 1 := by
  classical
  let base : Concept (Bool × Bool) Unit := fun _ => ()
  let supplement : Unit -> Concept (Bool × Bool) Bool := fun _ state => state.1
  let target : Concept (Bool × Bool) (Bool × Bool) := id
  let cost : Unit -> Real := fun _ => 0
  let weight : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
    { mass := fun set =>
        if set = ∅ then 0 else if set = defectRelation base target then 1 else 2
      empty_mass := by simp
      mass_nonnegative := by
        intro set
        by_cases set = ∅ <;> by_cases set = defectRelation base target <;>
          simp_all }
  let values := budgetedEscapeValues
    base supplement target cost weight
  let rate := budgetedEscapeRate
    base supplement target cost weight
  have baselineNonempty : (defectRelation base target).Nonempty := by
    refine ⟨((false, false), (true, false)), ?_⟩
    simp [base, target, defectRelation]
  have baselineMass : weight.mass (defectRelation base target) = 1 := by
    simp [weight, baselineNonempty.ne_empty]
  have residualNonempty (strategy : Unit) :
      (defectRelation (conceptJoin base (supplement strategy)) target).Nonempty := by
    refine ⟨((false, false), (false, true)), ?_⟩
    simp [base, supplement, target, defectRelation, conceptJoin]
  have residualNeBaseline (strategy : Unit) :
      defectRelation (conceptJoin base (supplement strategy)) target ≠
        defectRelation base target := by
    intro equality
    have pairInBaseline :
        ((false, false), (true, false)) ∈ defectRelation base target := by
      simp [base, target, defectRelation]
    have pairInResidual :
        ((false, false), (true, false)) ∈
          defectRelation (conceptJoin base (supplement strategy)) target := by
      rw [equality]
      exact pairInBaseline
    simp [base, supplement, target, defectRelation, conceptJoin] at pairInResidual
  have residualMass (strategy : Unit) :
      weight.mass
          (defectRelation (conceptJoin base (supplement strategy)) target) = 2 := by
    simp [weight, (residualNonempty strategy).ne_empty,
      residualNeBaseline strategy]
  have valuesBddBelow : BddBelow (values 0) := by
    refine ⟨0, ?_⟩
    rintro value ⟨strategy, _, rfl⟩
    exact div_nonneg (weight.mass_nonnegative _) (weight.mass_nonnegative _)
  have twoMem : (2 : Real) ∈ values 0 := by
    refine ⟨(), ?_, ?_⟩
    · norm_num [cost]
    · change weight.mass
          (defectRelation (conceptJoin base (supplement ())) target) /
            weight.mass (defectRelation base target) = 2
      rw [residualMass (), baselineMass]
      norm_num
  have valuesNonempty : (values 0).Nonempty := ⟨2, twoMem⟩
  have valuesEq : values 0 = {2} := by
    ext value
    constructor
    · rintro ⟨strategy, _, rfl⟩
      have strategyEq : strategy = () := Subsingleton.elim _ _
      subst strategy
      change weight.mass
          (defectRelation (conceptJoin base (supplement ())) target) /
            weight.mass (defectRelation base target) ∈ ({2} : Set Real)
      rw [residualMass (), baselineMass]
      norm_num
    · intro member
      have valueEq : value = 2 := Set.mem_singleton_iff.mp member
      subst value
      exact twoMem
  refine ⟨⟨by rw [baselineMass]; norm_num, weight.empty_mass, weight.mass_nonnegative,
    valuesBddBelow, valuesNonempty⟩, ?_⟩
  change ¬sInf (values 0) ≤ 1
  rw [valuesEq]
  norm_num

/-- For an empty state space every canonical defect is empty, so every
admissible weight forces the canonically normalized escape rate to zero. -/
example (weight : EscapeWeight (Empty × Empty)) :
    let base : Concept Empty Unit := fun state => state.elim
    let supplement : Unit -> Concept Empty Unit := fun _ state => state.elim
    let target : Concept Empty Empty := id
    let cost : Unit -> Real := fun _ => 0
    budgetedEscapeRate base supplement target cost weight 0 = 0 := by
  classical
  let base : Concept Empty Unit := fun state => state.elim
  let supplement : Unit -> Concept Empty Unit := fun _ state => state.elim
  let target : Concept Empty Empty := id
  let cost : Unit -> Real := fun _ => 0
  change budgetedEscapeRate base supplement target cost weight 0 = 0
  have defectEmpty (strategy : Unit) :
      defectRelation (conceptJoin base (supplement strategy)) target = ∅ := by
    ext pair
    exact pair.1.elim
  simp [budgetedEscapeRate, budgetedEscapeValues, defectEmpty, cost,
    weight.empty_mass]

#print axioms budgeted_escape_rate_bounds_and_antitone

end D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
