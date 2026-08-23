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
most the supplied budget. -/
def budgetedEscapeValues
    {X Base Added Target Strategy : Type*}
    (base : Concept X Base) (supplement : Strategy -> Concept X Added)
    (target : Concept X Target) (cost : Strategy -> Real)
    (weight : EscapeWeight (X × X)) (totalMass budget : Real) : Set Real :=
  (fun strategy =>
      weight.mass
          (defectRelation (conceptJoin base (supplement strategy)) target) /
        totalMass) ''
    {strategy | cost strategy ≤ budget}

/-- The unavoidable escape rate at a budget is the infimum of the normalized
escape masses attainable by supplements feasible at that budget. -/
noncomputable def budgetedEscapeRate
    {X Base Added Target Strategy : Type*}
    (base : Concept X Base) (supplement : Strategy -> Concept X Added)
    (target : Concept X Target) (cost : Strategy -> Real)
    (weight : EscapeWeight (X × X)) (totalMass budget : Real) : Real :=
  sInf (budgetedEscapeValues
    base supplement target cost weight totalMass budget)

/-- With a nonnegative zero-empty weight, positive total mass, escape mass
bounded by that total, and the real-infimum side conditions stated explicitly,
the budgeted escape rate lies in the unit interval and is antitone as the
feasible budget grows. -/
theorem budgeted_escape_rate_bounds_and_antitone
    {X Base Added Target Strategy : Type*}
    (base : Concept X Base) (supplement : Strategy -> Concept X Added)
    (target : Concept X Target) (cost : Strategy -> Real)
    (weight : EscapeWeight (X × X)) (totalMass : Real)
    {budget1 budget2 : Real} (totalMassPositive : 0 < totalMass)
    (escapeAtMostTotal : ∀ strategy,
      weight.mass
          (defectRelation (conceptJoin base (supplement strategy)) target) ≤
        totalMass)
    (valuesBddBelow1 : BddBelow (budgetedEscapeValues
      base supplement target cost weight totalMass budget1))
    (valuesBddBelow2 : BddBelow (budgetedEscapeValues
      base supplement target cost weight totalMass budget2))
    (valuesNonempty1 : (budgetedEscapeValues
      base supplement target cost weight totalMass budget1).Nonempty) :
    (0 ≤ budgetedEscapeRate
        base supplement target cost weight totalMass budget1 ∧
      budgetedEscapeRate
          base supplement target cost weight totalMass budget1 ≤ 1) ∧
      (budget1 ≤ budget2 ->
        budgetedEscapeRate
            base supplement target cost weight totalMass budget2 ≤
          budgetedEscapeRate
            base supplement target cost weight totalMass budget1) := by
  constructor
  · constructor
    · rw [budgetedEscapeRate]
      refine (le_csInf_iff valuesBddBelow1 valuesNonempty1).2 ?_
      rintro value ⟨strategy, _, rfl⟩
      exact div_nonneg (weight.mass_nonnegative _) totalMassPositive.le
    · rw [budgetedEscapeRate]
      rcases valuesNonempty1 with ⟨value, valueMem⟩
      refine (csInf_le valuesBddBelow1 valueMem).trans ?_
      rcases valueMem with ⟨strategy, _, rfl⟩
      exact (div_le_iff₀ totalMassPositive).2 (by
        simpa only [one_mul] using escapeAtMostTotal strategy)
  · intro budgetOrder
    rw [budgetedEscapeRate, budgetedEscapeRate]
    apply csInf_le_csInf valuesBddBelow2 valuesNonempty1
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
      base supplement target cost weight 2
    let rate := budgetedEscapeRate
      base supplement target cost weight 2
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
    base supplement target cost weight 2
  let rate := budgetedEscapeRate
    base supplement target cost weight 2
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
  have escapeAtMostTotal : ∀ strategy,
      weight.mass
          (defectRelation (conceptJoin base (supplement strategy)) target) ≤
        (2 : Real) := by
    intro strategy
    rw [residualEq strategy]
    norm_num [weight]
  have valuesBddBelow : ∀ budget, BddBelow (values budget) := by
    intro budget
    refine ⟨0, ?_⟩
    rintro value ⟨strategy, _, rfl⟩
    exact div_nonneg (weight.mass_nonnegative _) (by norm_num)
  have valuesNonempty : (values 0).Nonempty := by
    refine ⟨1, (), ?_, ?_⟩
    · norm_num [cost]
    · change weight.mass
          (defectRelation (conceptJoin base (supplement ())) target) / 2 = 1
      rw [residualEq ()]
      norm_num [weight]
  have package := budgeted_escape_rate_bounds_and_antitone
    base supplement target cost weight 2
    (budget1 := 0) (budget2 := 1) (by norm_num)
    escapeAtMostTotal
    (valuesBddBelow 0) (valuesBddBelow 1) valuesNonempty
  refine ⟨residualNonempty, valuesBddBelow 0, valuesBddBelow 1,
    valuesNonempty, package, ?_⟩
  norm_num [rate, budgetedEscapeRate, values, budgetedEscapeValues, weight,
    residualEq, cost]

/-- If the escape-mass upper bound is removed while every other displayed
premise holds, the unit upper bound can fail even for a finite counting
weight. -/
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
      base supplement target cost weight 1
    let rate := budgetedEscapeRate
      base supplement target cost weight 1
    (0 < (1 : Real) ∧
      weight.mass ∅ = 0 ∧
      (∀ set, 0 ≤ weight.mass set) ∧
      BddBelow (values 0) ∧ (values 0).Nonempty) ∧
      ¬rate 0 ≤ 1 := by
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
    base supplement target cost weight 1
  let rate := budgetedEscapeRate
    base supplement target cost weight 1
  change
    (0 < (1 : Real) ∧
      weight.mass ∅ = 0 ∧
      (∀ set, 0 ≤ weight.mass set) ∧
      BddBelow (values 0) ∧ (values 0).Nonempty) ∧
      ¬rate 0 ≤ 1
  have residualEq (strategy : Unit) :
      defectRelation (conceptJoin base (supplement strategy)) target =
        {(false, true), (true, false)} := by
    ext pair
    rcases pair with ⟨first, second⟩
    cases first <;> cases second <;>
      simp [base, supplement, target, defectRelation, conceptJoin]
  have valuesBddBelow : BddBelow (values 0) := by
    refine ⟨0, ?_⟩
    rintro value ⟨strategy, _, rfl⟩
    exact div_nonneg (weight.mass_nonnegative _) (by norm_num)
  have valuesNonempty : (values 0).Nonempty := by
    refine ⟨2, (), ?_, ?_⟩
    · norm_num [cost]
    · change weight.mass
          (defectRelation (conceptJoin base (supplement ())) target) / 1 = 2
      rw [residualEq ()]
      norm_num [weight]
  refine ⟨⟨by norm_num, weight.empty_mass, weight.mass_nonnegative,
    valuesBddBelow, valuesNonempty⟩, ?_⟩
  norm_num [rate, budgetedEscapeRate, values, budgetedEscapeValues, weight,
    residualEq, cost]

/-- Counterexample probe: for an empty state space every canonical defect is
empty, so every admissible weight forces the budgeted escape rate to zero. -/
example (weight : EscapeWeight (Empty × Empty)) :
    let base : Concept Empty Unit := fun state => state.elim
    let supplement : Unit -> Concept Empty Unit := fun _ state => state.elim
    let target : Concept Empty Empty := id
    let cost : Unit -> Real := fun _ => 0
    budgetedEscapeRate base supplement target cost weight 1 0 = 0 := by
  classical
  let base : Concept Empty Unit := fun state => state.elim
  let supplement : Unit -> Concept Empty Unit := fun _ state => state.elim
  let target : Concept Empty Empty := id
  let cost : Unit -> Real := fun _ => 0
  change budgetedEscapeRate base supplement target cost weight 1 0 = 0
  have defectEmpty (strategy : Unit) :
      defectRelation (conceptJoin base (supplement strategy)) target = ∅ := by
    ext pair
    exact pair.1.elim
  simp [budgetedEscapeRate, budgetedEscapeValues, defectEmpty, cost,
    weight.empty_mass]

#print axioms budgeted_escape_rate_bounds_and_antitone

end D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
