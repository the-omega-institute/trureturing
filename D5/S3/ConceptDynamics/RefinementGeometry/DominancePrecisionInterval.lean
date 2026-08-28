/- GID: D5/S3/ConceptDynamics/RefinementGeometry/DominancePrecisionInterval
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementGeometry/DominancePrecisionInterval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete dominance occupies the half-open interval between two reveal thresholds. -/

import D5.S3.ConceptDynamics.RefinementGeometry.PrecisionSeparationPersistence
import Mathlib.Data.ENat.Basic
import Mathlib.Order.Interval.Set.Nat

/- Library-search audit trail (2026-08-26):
   * Searches by theorem name, dominance terminology, threshold terminology,
     and the body shape `if h : exists k, q k x != q k y then Nat.find h
     else top` found no D5 owner for the extended-natural reveal threshold or
     its dominance interval.
   * `FiniteFutureCongruence.separationTime` returns zero when a pair never
     separates and concerns temporal iterates of one readout, so it is not the
     source's precision threshold with infinity.
   * The frozen `precision_separation_persists` supplies the exact upward
     closure of the separation test and is applied below.
   * Pinned Mathlib exact hits `Nat.find_spec`, `Nat.find_min'`,
     `ENat.ne_top_iff_exists`, `Set.nonempty_Ico`, and `Set.ncard_Ico_nat`
     supply the least-witness and interval arithmetic. No theorem packages the
     source's four dominance clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementGeometry.DominancePrecisionInterval

open D5.S3.ConceptDynamics.RefinementGeometry.PrecisionSeparationPersistence

universe u v

/-- The first precision layer separating a pair, or infinity when no layer
separates it. This is the source's pairwise reveal-threshold construction. -/
noncomputable def revealThreshold
    {X : Type u} (O : Nat -> Type v)
    (q : (level : Nat) -> X -> O level) (left right : X) : ℕ∞ := by
  classical
  exact if separates : exists level, q level left ≠ q level right then
    (Nat.find separates : ℕ∞)
  else
    ⊤

/-- For three genotype states in a compatible precision tower, complete
dominance at a layer means that `AA` and `AB` agree while `AB` and `BB` differ.
Those layers form exactly the half-open interval from the second reveal
threshold to the first. The interval is inhabited exactly when its endpoints
are strictly ordered, and finite endpoints give the stated dominance width. -/
theorem dominance_precision_interval
    {X : Type u}
    (O : Nat -> Type v)
    (q : (level : Nat) -> X -> O level)
    (lower : (level : Nat) -> O (level + 1) -> O level)
    (compatible : forall level, q level = lower level ∘ q (level + 1))
    (stateAA stateAB stateBB : X) :
    let r1 := revealThreshold O q stateAA stateAB
    let r2 := revealThreshold O q stateAB stateBB
    let dominantAt := fun level : Nat =>
      q level stateAA = q level stateAB ∧
        q level stateAB ≠ q level stateBB
    let dominanceBand : Set ℕ∞ :=
      {value | exists level : Nat, value = (level : ℕ∞) ∧ dominantAt level}
    let finiteDominanceBand : Set Nat := {level | dominantAt level}
    let dominanceWidth := finiteDominanceBand.ncard
    (forall level, dominantAt level ↔
      r2 ≤ (level : ℕ∞) ∧ (level : ℕ∞) < r1) ∧
    dominanceBand = Set.Ico r2 r1 ∧
    ((exists level, dominantAt level) ↔ r2 < r1) ∧
    (forall n1 n2 : Nat,
      r1 = (n1 : ℕ∞) -> r2 = (n2 : ℕ∞) ->
        dominanceWidth = n1 - n2) := by
  classical
  let r1 := revealThreshold O q stateAA stateAB
  let r2 := revealThreshold O q stateAB stateBB
  let dominantAt := fun level : Nat =>
    q level stateAA = q level stateAB ∧
      q level stateAB ≠ q level stateBB
  let dominanceBand : Set ℕ∞ :=
    {value | exists level : Nat, value = (level : ℕ∞) ∧ dominantAt level}
  let finiteDominanceBand : Set Nat := {level | dominantAt level}
  let dominanceWidth := finiteDominanceBand.ncard
  change
    (forall level, dominantAt level ↔
      r2 ≤ (level : ℕ∞) ∧ (level : ℕ∞) < r1) ∧
    dominanceBand = Set.Ico r2 r1 ∧
    ((exists level, dominantAt level) ↔ r2 < r1) ∧
    (forall n1 n2 : Nat,
      r1 = (n1 : ℕ∞) -> r2 = (n2 : ℕ∞) ->
        dominanceWidth = n1 - n2)
  have threshold_le_iff (left right : X) (level : Nat) :
      revealThreshold O q left right ≤ (level : ℕ∞) ↔
        q level left ≠ q level right := by
    rw [revealThreshold]
    split_ifs with separates
    · constructor
      · intro thresholdLe
        have firstLe : Nat.find separates ≤ level := by
          exact_mod_cast thresholdLe
        exact precision_separation_persists O q lower compatible
          left right firstLe (Nat.find_spec separates)
      · intro differs
        exact_mod_cast Nat.find_min' separates differs
    · have doesNotDiffer : ¬q level left ≠ q level right := by
        intro differs
        exact separates ⟨level, differs⟩
      simp [doesNotDiffer]
  have below_threshold_iff (left right : X) (level : Nat) :
      (level : ℕ∞) < revealThreshold O q left right ↔
        q level left = q level right := by
    rw [lt_iff_not_ge, threshold_le_iff]
    exact not_ne_iff
  have dominantAt_iff (level : Nat) :
      dominantAt level ↔
        r2 ≤ (level : ℕ∞) ∧ (level : ℕ∞) < r1 := by
    change
      (q level stateAA = q level stateAB ∧
        q level stateAB ≠ q level stateBB) ↔ _
    constructor
    · rintro ⟨sameFirstPair, differentSecondPair⟩
      constructor
      · simpa [r2] using
          (threshold_le_iff stateAB stateBB level).2 differentSecondPair
      · simpa [r1] using
          (below_threshold_iff stateAA stateAB level).2 sameFirstPair
    · rintro ⟨secondRevealed, firstNotRevealed⟩
      constructor
      · exact (below_threshold_iff stateAA stateAB level).1 (by
          simpa [r1] using firstNotRevealed)
      · exact (threshold_le_iff stateAB stateBB level).1 (by
          simpa [r2] using secondRevealed)
  have dominanceBand_eq : dominanceBand = Set.Ico r2 r1 := by
    ext value
    constructor
    · rintro ⟨level, rfl, dominates⟩
      exact (dominantAt_iff level).1 dominates
    · intro inInterval
      have finiteValue : value ≠ ⊤ :=
        ne_top_of_lt (inInterval.2.trans_le le_top)
      obtain ⟨level, levelEq⟩ := ENat.ne_top_iff_exists.mp finiteValue
      refine ⟨level, levelEq.symm, ?_⟩
      rw [← levelEq] at inInterval
      exact (dominantAt_iff level).2 inInterval
  have dominance_exists_iff :
      (exists level, dominantAt level) ↔ r2 < r1 := by
    constructor
    · rintro ⟨level, dominates⟩
      exact ((dominantAt_iff level).1 dominates).1.trans_lt
        ((dominantAt_iff level).1 dominates).2
    · intro ordered
      have finiteLower : r2 ≠ ⊤ := ne_top_of_lt (ordered.trans_le le_top)
      obtain ⟨level, levelEq⟩ := ENat.ne_top_iff_exists.mp finiteLower
      refine ⟨level, (dominantAt_iff level).2 ?_⟩
      constructor
      · rw [← levelEq]
      · simpa only [levelEq] using ordered
  have finite_width :
      forall n1 n2 : Nat,
        r1 = (n1 : ℕ∞) -> r2 = (n2 : ℕ∞) ->
          dominanceWidth = n1 - n2 := by
    intro n1 n2 r1Finite r2Finite
    have finiteBandEq : finiteDominanceBand = Set.Ico n2 n1 := by
      ext level
      simpa [finiteDominanceBand, r1Finite, r2Finite] using
        dominantAt_iff level
    change finiteDominanceBand.ncard = n1 - n2
    rw [finiteBandEq, Set.ncard_Ico_nat]
  exact ⟨dominantAt_iff, dominanceBand_eq,
    dominance_exists_iff, finite_width⟩

#print axioms revealThreshold
#print axioms dominance_precision_interval

end D5.S3.ConceptDynamics.RefinementGeometry.DominancePrecisionInterval
