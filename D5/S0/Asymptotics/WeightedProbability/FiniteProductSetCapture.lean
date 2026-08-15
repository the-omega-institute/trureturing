/- GID: D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every prescribed finite set of captured addresses has an exact product mass. -/

/- Library-search audit trail (2026-08-15):
   * Repository searches found exact one-row and distinct two-row weighted capture laws, but
     no formula for an arbitrary prescribed finite set of captured addresses.
   * Pinned Mathlib supplies `Fintype.prod_sum` and dependent finite-product reindexing, but
     no theorem for the repository's model-specific twisted-diagonal intersection masses.
   * The proof applies the frozen `constrainedRows_weight_sum`; singleton and pair bridges
     then apply both this all-orders law and the corresponding frozen exact law.
-/

import D5.S0.Asymptotics.WeightedProbability.FiniteProductPairCapture

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.FiniteProductSetCapture

open FiniteProductCapture
open FiniteProductPairCapture

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- Fixed-point mass with the power contributed by a prescribed captured set. -/
noncomputable def fixedPowerMass [Fintype Y]
    (q : A -> Y -> Real) (f : Y -> Y) (a : A) (e : Nat) : Real := by
  classical exact ∑ y, if f y = y then q a y ^ e else 0

/-- Collision mass with the power contributed by a prescribed captured set. -/
def collisionPowerMass [Fintype Y]
    (q : A -> Y -> Real) (f : Y -> Y) (a : A) (e : Nat) : Real :=
  ∑ y, q a y * q a (f y) ^ e

/-- Weighted probability that every address in `T` captures the twisted diagonal. -/
noncomputable def setCaptureProbability [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) (T : Finset A) : Real := by
  classical exact eventProbability q (fun s => forall a, a ∈ T -> Captured f s a)

/-- Selected target-row weights regroup by output column. -/
theorem selected_target_row_product [Fintype A] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) (X : A -> Y) (T : Finset A) :
    (∏ a ∈ T, rowWeight q a (targetRows f X a)) =
      ∏ b, q b (f (X b)) ^ (T.filter fun a => b ≠ a).card := by
  classical
  simp only [rowWeight, targetRows]
  rw [show (∏ a ∈ T, ∏ b : {b : A // b ≠ a}, q b.1 (f (X b.1))) =
      ∏ a ∈ T, ∏ b ∈ (Finset.univ : Finset A) with b ≠ a, q b (f (X b)) by
    apply Finset.prod_congr rfl
    intro a _
    symm
    exact Finset.prod_subtype ((Finset.univ : Finset A).filter fun b => b ≠ a)
      (by simp) (fun b => q b (f (X b)))]
  rw [Finset.prod_comm'
    (s := T)
    (t := fun a => (Finset.univ : Finset A).filter fun b => b ≠ a)
    (t' := Finset.univ)
    (s' := fun b => T.filter fun a => b ≠ a)
    (fun a b => by simp)]
  apply Finset.prod_congr rfl
  intro b _
  rw [Finset.prod_const]

/-- A selected address contributes one fewer off-diagonal row factor at its own column. -/
theorem selected_row_count (T : Finset A) (b : A) [DecidableEq A] :
    (T.filter fun a => b ≠ a).card = if b ∈ T then T.card - 1 else T.card := by
  classical
  by_cases hb : b ∈ T
  · rw [if_pos hb]
    have hfilter : T.filter (fun a => b ≠ a) = T.erase b := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨ha, hne⟩
        exact ⟨fun hab => hne hab.symm, ha⟩
      · rintro ⟨hne, ha⟩
        exact ⟨ha, fun hba => hne hba.symm⟩
    rw [hfilter, Finset.card_erase_of_mem hb]
  · rw [if_neg hb]
    apply congrArg Finset.card
    ext a
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro ha
      exact ⟨ha, fun hba => hb (hba ▸ ha)⟩

/-- Under selected-column fixedness, the diagonal and selected rows factor by column. -/
theorem diagonal_times_selected_rows [Fintype A] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) (X : A -> Y) (T : Finset A)
    (hfixed : forall b, b ∈ T -> f (X b) = X b) :
    (∏ b, q b (X b)) * ∏ a ∈ T, rowWeight q a (targetRows f X a) =
      ∏ b, if b ∈ T then q b (X b) ^ T.card
        else q b (X b) * q b (f (X b)) ^ T.card := by
  classical
  rw [selected_target_row_product q f X T, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro b _
  rw [selected_row_count T b]
  by_cases hb : b ∈ T
  · simp only [hb, if_true]
    rw [hfixed b hb]
    have hcard : 1 ≤ T.card := Finset.one_le_card.mpr ⟨b, hb⟩
    rw [← pow_succ']
    congr 1
    omega
  · simp [hb]

/-- Exact all-orders intersection mass for an arbitrary prescribed captured set. -/
theorem set_capture_probability_exact [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) (T : Finset A) :
    setCaptureProbability q f T =
      ∏ b, if b ∈ T then fixedPowerMass q f b T.card
        else collisionPowerMass q f b T.card := by
  classical
  rw [setCaptureProbability, eventProbability, Fintype.sum_prod_type]
  have hinner : forall X : A -> Y,
      (∑ R : (a : A) -> OffRow A Y a,
        if (forall a, a ∈ T -> Captured f (X, R) a) then sampleWeight q (X, R) else 0) =
      if (forall a, a ∈ T -> f (X a) = X a) then
        (∏ b, q b (X b)) * ∏ a ∈ T, rowWeight q a (targetRows f X a)
      else 0 := by
    intro X
    by_cases hfixed : forall a, a ∈ T -> f (X a) = X a
    · rw [if_pos hfixed]
      have hevent : forall R : (a : A) -> OffRow A Y a,
          (forall a, a ∈ T -> Captured f (X, R) a) <->
            (forall a, a ∈ T -> R a = targetRows f X a) := by
        intro R
        simp only [captured_iff_twisted_diagonal]
        constructor
        · intro h a ha
          exact (h a ha).2
        · intro h a ha
          exact ⟨hfixed a ha, h a ha⟩
      simp_rw [hevent, sampleWeight]
      calc
        (∑ R : (a : A) -> OffRow A Y a,
            if (forall a, a ∈ T -> R a = targetRows f X a) then
              (∏ b, q b (X b)) * ∏ i, rowWeight q i (R i) else 0) =
            (∏ b, q b (X b)) *
              ∑ R : (a : A) -> OffRow A Y a,
                if (forall a, a ∈ T -> R a = targetRows f X a) then
                  ∏ i, rowWeight q i (R i) else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro R _
            split <;> simp_all
        _ = _ := by rw [constrainedRows_weight_sum q hq T (targetRows f X)]
    · rw [if_neg hfixed]
      push Not at hfixed
      obtain ⟨a, ha, hnotfixed⟩ := hfixed
      apply Finset.sum_eq_zero
      intro R _
      rw [if_neg]
      intro hcaptured
      exact hnotfixed ((captured_iff_twisted_diagonal f (X, R) a).mp
        (hcaptured a ha)).1
  simp_rw [hinner]
  have hsummand : forall X : A -> Y,
      (if (forall a, a ∈ T -> f (X a) = X a) then
          (∏ b, q b (X b)) * ∏ a ∈ T, rowWeight q a (targetRows f X a)
        else 0) =
      ∏ b, if b ∈ T then
          (if f (X b) = X b then q b (X b) ^ T.card else 0)
        else q b (X b) * q b (f (X b)) ^ T.card := by
    intro X
    by_cases hfixed : forall a, a ∈ T -> f (X a) = X a
    · rw [if_pos hfixed, diagonal_times_selected_rows q f X T hfixed]
      apply Finset.prod_congr rfl
      intro b _
      by_cases hb : b ∈ T <;> simp [hb, hfixed b]
    · rw [if_neg hfixed]
      push Not at hfixed
      obtain ⟨b, hb, hnotfixed⟩ := hfixed
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      simp [hb, hnotfixed]
  simp_rw [hsummand]
  calc
    (∑ X : A -> Y, ∏ b, if b ∈ T then
          (if f (X b) = X b then q b (X b) ^ T.card else 0)
        else q b (X b) * q b (f (X b)) ^ T.card) =
        ∏ b, ∑ y, if b ∈ T then
          (if f y = y then q b y ^ T.card else 0)
        else q b y * q b (f y) ^ T.card := by
      symm
      exact Fintype.prod_sum fun b y => if b ∈ T then
        (if f y = y then q b y ^ T.card else 0)
        else q b y * q b (f y) ^ T.card
    _ = _ := by
      apply Finset.prod_congr rfl
      intro b _
      by_cases hb : b ∈ T <;>
        simp [hb, fixedPowerMass, collisionPowerMass]

/-- The degree-one instance is exactly the frozen one-address product expression. -/
theorem singleton_set_formula_eq_capture_probability_exact
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) (a : A) :
    (∏ b, if b ∈ ({a} : Finset A) then fixedPowerMass q f b ({a} : Finset A).card
      else collisionPowerMass q f b ({a} : Finset A).card) =
      fixedMass q f a * ∏ b : {b : A // b ≠ a}, collisionMass q f b.1 := by
  calc
    _ = setCaptureProbability q f {a} := (set_capture_probability_exact q hq f {a}).symm
    _ = captureProbability q f a := by
      simp [setCaptureProbability, captureProbability]
    _ = _ := capture_probability_exact q hq f a

/-- The degree-two instance is exactly the frozen distinct-pair product expression. -/
theorem pair_set_formula_eq_pair_capture_probability_exact
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) (a a' : A) (haa' : a ≠ a') :
    (∏ b, if b ∈ ({a, a'} : Finset A) then
        fixedPowerMass q f b ({a, a'} : Finset A).card
      else collisionPowerMass q f b ({a, a'} : Finset A).card) =
      fixedSquareMass q f a * fixedSquareMass q f a' *
        ∏ b : {b : A // b ≠ a ∧ b ≠ a'}, collisionSquareMass q f b.1 := by
  calc
    _ = setCaptureProbability q f {a, a'} :=
      (set_capture_probability_exact q hq f {a, a'}).symm
    _ = pairCaptureProbability q f a a' := by
      simp [setCaptureProbability, pairCaptureProbability]
    _ = _ := pair_capture_probability_exact q hq f a a' haa'

#print axioms fixedPowerMass
#print axioms collisionPowerMass
#print axioms setCaptureProbability
#print axioms selected_target_row_product
#print axioms selected_row_count
#print axioms diagonal_times_selected_rows
#print axioms set_capture_probability_exact
#print axioms singleton_set_formula_eq_capture_probability_exact
#print axioms pair_set_formula_eq_pair_capture_probability_exact

end

end D5.S0.Asymptotics.WeightedProbability.FiniteProductSetCapture
