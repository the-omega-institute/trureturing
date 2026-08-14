/- GID: D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/FiniteBonferroni
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite weighted capture events satisfy two-sided Bonferroni escape bounds. -/

/- Library-search audit trail (2026-08-15):
   * Repository searches found no pre-existing two-sided weighted escape bound.
   * Pinned Mathlib's `Combinatorics/Enumerative/InclusionExclusion.lean` provides exact
     inclusion-exclusion identities, but not the first- and second-order truncated
     inequalities needed here, so the finite indicator inequalities are proved locally.
   * Crossref resolved Janos Galambos, "Bonferroni Inequalities" (1977), DOI
     `10.1214/aop/1176995765`; the Scribe source carries that literature provenance.
-/

import D5.S0.Asymptotics.WeightedProbability.FiniteProductPairCapture
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.FiniteBonferroni

open FiniteProductCapture
open D5.S0.Diagonal.EscapeCount

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

private noncomputable def noneIndicator (P : A -> Prop) (S : Finset A) : Real :=
  if (forall a, a ∈ S -> ¬ P a) then 1 else 0

private noncomputable def singleIndicator (P : A -> Prop) (S : Finset A) : Real :=
  ∑ a ∈ S, if P a then 1 else 0

private noncomputable def pairIndicator [LinearOrder A]
    (P : A -> Prop) (S : Finset A) : Real :=
  ∑ a ∈ S, ∑ b ∈ S, if a < b ∧ P a ∧ P b then 1 else 0

private theorem noneIndicator_insert [DecidableEq A]
    (P : A -> Prop) (S : Finset A) (a : A) (_ha : a ∉ S) :
    noneIndicator P (insert a S) = if P a then 0 else noneIndicator P S := by
  classical
  by_cases hPa : P a
  · simp [noneIndicator, hPa]
  · simp only [noneIndicator, hPa, if_false]
    congr 1
    simp [hPa]

private theorem singleIndicator_insert [DecidableEq A]
    (P : A -> Prop) (S : Finset A) (a : A) (ha : a ∉ S) :
    singleIndicator P (insert a S) =
      (if P a then 1 else 0) + singleIndicator P S := by
  classical
  simp only [singleIndicator, Finset.sum_insert ha]

private theorem pairIndicator_insert [LinearOrder A]
    (P : A -> Prop) (S : Finset A) (a : A) (ha : a ∉ S) :
    pairIndicator P (insert a S) =
      pairIndicator P S + (if P a then 1 else 0) * singleIndicator P S := by
  classical
  simp only [pairIndicator, singleIndicator]
  simp_rw [Finset.sum_insert ha]
  have hcross :
      (∑ b ∈ S, if a < b ∧ P a ∧ P b then (1 : Real) else 0) +
        (∑ b ∈ S, if b < a ∧ P b ∧ P a then (1 : Real) else 0) =
      (if P a then 1 else 0) * ∑ b ∈ S, if P b then (1 : Real) else 0 := by
    by_cases hPa : P a
    · simp only [hPa, and_true, true_and, if_true, one_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      have hba : b ≠ a := by
        intro h
        subst b
        exact ha hb
      rcases lt_or_gt_of_ne hba with hlt | hgt
      · simp [hlt, not_lt_of_ge hlt.le]
      · simp [hgt, not_lt_of_ge hgt.le]
    · simp [hPa]
  simp only [lt_irrefl, false_and, if_false, zero_add]
  rw [Finset.sum_add_distrib, ← add_assoc, hcross]
  ring

private theorem bonferroni_indicators [LinearOrder A] (P : A -> Prop) (S : Finset A) :
    1 - singleIndicator P S ≤ noneIndicator P S ∧
      noneIndicator P S ≤ 1 - singleIndicator P S + pairIndicator P S := by
  classical
  induction S using Finset.induction with
  | empty => simp [noneIndicator, singleIndicator, pairIndicator]
  | @insert a S ha ih =>
      rw [noneIndicator_insert P S a ha, singleIndicator_insert P S a ha,
        pairIndicator_insert P S a ha]
      by_cases hPa : P a
      · simp only [hPa, if_true]
        constructor
        · have hnonneg : 0 ≤ singleIndicator P S := by
            rw [singleIndicator]
            positivity
          linarith
        · have hpnonneg : 0 ≤ pairIndicator P S := by
            rw [pairIndicator]
            positivity
          linarith
      · simp only [hPa, if_false, zero_add, zero_mul, add_zero]
        exact ih

/-- No captured row is exactly the frozen `EscapeCount.IsEscaped` event for the listing. -/
theorem no_capture_iff_isEscaped [DecidableEq A]
    (f : Y -> Y) (s : Sample A Y) :
    (forall a, ¬ Captured f s a) <-> IsEscaped f (listing s) := by
  change (forall a, ¬ listing s a = diagonal f (listing s)) <->
    ¬(Exists fun a => listing s a = diagonal f (listing s))
  constructor
  · intro hNoCapture hRange
    obtain ⟨a, ha⟩ := hRange
    exact hNoCapture a ha
  · intro hEscaped a ha
    exact hEscaped ⟨a, ha⟩

/-- Probability that no row captures the twisted diagonal. -/
def escapeProbability [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) : Real :=
  eventProbability q (fun s => forall a, ¬ Captured f s a)

/-- Sum over unordered address pairs, represented canonically by `a < a'`. -/
def pairProbabilitySum [Fintype A] [Fintype Y] [LinearOrder A]
    (q : A -> Y -> Real) (f : Y -> Y) : Real :=
  ∑ a, ∑ a', if a < a' then pairCaptureProbability q f a a' else 0

private theorem sampleWeight_nonneg [Fintype A] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b y, 0 ≤ q b y) (s : Sample A Y) :
    0 ≤ sampleWeight q s := by
  rw [sampleWeight]
  apply mul_nonneg
  · exact Finset.prod_nonneg fun b _ => hq b (s.1 b)
  · exact Finset.prod_nonneg fun a _ =>
      Finset.prod_nonneg fun b _ => hq b.1 (s.2 a b)

private theorem escapeProbability_eq_indicator_sum
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) :
    escapeProbability q f =
      ∑ s : Sample A Y,
        sampleWeight q s * noneIndicator (fun a => Captured f s a) Finset.univ := by
  classical
  simp only [escapeProbability, eventProbability]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : forall a, ¬ Captured f s a <;> simp [h, noneIndicator]

private theorem captureProbability_sum_eq_indicator_sum
    [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) :
    (∑ a, captureProbability q f a) =
      ∑ s : Sample A Y,
        sampleWeight q s * singleIndicator (fun a => Captured f s a) Finset.univ := by
  classical
  simp only [singleIndicator]
  calc
    (∑ a, captureProbability q f a) =
        ∑ a, ∑ s : Sample A Y,
          if Captured f s a then sampleWeight q s else 0 := by
      simp [captureProbability, eventProbability]
    _ = ∑ s : Sample A Y, ∑ a,
          if Captured f s a then sampleWeight q s else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : Captured f s a <;> simp [h]

private theorem pairProbabilitySum_eq_indicator_sum
    [Fintype A] [Fintype Y] [LinearOrder A]
    (q : A -> Y -> Real) (f : Y -> Y) :
    pairProbabilitySum q f =
      ∑ s : Sample A Y,
        sampleWeight q s * pairIndicator (fun a => Captured f s a) Finset.univ := by
  classical
  simp only [pairIndicator]
  calc
    pairProbabilitySum q f =
        ∑ a, ∑ a', ∑ s : Sample A Y,
          if a < a' ∧ Captured f s a ∧ Captured f s a' then
            sampleWeight q s else 0 := by
      simp only [pairProbabilitySum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro a' _
      by_cases haa' : a < a' <;>
        simp [haa', pairCaptureProbability, eventProbability]
    _ = ∑ a, ∑ s : Sample A Y, ∑ a',
          if a < a' ∧ Captured f s a ∧ Captured f s a' then
            sampleWeight q s else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ s : Sample A Y, ∑ a, ∑ a',
          if a < a' ∧ Captured f s a ∧ Captured f s a' then
            sampleWeight q s else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a' _
      by_cases h : a < a' ∧ Captured f s a ∧ Captured f s a' <;> simp [h]

/-- The union and second-order Bonferroni inequalities give two-sided escape bounds. -/
theorem escape_bonferroni_bounds
    [Fintype A] [Fintype Y] [LinearOrder A]
    (q : A -> Y -> Real)
    (hq_nonneg : forall b y, 0 ≤ q b y)
    (hq_sum : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    1 - ∑ a, captureProbability q f a ≤ escapeProbability q f ∧
      escapeProbability q f ≤
        1 - ∑ a, captureProbability q f a + pairProbabilitySum q f := by
  classical
  rw [escapeProbability_eq_indicator_sum,
    captureProbability_sum_eq_indicator_sum,
    pairProbabilitySum_eq_indicator_sum]
  have htotal := sample_weight_sum_one q hq_sum
  constructor
  · calc
      1 - ∑ s : Sample A Y,
          sampleWeight q s * singleIndicator (fun a => Captured f s a) Finset.univ =
          ∑ s : Sample A Y, sampleWeight q s *
            (1 - singleIndicator (fun a => Captured f s a) Finset.univ) := by
        calc
          _ = (∑ s : Sample A Y, sampleWeight q s) -
              ∑ s : Sample A Y, sampleWeight q s *
                singleIndicator (fun a => Captured f s a) Finset.univ := by rw [htotal]
          _ = ∑ s : Sample A Y, (sampleWeight q s - sampleWeight q s *
                singleIndicator (fun a => Captured f s a) Finset.univ) :=
            (Finset.sum_sub_distrib
              (fun s : Sample A Y => sampleWeight q s)
              (fun s : Sample A Y => sampleWeight q s *
                singleIndicator (fun a => Captured f s a) Finset.univ)).symm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro s _
            ring
      _ ≤ ∑ s : Sample A Y,
          sampleWeight q s * noneIndicator (fun a => Captured f s a) Finset.univ := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left
          (bonferroni_indicators (fun a => Captured f s a) Finset.univ).1
          (sampleWeight_nonneg q hq_nonneg s)
  · calc
      (∑ s : Sample A Y,
          sampleWeight q s * noneIndicator (fun a => Captured f s a) Finset.univ) ≤
          ∑ s : Sample A Y, sampleWeight q s *
            (1 - singleIndicator (fun a => Captured f s a) Finset.univ +
              pairIndicator (fun a => Captured f s a) Finset.univ) := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left
          (bonferroni_indicators (fun a => Captured f s a) Finset.univ).2
          (sampleWeight_nonneg q hq_nonneg s)
      _ = 1 -
          ∑ s : Sample A Y,
            sampleWeight q s * singleIndicator (fun a => Captured f s a) Finset.univ +
          ∑ s : Sample A Y,
            sampleWeight q s * pairIndicator (fun a => Captured f s a) Finset.univ := by
        simp_rw [mul_add, mul_sub, mul_one]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, htotal]

#print axioms escape_bonferroni_bounds
#print axioms no_capture_iff_isEscaped

end

end D5.S0.Asymptotics.WeightedProbability.FiniteBonferroni
