/- GID: D5/S0/Asymptotics/WeightedProbability/FiniteProductCapture
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/FiniteProductCapture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independent column-weighted listings have an exact one-row capture mass. -/

/- Library-search audit trail (2026-08-15):
   * Repository searches found the uniform cardinal laws in `Diagonal/CaptureCount` and
     `Diagonal/CaptureIntersectionCardinality`, but no varying-marginal capture law.
   * Pinned Mathlib supplies finite sum-product factorization but no theorem matching the
     weighted twisted-diagonal capture events below.
   * `listing` is connected to the existing `EscapeCount.diagonal`, and
     `fixedMass_pmf_toReal` bridges the existing `SkewedEscapeMass.fixedMass`; the event
     formulas are derived from independently normalized cell weights, not installed by
     definition.
-/

import D5.S0.Diagonal.EscapeCount
import D5.S0.Asymptotics.SkewedEscapeMass
import Mathlib

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.FiniteProductCapture

open D5.S0.Diagonal.EscapeCount

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- Off-diagonal entries in one row of a finite listing. -/
abbrev OffRow (A Y : Type*) (a : A) := {b : A // b ≠ a} -> Y

/-- Independent coordinates for a listing: its diagonal and all off-diagonal rows. -/
abbrev Sample (A Y : Type*) :=
  (A -> Y) × ((a : A) -> OffRow A Y a)

/-- Reassemble the matrix listing represented by independent diagonal and row coordinates. -/
def listing [DecidableEq A] (s : Sample A Y) : A -> A -> Y :=
  fun a b => if h : b = a then s.1 a else s.2 a ⟨b, h⟩

/-- Product mass when every cell in column `b` independently has marginal `q b`. -/
def sampleWeight [Fintype A] [DecidableEq A]
    (q : A -> Y -> Real) (s : Sample A Y) : Real :=
  (∏ b, q b (s.1 b)) * ∏ a, ∏ b, q b.1 (s.2 a b)

/-- Product mass of one off-diagonal row. -/
def rowWeight [Fintype A] [DecidableEq A]
    (q : A -> Y -> Real) (a : A) (r : OffRow A Y a) : Real :=
  ∏ b, q b.1 (r b)

/-- Row `a` captures the repository's twisted diagonal. -/
def Captured [DecidableEq A]
    (f : Y -> Y) (s : Sample A Y) (a : A) : Prop :=
  listing s a = diagonal f (listing s)

/-- Captured off-diagonal rows determined by the listing diagonal. -/
def targetRows (f : Y -> Y) (X : A -> Y) :
    (a : A) -> OffRow A Y a :=
  fun _a b => f (X b.1)

/-- Capture in the product coordinates is fixedness on the diagonal plus one pinned row. -/
theorem captured_iff_twisted_diagonal [DecidableEq A]
    (f : Y -> Y) (s : Sample A Y) (a : A) :
    Captured f s a <->
      f (s.1 a) = s.1 a ∧ s.2 a = targetRows f s.1 a := by
  constructor
  · intro h
    constructor
    · have ha := congrFun h a
      simpa [Captured, listing, diagonal] using ha.symm
    · funext b
      have hb := congrFun h b.1
      simpa [Captured, listing, diagonal, targetRows, b.property] using hb
  · rintro ⟨hfixed, hrow⟩
    funext b
    by_cases hba : b = a
    · subst b
      simpa [Captured, listing, diagonal] using hfixed.symm
    · have hb := congrFun hrow ⟨b, hba⟩
      simpa [Captured, listing, diagonal, targetRows, hba] using hb

/-- Weighted probability of an event in the finite independent listing model. -/
def eventProbability [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (P : Sample A Y -> Prop) [DecidablePred P] : Real :=
  ∑ s : Sample A Y, if P s then sampleWeight q s else 0

/-- Weighted fixed-point mass `q_a(Fix f)`. -/
noncomputable def fixedMass [Fintype Y]
    (q : A -> Y -> Real) (f : Y -> Y) (a : A) : Real := by
  classical exact ∑ y, if f y = y then q a y else 0

/-- The real fixed-point mass agrees with the existing PMF fixed-point mass after `toReal`. -/
theorem fixedMass_pmf_toReal [Fintype Y]
    (q : PMF Y) (f : Y -> Y) (a : A) :
    fixedMass (fun _ y => (q y).toReal) f a =
      (D5.S0.Asymptotics.SkewedEscapeMass.fixedMass q f).toReal := by
  classical
  rw [D5.S0.Asymptotics.SkewedEscapeMass.fixedMass, ENNReal.toReal_sum]
  · simpa [fixedMass] using
      (Finset.sum_filter (s := Finset.univ) (fun y : Y => f y = y)
        (fun y => (q y).toReal)).symm
  · intro y _
    exact PMF.apply_ne_top q y

/-- One-coordinate collision mass `sum_z q_b(z) q_b(f(z))`. -/
def collisionMass [Fintype Y]
    (q : A -> Y -> Real) (f : Y -> Y) (b : A) : Real :=
  ∑ z, q b z * q b (f z)

/-- Squared weighted fixed-point mass used by a two-row capture event. -/
noncomputable def fixedSquareMass [Fintype Y]
    (q : A -> Y -> Real) (f : Y -> Y) (a : A) : Real := by
  classical exact ∑ y, if f y = y then q a y ^ 2 else 0

/-- Squared collision mass used away from two captured rows. -/
def collisionSquareMass [Fintype Y]
    (q : A -> Y -> Real) (f : Y -> Y) (b : A) : Real :=
  ∑ z, q b z * q b (f z) ^ 2

/-- Probability of capture at one address. -/
noncomputable def captureProbability [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) (a : A) : Real := by
  classical exact eventProbability q (fun s => Captured f s a)

/-- Probability of simultaneous capture at two addresses. -/
noncomputable def pairCaptureProbability [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) (a a' : A) : Real := by
  classical exact eventProbability q (fun s => Captured f s a ∧ Captured f s a')

private theorem offRow_weight_sum [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1) (a : A) :
    (∑ r : OffRow A Y a, ∏ b, q b.1 (r b)) = 1 := by
  rw [← Fintype.prod_sum]
  simp [hq]

set_option maxHeartbeats 4000000 in
-- Dependent finite-product factorization requires additional elaboration budget.
private theorem allRows_weight_sum [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1) :
    (∑ R : (a : A) -> OffRow A Y a, ∏ a, ∏ b, q b.1 (R a b)) = 1 := by
  calc
    _ = ∏ a, ∑ r : OffRow A Y a, ∏ b, q b.1 (r b) :=
      (Fintype.prod_sum fun (a : A) (r : OffRow A Y a) =>
        ∏ b, q b.1 (r b)).symm
    _ = 1 := by simp [offRow_weight_sum q hq]

/-- Fixing selected independent rows leaves exactly their product mass. -/
theorem constrainedRows_weight_sum [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1)
    (C : Finset A) (target : (a : A) -> OffRow A Y a) :
    (∑ R : (a : A) -> OffRow A Y a,
        if (forall a, a ∈ C -> R a = target a) then
          ∏ a, rowWeight q a (R a)
        else 0) =
      ∏ a ∈ C, rowWeight q a (target a) := by
  classical
  have hsummand : forall R : (a : A) -> OffRow A Y a,
      (if (forall a, a ∈ C -> R a = target a) then
          ∏ a, rowWeight q a (R a)
        else 0) =
      ∏ a, if a ∈ C then
        (if R a = target a then rowWeight q a (R a) else 0)
      else rowWeight q a (R a) := by
    intro R
    by_cases hC : forall a, a ∈ C -> R a = target a
    · rw [if_pos hC]
      apply Finset.prod_congr rfl
      intro a _
      by_cases ha : a ∈ C
      · simp [ha, hC a ha]
      · simp [ha]
    · rw [if_neg hC]
      push Not at hC
      obtain ⟨a, ha, hne⟩ := hC
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      simp [ha, hne]
  calc
    _ = ∏ a, ∑ r : OffRow A Y a,
        if a ∈ C then
          (if r = target a then rowWeight q a r else 0)
        else rowWeight q a r := by
      simp_rw [hsummand]
      symm
      exact Fintype.prod_sum fun a r => if a ∈ C then
        (if r = target a then rowWeight q a r else 0) else rowWeight q a r
    _ = ∏ a, if a ∈ C then rowWeight q a (target a) else 1 := by
      apply Finset.prod_congr rfl
      intro a _
      by_cases ha : a ∈ C
      · simp [ha]
      · simp [ha, rowWeight, offRow_weight_sum q hq]
    _ = ∏ a ∈ C, rowWeight q a (target a) := by
      simp [Finset.prod_ite_mem]

/-- Normalized marginals make the independent product weight sum to one. -/
theorem sample_weight_sum_one [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1) :
    (∑ s : Sample A Y, sampleWeight q s) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [sampleWeight]
  rw [← Fintype.sum_mul_sum]
  rw [show (∑ i : A -> Y, ∏ x, q x (i x)) = 1 by
    rw [← Fintype.prod_sum]
    simp [hq]]
  rw [allRows_weight_sum q hq]
  norm_num

/-- Exact one-address capture probability in the independent column-weighted model. -/
theorem capture_probability_exact [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) (a : A) :
    captureProbability q f a =
      fixedMass q f a *
        ∏ b : {b : A // b ≠ a}, collisionMass q f b.1 := by
  classical
  rw [captureProbability, eventProbability, Fintype.sum_prod_type]
  have hinner : forall X : A -> Y,
      (∑ R : (a : A) -> OffRow A Y a,
        if Captured f (X, R) a then sampleWeight q (X, R) else 0) =
      if f (X a) = X a then
        (∏ b, q b (X b)) * rowWeight q a (targetRows f X a)
      else 0 := by
    intro X
    by_cases hfixed : f (X a) = X a
    · simp only [captured_iff_twisted_diagonal, hfixed, true_and, if_true]
      simp_rw [sampleWeight]
      calc
        (∑ R : (a : A) -> OffRow A Y a,
            if R a = targetRows f X a then
              (∏ b, q b (X b)) * ∏ i, rowWeight q i (R i) else 0) =
            (∏ b, q b (X b)) *
          (∑ R : (a : A) -> OffRow A Y a,
            if R a = targetRows f X a then ∏ i, rowWeight q i (R i) else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro R _
              split <;> simp_all
        _ = _ := by
          rw [show (∑ R : (a : A) -> OffRow A Y a,
                if R a = targetRows f X a then ∏ i, rowWeight q i (R i) else 0) =
              rowWeight q a (targetRows f X a) by
            simpa using constrainedRows_weight_sum q hq {a} (targetRows f X)]
    · simp [captured_iff_twisted_diagonal, hfixed]
  simp_rw [hinner]
  have hsummand : forall X : A -> Y,
      (if f (X a) = X a then
          (∏ b, q b (X b)) * rowWeight q a (targetRows f X a)
        else 0) =
      ∏ b, if b = a then
        (if f (X b) = X b then q b (X b) else 0)
      else q b (X b) * q b (f (X b)) := by
    intro X
    by_cases hfixed : f (X a) = X a
    · rw [if_pos hfixed,
        Fintype.prod_eq_mul_prod_subtype_ne (fun b => q b (X b)) a,
        Fintype.prod_eq_mul_prod_subtype_ne
          (fun b => if b = a then
            (if f (X b) = X b then q b (X b) else 0)
          else q b (X b) * q b (f (X b))) a]
      simp only [if_pos, hfixed, rowWeight, targetRows]
      have hprod :
          (∏ b : {b : A // b ≠ a}, if b.1 = a then
              (if f (X b.1) = X b.1 then q b.1 (X b.1) else 0)
            else q b.1 (X b.1) * q b.1 (f (X b.1))) =
            ∏ b : {b : A // b ≠ a}, q b.1 (X b.1) * q b.1 (f (X b.1)) := by
        apply Finset.prod_congr rfl
        intro b _
        rw [if_neg b.property]
      rw [hprod, Finset.prod_mul_distrib]
      ring
    · rw [if_neg hfixed]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      simp [hfixed]
  simp_rw [hsummand]
  calc
    (∑ X : A -> Y, ∏ b, if b = a then
        (if f (X b) = X b then q b (X b) else 0)
      else q b (X b) * q b (f (X b))) =
        ∏ b, ∑ y, if b = a then
          (if f y = y then q b y else 0)
        else q b y * q b (f y) := by
      symm
      exact Fintype.prod_sum fun b y => if b = a then
        (if f y = y then q b y else 0) else q b y * q b (f y)
    _ = _ := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne
      (fun b => ∑ y, if b = a then
        (if f y = y then q b y else 0)
      else q b y * q b (f y)) a]
      simp only [if_pos]
      have hprod :
          (∏ b : {b : A // b ≠ a}, ∑ y, if b.1 = a then
              (if f y = y then q b.1 y else 0)
            else q b.1 y * q b.1 (f y)) =
            ∏ b : {b : A // b ≠ a}, collisionMass q f b.1 := by
        apply Finset.prod_congr rfl
        intro b _
        simp [b.property, collisionMass]
      rw [hprod]
      rfl

#print axioms captured_iff_twisted_diagonal
#print axioms fixedMass_pmf_toReal
#print axioms sample_weight_sum_one
#print axioms capture_probability_exact

end

end D5.S0.Asymptotics.WeightedProbability.FiniteProductCapture
