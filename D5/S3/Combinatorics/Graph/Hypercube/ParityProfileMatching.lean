/- GID: D5/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer couplings of opposite parity classes have a sharp common-one count across coordinates. -/

import D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching
import D5.S3.Combinatorics.Transportation.OrderedMarginAllocation
import D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity
import Mathlib.Algebra.Order.Floor.Div

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching

open Finset DirectionMatching
open D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity (binary)
open D5.S3.Combinatorics.Transportation.OrderedMarginAllocation
open scoped Classical

private def commonOne {I T : Type*} [Fintype T]
    (p q : T → I → Bool) (weight : T → ℕ) (i : I) : ℕ :=
  ∑ x, if p x i && q x i then weight x else 0

private def differing {I T : Type*} [Fintype T]
    (p q : T → I → Bool) (weight : T → ℕ) (i : I) : ℕ :=
  ∑ x, if p x i ≠ q x i then weight x else 0

private theorem deviation_total {I T : Type*} [Fintype I] [Fintype T]
    (p q : T → I → Bool) (weight : T → ℕ) (h : ℕ)
    (total : ∑ x, weight x = 2 * h)
    (fairP : ∀ i, (∑ x, if p x i then weight x else 0) = h)
    (fairQ : ∀ i, (∑ x, if q x i then weight x else 0) = h)
    (differ : ∀ x, ∃ i, p x i ≠ q x i) :
    h ≤ ∑ i, (h - commonOne p q weight i) := by
  have mismatch (i : I) : differing p q weight i = 2 * (h - commonOne p q weight i) := by
    have identity (x : T) :
        (if p x i then weight x else 0) + (if q x i then weight x else 0) =
        2 * (if p x i && q x i then weight x else 0) +
          (if p x i ≠ q x i then weight x else 0) := by
      cases p x i <;> cases q x i <;> simp [two_mul]
    have summed := sum_congr (rfl : (univ : Finset T) = univ) (fun x _ => identity x)
    simp only [sum_add_distrib, ← mul_sum, fairP, fairQ] at summed
    change h + h = 2 * commonOne p q weight i + differing p q weight i at summed
    omega
  have count : (∑ x, weight x) ≤ ∑ i, differing p q weight i := by
    unfold differing
    rw [sum_comm]
    apply sum_le_sum
    intro x _
    obtain ⟨i, hi⟩ := differ x
    have seek : weight x = (if p x i ≠ q x i then weight x else 0) := by simp [hi]
    calc
      _ = (if p x i ≠ q x i then weight x else 0) := seek
      _ ≤ _ := single_le_sum
        (f := fun j : I => if p x j ≠ q x j then weight x else 0)
        (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [total] at count
  simp_rw [mismatch] at count
  rw [← mul_sum] at count
  omega

private theorem deviation_bound {I T : Type*} [Fintype I] [Fintype T]
    (p q : T → I → Bool) (weight : T → ℕ) (h : ℕ) (C : I → ℕ)
    (total : ∑ x, weight x = 2 * h)
    (fairP : ∀ i, (∑ x, if p x i then weight x else 0) = h)
    (fairQ : ∀ i, (∑ x, if q x i then weight x else 0) = h)
    (differ : ∀ x, ∃ i, p x i ≠ q x i)
    (bound : ∀ i, h - commonOne p q weight i ≤ C i) :
    h ≤ ∑ i, C i := by
  calc
    h ≤ ∑ i, (h - commonOne p q weight i) :=
      deviation_total p q weight h total fairP fairQ differ
    _ ≤ ∑ i : I, C i := sum_le_sum fun i _ => bound i

private theorem allocate_under_caps {R C : Type*} [Fintype R] [Fintype C]
    (supply : R → ℕ) (caps : C → ℕ)
    (fits : ∑ a, supply a ≤ ∑ b, caps b) :
    ∃ w : R → C → ℕ,
      (∀ a, ∑ b, w a b = supply a) ∧
      ∀ b, (∑ a, w a b) ≤ caps b := by
  classical
  let demand : Option R → ℕ := fun a => a.elim ((∑ b, caps b) - (∑ a, supply a)) supply
  have balanced : (∑ a, demand a) = ∑ b, caps b := by
    rw [Fintype.sum_option]
    exact Nat.sub_add_cancel fits
  let rows := (univ : Finset (Option R)).toList
  let cols := (univ : Finset C).toList
  let state := orderedAllocation rows cols demand caps
  have complete := ordered_allocation_complete rows cols (by simp [rows])
    (by simp [cols]) demand caps balanced
  refine ⟨fun a b => state.2.2 (some a, b), fun a => (complete.1 (some a)).2, ?_⟩
  intro b
  have hc := (complete.2.1 b).2
  change (∑ a : Option R, state.2.2 (a, b)) = caps b at hc
  rw [Fintype.sum_option] at hc
  change (∑ a : R, state.2.2 (some a, b)) ≤ caps b
  omega

private theorem batch_matches (n k : ℕ) (target : Fin (n + 2) → ℕ)
    (total : ∑ i, target i = k * 2 ^ n) :
    ∃ (partner : Fin k → ParityClass (n + 2) 0 ≃ ParityClass (n + 2) 1)
      (direction : Fin k → ParityClass (n + 2) 0 → Fin (n + 2)),
      (∀ j p, partner j p = flipToOdd p (direction j p)) ∧
      ∀ i, (∑ j, ∑ p, if direction j p = i then 1 else (0 : ℕ)) = 2 * target i := by
  classical
  let batchSize (_ : Fin k) : ℕ := 2 ^ n
  let rows := (univ : Finset (Fin k)).toList
  let columns := (univ : Finset (Fin (n + 2))).toList
  let state := orderedAllocation rows columns batchSize target
  have balanced : (∑ j, batchSize j) = ∑ i, target i := by simp [batchSize, total]
  have feasible := ordered_allocation_complete rows columns (by simp [rows])
    (by simp [columns]) batchSize target balanced
  let demands (j : Fin k) (i : Fin (n + 2)) : ℕ := 2 * state.2.2 (j, i)
  have rowTotal (j : Fin k) : (∑ i, demands j i) = 2 ^ (n + 1) := by
    unfold demands
    rw [← mul_sum, (feasible.1 j).2, pow_succ, mul_comm]
  have rowEven (j : Fin k) (i : Fin (n + 2)) : Even (demands j i) :=
    even_two.mul_right _
  have matching (j : Fin k) :=
    (exact_matching_directions n (demands j) (rowTotal j)).mpr (rowEven j)
  choose partner direction edges counts using matching
  refine ⟨partner, direction, edges, fun i => ?_⟩
  simp_rw [counts]
  unfold demands
  rw [← mul_sum, (feasible.2.1 i).2]

private theorem parity_fair (n : ℕ) (t : ZMod 2) (i : Fin (n + 2)) :
    2 * (∑ p : ParityClass (n + 2) t, if p.val i = 1 then 1 else (0 : ℕ)) =
      Fintype.card (ParityClass (n + 2) t) := by
  classical
  obtain ⟨j, hji⟩ := exists_ne i
  let d : Profile (n + 2) := Pi.single i 1 + Pi.single j 1
  have zero : parity d = 0 := by
    change (∑ k : Fin (n + 2), (Pi.single i (1 : ZMod 2) k + Pi.single j (1 : ZMod 2) k)) =
      (0 : ZMod 2)
    rw [sum_add_distrib]
    simp [show (1 : ZMod 2) + 1 = 0 by decide]
  have add_zero (p : Profile (n + 2)) : parity (p + d) = parity p := by
    change (∑ k : Fin (n + 2), (p k + d k)) = ∑ k : Fin (n + 2), p k
    rw [sum_add_distrib]
    exact _root_.add_eq_left.mpr zero
  let move (p : ParityClass (n + 2) t) : ParityClass (n + 2) t :=
    ⟨p.val + d, (add_zero p.val).trans p.property⟩
  have twice (p : ParityClass (n + 2) t) : move (move p) = p := by
    apply Subtype.ext
    funext k
    change (p.val k + d k) + d k = p.val k
    have dd : d k + d k = 0 := by
      rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
    rw [add_assoc, dd, _root_.add_zero]
  let E : Equiv.Perm (ParityClass (n + 2) t) := (Function.Involutive.toPerm move twice)
  let bit (p : ParityClass (n + 2) t) : ℕ := if p.val i = 1 then 1 else 0
  have complement (p : ParityClass (n + 2) t) : bit p + bit (E p) = 1 := by
    have di : d i = 1 := by simp [d, Pi.single_eq_of_ne hji.symm]
    change (if p.val i = 1 then 1 else 0) + (if p.val i + d i = 1 then 1 else 0) = 1
    rw [di]
    rcases binary (p.val i) with h | h <;> simp [h, show (1 : ZMod 2) + 1 = 0 by decide]
  change 2 * (∑ p, bit p) = _
  calc
    _ = (∑ p, bit p) + (∑ p, bit (E p)) := by rw [Equiv.sum_comp E bit, two_mul]
    _ = ∑ p, (bit p + bit (E p)) := sum_add_distrib.symm
    _ = _ := by simp [complement]

private def edgeWeight {A B : Type*} [DecidableEq B] {k : ℕ}
    (partner : Fin k → A ≃ B) (a : A) (b : B) : ℕ :=
  ∑ j, if partner j a = b then 1 else 0

private theorem edge_margins {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] {k : ℕ}
    (partner : Fin k → A ≃ B) :
    (∀ a, ∑ b, edgeWeight partner a b = k) ∧ (∀ b, ∑ a, edgeWeight partner a b = k) := by
  classical
  constructor
  · intro a
    unfold edgeWeight
    rw [sum_comm]
    simp
  · intro b
    unfold edgeWeight
    rw [sum_comm]
    have single (j : Fin k) : (∑ a, if partner j a = b then (1 : ℕ) else 0) = 1 := by
      rw [← Equiv.sum_comp (partner j).symm]
      simp
    simp [single]

private theorem edge_mismatch {n k : ℕ}
    (partner : Fin k → ParityClass (n + 2) 0 ≃ ParityClass (n + 2) 1)
    (direction : Fin k → ParityClass (n + 2) 0 → Fin (n + 2))
    (edges : ∀ j p, partner j p = flipToOdd p (direction j p))
    (i : Fin (n + 2)) :
    (∑ p, ∑ q, if p.val i ≠ q.val i then edgeWeight partner p q else 0) =
      ∑ j, ∑ p, if direction j p = i then 1 else 0 := by
  classical
  unfold edgeWeight
  have single (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
      (if p.val i ≠ q.val i then (∑ j, if partner j p = q then (1 : ℕ) else 0) else 0) =
        ∑ j, if partner j p = q ∧ p.val i ≠ q.val i then 1 else 0 := by
    by_cases h : p.val i ≠ q.val i <;> simp [h]
  trans ∑ p, ∑ q, ∑ j, if partner j p = q ∧ p.val i ≠ q.val i then 1 else 0
  · exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => single p q
  simp_rw [sum_comm (s := (univ : Finset (ParityClass (n + 2) 1))) (t := (univ : Finset (Fin k)))]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro p _
  have single_edge (q : ParityClass (n + 2) 1) :
      (if partner j p = q ∧ p.val i ≠ q.val i then (1 : ℕ) else 0) =
        if partner j p = q then (if p.val i ≠ (partner j p).val i then 1 else 0) else 0 := by
    by_cases h : partner j p = q
    · subst q
      simp
    · simp [h]
  simp_rw [single_edge]
  rw [Finset.sum_ite_eq_of_mem _ _ _ (mem_univ _), edges]
  change (if p.val i ≠ p.val i + (Pi.single (direction j p) 1 : Profile (n + 2)) i
      then (1 : ℕ) else 0) =
    if direction j p = i then 1 else 0
  by_cases h : direction j p = i
  · have neq : p.val i ≠ p.val i + 1 := by
      intro equality
      exact one_ne_zero (add_left_cancel (equality.symm.trans (add_zero _).symm))
    simp [h, neq]
  · simp [h]

private theorem profile_card (n : ℕ) (t : ZMod 2) :
    Fintype.card (ParityClass (n + 2) t) = 2 ^ (n + 1) := by
  rw [Fintype.card_congr (tailEquiv (n + 1) t), Fintype.card_fun, Fintype.card_fin, ZMod.card]

private theorem target_under_coordinate_caps (n M : ℕ) (C : Fin (n + 2) → ℕ) (capacity : M ≤ ∑ i, C i) :
    ∃ target : Fin (n + 2) → ℕ, (∑ i, target i) = M ∧ ∀ i, target i ≤ C i := by
  have fits : (∑ _ : Unit, M) ≤ ∑ i : Fin (n + 2), C i := by simpa using capacity
  obtain ⟨w, sum, caps⟩ :=
    allocate_under_caps (fun _ : Unit => M) C fits
  exact ⟨w (), sum (), fun i => by simpa using caps i⟩

private theorem matching_profile_counts (n k : ℕ) (C : Fin (n + 2) → ℕ) (capacity : k * 2 ^ n ≤ ∑ i, C i) :
    ∃ w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, w p q = k) ∧ (∀ q, ∑ p, w p q = k) ∧
      ∀ i : Fin (n + 2), (∑ p, ∑ q, if p.val i ≠ q.val i then w p q else 0) ≤ 2 * C i := by
  obtain ⟨target, total, caps⟩ := target_under_coordinate_caps n (k * 2 ^ n) C capacity
  obtain ⟨partner, direction, edges, counts⟩ := batch_matches n k target total
  refine ⟨edgeWeight partner, (edge_margins partner).1, (edge_margins partner).2, fun i => ?_⟩
  rw [edge_mismatch partner direction edges i, counts]
  exact Nat.mul_le_mul_left 2 (caps i)

private theorem weighted_bit_totals (n k : ℕ) (w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (rows : ∀ p, ∑ q, w p q = k) (cols : ∀ q, ∑ p, w p q = k) (i : Fin (n + 2)) :
    (∑ p, ∑ q, if p.val i = 1 then w p q else 0) = k * 2 ^ n ∧
    (∑ p, ∑ q, if q.val i = 1 then w p q else 0) = k * 2 ^ n := by
  classical
  have fair (t : ZMod 2) :
      ∑ p : ParityClass (n + 2) t, (if p.val i = 1 then 1 else (0 : ℕ)) = 2 ^ n := by
    have h := parity_fair n t i
    rw [profile_card, pow_succ] at h
    omega
  constructor
  · have rowSum (p : ParityClass (n + 2) 0) :
        (∑ q, if p.val i = 1 then w p q else 0) = k * (if p.val i = 1 then 1 else 0) := by
      by_cases h : p.val i = 1 <;> simp [h, rows]
    simp_rw [rowSum]
    rw [← mul_sum, fair]
  · rw [sum_comm]
    have colSum (q : ParityClass (n + 2) 1) :
        (∑ p, if q.val i = 1 then w p q else 0) = k * (if q.val i = 1 then 1 else 0) := by
      by_cases h : q.val i = 1 <;> simp [h, cols]
    simp_rw [colSum]
    rw [← mul_sum, fair]

/-- The weight of the pairs with bit one on both sides in coordinate `i`. -/
noncomputable def commonOneCount {n : ℕ} (w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (i : Fin (n + 2)) : ℕ :=
  ∑ p, ∑ q, if p.val i = 1 ∧ q.val i = 1 then w p q else 0

private theorem coordinates_detect_difference {n : ℕ} (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
    ∃ i : Fin (n + 2), decide (p.val i = 1) ≠ decide (q.val i = 1) := by
  by_contra! equal
  have same : p.val = q.val := by
    funext i
    have h := equal i
    rcases binary (x := p.val i) with hp | hp <;>
      rcases binary (x := q.val i) with hq | hq <;> simp_all
  exact zero_ne_one (p.property.symm.trans ((congrArg parity same).trans q.property))

private theorem profile_cap_necessary (n k : ℕ) (C : Fin (n + 2) → ℕ)
    (w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (rows : ∀ p, ∑ q, w p q = k) (cols : ∀ q, ∑ p, w p q = k)
    (common : ∀ i, k * 2 ^ n - C i ≤ commonOneCount w i) :
    k * 2 ^ n ≤ ∑ i, C i := by
  classical
  let T := ParityClass (n + 2) 0 × ParityClass (n + 2) 1
  let p : T → Fin (n + 2) → Bool := fun a i => decide (a.1.val i = 1)
  let q : T → Fin (n + 2) → Bool := fun a i => decide (a.2.val i = 1)
  let weight : T → ℕ := fun a => w a.1 a.2
  have total : (∑ a, weight a) = 2 * (k * 2 ^ n) := by
    unfold weight
    rw [Fintype.sum_prod_type]
    simp only [rows, sum_const, card_univ, nsmul_eq_mul, profile_card]
    rw [pow_succ]
    ac_rfl
  have left (i : Fin (n + 2)) :
      (∑ a, if p a i then weight a else 0) = k * 2 ^ n := by
    rw [Fintype.sum_prod_type]
    simpa [p, weight] using (weighted_bit_totals n k w rows cols i).1
  have right (i : Fin (n + 2)) :
      (∑ a, if q a i then weight a else 0) = k * 2 ^ n := by
    rw [Fintype.sum_prod_type]
    simpa [q, weight] using (weighted_bit_totals n k w rows cols i).2
  have typed (i : Fin (n + 2)) : commonOne p q weight i = commonOneCount w i := by
    unfold commonOne commonOneCount
    rw [Fintype.sum_prod_type]
    simp [p, q, weight]
  have cap (i : Fin (n + 2)) : k * 2 ^ n - commonOne p q weight i ≤ C i := by
    have h := common i
    rw [typed]
    omega
  have h := deviation_bound p q weight (k * 2 ^ n) C total left right
    (fun a => coordinates_detect_difference a.1 a.2) cap
  exact h

private theorem profile_cap_sufficient (n k : ℕ) (C : Fin (n + 2) → ℕ) (cap : k * 2 ^ n ≤ ∑ i, C i) :
    ∃ w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, w p q = k) ∧ (∀ q, ∑ p, w p q = k) ∧
      ∀ i, k * 2 ^ n - C i ≤ commonOneCount w i := by
  classical
  obtain ⟨w, rows, cols, mismatch⟩ := matching_profile_counts n k C cap
  refine ⟨w, rows, cols, ?_⟩
  intro i
  let diff : ℕ := ∑ p, ∑ q, if p.val i ≠ q.val i then w p q else 0
  have pointwise (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
      (if p.val i = 1 then w p q else 0) + (if q.val i = 1 then w p q else 0) =
      2 * (if p.val i = 1 ∧ q.val i = 1 then w p q else 0) +
        (if p.val i ≠ q.val i then w p q else 0) := by
    rcases binary (x := p.val i) with hp | hp <;>
      rcases binary (x := q.val i) with hq | hq <;> simp [hp, hq, two_mul, zero_ne_one]
  have summed := sum_congr (rfl : (univ : Finset (ParityClass (n + 2) 0)) = univ)
    (fun p _ => sum_congr (rfl : (univ : Finset (ParityClass (n + 2) 1)) = univ) (fun q _ => pointwise p q))
  simp only [sum_add_distrib, ← mul_sum, (weighted_bit_totals n k w rows cols i).1,
    (weighted_bit_totals n k w rows cols i).2] at summed
  change k * 2 ^ n + k * 2 ^ n = 2 * commonOneCount w i + diff at summed
  have diffBound : diff ≤ 2 * C i := mismatch i
  omega

private theorem profile_threshold (n k : ℕ) (C : Fin (n + 2) → ℕ) :
    (∃ w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, w p q = k) ∧ (∀ q, ∑ p, w p q = k) ∧
      ∀ i, k * 2 ^ n - C i ≤ commonOneCount w i) ↔
      k * 2 ^ n ≤ ∑ i, C i := by
  constructor
  · rintro ⟨w, rows, cols, common⟩
    exact profile_cap_necessary n k C w rows cols common
  · exact profile_cap_sufficient n k C


private def balancedCommonOneCount (n k : ℕ) : ℕ :=
  let M := k * 2 ^ n
  M - (M + (n + 2 - 1)) / (n + 2)

/-- The maximum minimum common-one count across coordinates of an integer parity coupling. -/
theorem best_profile_count (n k : ℕ) (positive : 0 < k) :
    let best := balancedCommonOneCount n k
    (∃ w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, w p q = k) ∧ (∀ q, ∑ p, w p q = k) ∧
      ∀ i, best ≤ commonOneCount w i) ∧
    ∀ w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, w p q = k) → (∀ q, ∑ p, w p q = k) →
      ∃ i, commonOneCount w i ≤ best := by
  dsimp only [balancedCommonOneCount]
  let M := k * 2 ^ n
  let C := (M + (n + 2 - 1)) / (n + 2)
  have ceiling_le (cap : ℕ) : C ≤ cap ↔ M ≤ (n + 2) * cap := by
    simpa only [C, Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc (by omega : 1 ≤ n + 2)] using
      (ceilDiv_le_iff_le_mul (a := n + 2) (b := M) (c := cap) (by omega))
  have positiveM : 0 < M := Nat.mul_pos positive (by positivity)
  have positiveC : 0 < C := by
    have h : C ≠ 0 := by
      intro zero
      have cap := (ceiling_le 0).mp
        (show C ≤ 0 by omega)
      simp at cap
      omega
    exact Nat.pos_of_ne_zero h
  have capped : C ≤ M :=
    (ceiling_le M).mpr
      (by rw [Nat.add_mul]; omega)
  constructor
  · apply (profile_threshold n k (fun _ => C)).mpr
    simpa using (ceiling_le C).mp le_rfl
  · intro w rows cols
    by_contra! bad
    have lower (i : Fin (n + 2)) : M - (C - 1) ≤ commonOneCount w i := by
      have hi := bad i
      change M - C < commonOneCount w i at hi
      omega
    have tooSmall := profile_cap_necessary n k (fun _ => C - 1) w rows cols lower
    have h := (ceiling_le (C - 1)).mpr (by simpa using tooSmall)
    change C ≤ C - 1 at h
    exact (Nat.not_le_of_lt (Nat.sub_lt positiveC Nat.one_pos)) h

/-- A vector is a feasible floor when one coupling meets all its coordinate bounds. -/
def FeasibleProfileFloor (n k : ℕ) (v : Fin (n + 2) → ℕ) : Prop :=
  ∃ w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
    (∀ p, ∑ q, w p q = k) ∧ (∀ q, ∑ p, w p q = k) ∧
    ∀ i, v i ≤ commonOneCount w i

private theorem common_le_marginal (n k : ℕ)
    (w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (rows : ∀ p, ∑ q, w p q = k) (cols : ∀ q, ∑ p, w p q = k) (i : Fin (n + 2)) :
    commonOneCount w i ≤ k * 2 ^ n := by
  rw [← (weighted_bit_totals n k w rows cols i).1]
  unfold commonOneCount
  apply sum_le_sum
  intro p _
  apply sum_le_sum
  intro q _
  split
  · rename_i h
    simp [h.1]
  · exact Nat.zero_le _

private theorem feasible_floor_iff (n k : ℕ) (v : Fin (n + 2) → ℕ) :
    FeasibleProfileFloor n k v ↔
      (∀ i, v i ≤ k * 2 ^ n) ∧ k * 2 ^ n ≤ ∑ i, (k * 2 ^ n - v i) := by
  constructor
  · rintro ⟨w, rows, cols, bounds⟩
    have bounded (i : Fin (n + 2)) : v i ≤ k * 2 ^ n :=
      (bounds i).trans (common_le_marginal n k w rows cols i)
    refine ⟨bounded, ?_⟩
    apply (profile_threshold n k (fun i => k * 2 ^ n - v i)).1
    refine ⟨w, rows, cols, fun i => ?_⟩
    rw [Nat.sub_sub_self (bounded i)]
    exact bounds i
  · rintro ⟨bounded, cap⟩
    obtain ⟨w, rows, cols, bounds⟩ := (profile_threshold n k (fun i => k * 2 ^ n - v i)).2 cap
    refine ⟨w, rows, cols, fun i => ?_⟩
    have h := bounds i
    change k * 2 ^ n - (k * 2 ^ n - v i) ≤ commonOneCount w i at h
    rwa [Nat.sub_sub_self (bounded i)] at h

/-- A profile count vector with the full coordinate sum allowed by opposite parity. -/
def ProfileBoundary (n k : ℕ) (v : Fin (n + 2) → ℕ) : Prop :=
  (∀ i, v i ≤ k * 2 ^ n) ∧ ∑ i, (k * 2 ^ n - v i) = k * 2 ^ n

/-- A feasible floor is dominated by a vector on the profile boundary. -/
theorem profile_floor_dominated {n k : ℕ} {v : Fin (n + 2) → ℕ}
    (h : FeasibleProfileFloor n k v) :
    ∃ u, ProfileBoundary n k u ∧ ∀ i, v i ≤ u i := by
  let M := k * 2 ^ n
  obtain ⟨bounded, capacity⟩ := (feasible_floor_iff n k v).1 h
  change M ≤ ∑ i, (M - v i) at capacity
  obtain ⟨a, total, caps⟩ := target_under_coordinate_caps n M (fun i => M - v i) capacity
  let u (i : Fin (n + 2)) := M - a i
  have aLe (i : Fin (n + 2)) : a i ≤ M := (caps i).trans (Nat.sub_le _ _)
  refine ⟨u, ⟨fun _ => Nat.sub_le _ _, ?_⟩, fun i => ?_⟩
  · change (∑ i, (M - (M - a i))) = M
    simpa only [Nat.sub_sub_self (aLe _)] using total
  · have hi := bounded i
    have ai := caps i
    change v i ≤ M at hi
    change a i ≤ M - v i at ai
    change v i ≤ M - a i
    omega

/-- The maximal feasible floors are exactly the profile boundary vectors. -/
theorem exact_profile_frontier (n k : ℕ) (v : Fin (n + 2) → ℕ) :
    (FeasibleProfileFloor n k v ∧
      ∀ u, FeasibleProfileFloor n k u → (∀ i, v i ≤ u i) → u = v) ↔
    ProfileBoundary n k v := by
  let M := k * 2 ^ n
  constructor
  · rintro ⟨feasible, maximal⟩
    obtain ⟨u, boundary, dominates⟩ := profile_floor_dominated feasible
    have eq := maximal u ((feasible_floor_iff n k u).2 ⟨boundary.1, boundary.2.ge⟩) dominates
    simpa only [eq] using boundary
  · rintro ⟨bounded, equality⟩
    refine ⟨(feasible_floor_iff n k v).2 ⟨bounded, equality.ge⟩, ?_⟩
    intro u feasible dominates
    apply funext
    intro i
    by_contra! neq
    have strict : v i < u i := lt_of_le_of_ne (dominates i) (Ne.symm neq)
    obtain ⟨uBound, uCapacity⟩ := (feasible_floor_iff n k u).1 feasible
    have less : M - u i < M - v i := by
      have hu := uBound i
      have hv := bounded i
      change u i ≤ M at hu
      change v i ≤ M at hv
      omega
    have totalLess : (∑ j, (M - u j)) < ∑ j, (M - v j) :=
      sum_lt_sum (fun j _ => Nat.sub_le_sub_left (dominates j) M) ⟨i, mem_univ i, less⟩
    exact (Nat.not_lt_of_ge (equality.le.trans uCapacity)) totalLess


end D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
