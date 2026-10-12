/- GID: D5/S1/Words/MBonacciMinimumGreedy
   generality: I
   mirror-B: D5/B/S1/Words/MBonacciMinimumGreedy
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Actual m-bonacci weights and full greedy minimum-complexity expansions. -/
import D5.S1.Words.MBonacciMinimumParikhDescent
import D5.S0.Tower.DBonacci.Values
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.MBonacciMinimumGreedy

open MBonacciSentinelDesubstitution
open MBonacciMinimumParikhDescent (parikhImage minimal_abelian_complexity_length)
open RankOneMorphismIterationBound (subst image image_add subst_append)
open D5.S0.Tower.DBonacci.Names (dbonacci dbonacci_add_two_of_lt dbonacci_add_two_of_le)

variable {m : ℕ} (hm : 2 ≤ m)

/-- Integer weights from the literal iterated image of zero. -/
def U (j : ℕ) : ℕ := (image (phi hm) j (zero hm)).length

/-- The sentinel length, written as a sum of actual image weights. -/
def S (k : ℕ) : ℕ := 1 + ∑ j ∈ Finset.range k, U hm j

private theorem letter_length_expansion (k : ℕ) (a : Fin m) :
    (image (phi hm) k a).length =
      if k < m - a.val then S hm k
      else ∑ i ∈ Finset.range (m - a.val), U hm (k - (m - a.val) + i) := by
  induction k generalizing a with
  | zero => simp [image, S, show 0 < m - a.val by have := a.isLt; omega]
  | succ k ih =>
    rw [image_add _ k 1]
    by_cases ha : a.val + 1 < m
    · let b : Fin m := ⟨a.val + 1, ha⟩
      have he : (subst (fun c => image (phi hm) k c) (image (phi hm) 1 a)).length =
          U hm k + (image (phi hm) k b).length := by
        simp [image, subst, phi, ha, b, U]
      rw [he, ih]
      have hb : b.val = a.val + 1 := rfl
      by_cases hk : k + 1 < m - a.val
      · have hk' : k < m - b.val := by omega
        rw [if_pos hk, if_pos hk']
        simp [S, Finset.sum_range_succ, Nat.add_comm, Nat.add_assoc]
      · have hk' : ¬ k < m - b.val := by omega
        rw [if_neg hk, if_neg hk']
        have hr : m - a.val = (m - b.val) + 1 := by omega
        rw [hr, Finset.sum_range_succ]
        have ht : k - (m - b.val) = k + 1 - (m - b.val + 1) := by omega
        rw [ht]
        have hend : k + 1 - (m - b.val + 1) + (m - b.val) = k := by omega
        rw [hend, Nat.add_comm]
    · have hr : m - a.val = 1 := by have := a.isLt; omega
      simp [image, subst, phi, ha, hr, U]

private theorem weight_recurrence (k : ℕ) :
    U hm k = if k < m then S hm k
      else ∑ i ∈ Finset.range m, U hm (k - m + i) := by
  simpa [U, zero] using letter_length_expansion hm k (zero hm)

private theorem short_weight (k : ℕ) (hk : k < m) : U hm k = 2 ^ k := by
  induction k with
  | zero => simp [U, image]
  | succ k ih =>
    have hk' : k < m := by omega
    rw [weight_recurrence hm, if_pos hk]
    have hs : S hm (k + 1) = S hm k + U hm k := by
      simp [S, Finset.sum_range_succ, Nat.add_assoc]
    rw [hs]
    have hw : S hm k = U hm k := by rw [weight_recurrence hm k, if_pos hk']
    rw [hw, ih hk', pow_succ]
    omega

private theorem weights_dbonacci (k : ℕ) : U hm k = dbonacci m (k + 2) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < m
    · rw [short_weight hm k hk, dbonacci_add_two_of_lt m k hk]
    · rw [weight_recurrence hm, if_neg hk, dbonacci_add_two_of_le m k (by omega),
        ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      exact ih (k - m + i.val) (by have := i.isLt; omega)

theorem sentinel_sum (k : ℕ) :
    (((T hm)^[k]) ([] : List (Fin m))).length + 1 = S hm k := by
  have hstep : ∀ k : ℕ, ((T hm)^[k + 1]) ([] : List (Fin m)) =
      image (phi hm) k (zero hm) ++ ((T hm)^[k]) [] := by
    intro k
    induction k with
    | zero => simp [T, subst, image]
    | succ k ih =>
      simpa [T, subst_append, image, Function.iterate_succ_apply',
        List.append_assoc] using congrArg (T hm) ih
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [hstep, List.length_append]
    simpa [S, Finset.sum_range_succ, U, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using congrArg (fun x => U hm k + x) ih

private theorem sentinel_recurrence (k : ℕ) :
    S hm k = if k < m then U hm k else U hm k + S hm (k - m) := by
  by_cases hk : k < m
  · rw [if_pos hk]
    exact (by rw [weight_recurrence hm k, if_pos hk])
  · rw [if_neg hk]
    have hu : U hm k = ∑ i ∈ Finset.range m, U hm (k - m + i) := by
      rw [weight_recurrence hm, if_neg hk]
    have he : k = (k - m) + m := by omega
    unfold S
    conv_lhs => rw [he, Finset.sum_range_add]
    rw [hu]
    omega

private theorem scanner_bounds (k : ℕ) : U hm k ≤ S hm k ∧ S hm k < U hm (k + 1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have huS : U hm k ≤ S hm k := by
      rw [sentinel_recurrence hm]
      split_ifs <;> omega
    refine ⟨huS, ?_⟩
    let a : Fin m := ⟨1, by omega⟩
    have he : U hm (k + 1) = U hm k + (image (phi hm) k a).length := by
      rw [U, image_add _ k 1]
      simp [image, subst, phi, zero, U, a, show 1 < m by omega]
    have hl := letter_length_expansion hm k a
    change (image (phi hm) k a).length =
      if k < m - 1 then S hm k
      else ∑ i ∈ Finset.range (m - 1), U hm (k - (m - 1) + i) at hl
    by_cases hk : k < m
    · rw [sentinel_recurrence hm k, if_pos hk, he]
      by_cases ht : k < m - 1
      · rw [hl, if_pos ht]
        have hp : 0 < S hm k := by unfold S; omega
        omega
      · rw [hl, if_neg ht]
        have hsum := Finset.single_le_sum (f := fun i => U hm (k - (m - 1) + i))
          (fun i _ => Nat.zero_le _) (show 0 ∈ Finset.range (m - 1) by simp; omega)
        have hp : 0 < U hm (k - (m - 1)) := by
          rw [weights_dbonacci hm]
          exact D5.S0.Tower.DBonacci.Values.dbonacci_level_pos m (k - (m - 1)) (by omega)
        simp only [Nat.add_zero] at hsum
        omega
    · have hnot : ¬ k < m - 1 := by omega
      have hlong : S hm k = U hm k + S hm (k - m) := by
        simpa only [if_neg hk] using sentinel_recurrence hm k
      have hl' : (image (phi hm) k a).length =
          ∑ i ∈ Finset.range (m - 1), U hm (k - (m - 1) + i) := by
        simpa only [if_neg hnot] using hl
      rw [hl'] at he
      rw [hlong, he]
      have hsum := Finset.single_le_sum (f := fun i => U hm (k - (m - 1) + i))
        (fun i _ => Nat.zero_le _) (show 0 ∈ Finset.range (m - 1) by simp; omega)
      simp only [Nat.add_zero] at hsum
      have hi := (ih (k - m) (by omega)).2
      have ht : k - (m - 1) = k - m + 1 := by omega
      rw [ht]
      rw [ht] at hsum
      omega

private theorem weight_growth : StrictMono (U hm) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact lt_of_le_of_lt (scanner_bounds hm k).1 (scanner_bounds hm k).2

/-- Scan exactly count weights, from U(count-1) down through U(0). -/
def greedyScan : ℕ → ℕ → List ℕ
  | 0, _ => []
  | count + 1, r => r / U hm count :: greedyScan count (r % U hm count)

/-- The greatest fitting actual weight; the index bound makes the finite search exhaustive. -/
def topIndex (n : ℕ) : ℕ := Nat.findGreatest (fun j => U hm j ≤ n) n

/-- MSB-first full greedy expansion, retaining every digit down through U(0). -/
def fullGreedy (n : ℕ) : List ℕ :=
  if n = 0 then [] else greedyScan hm (topIndex hm n + 1) n

/-- A nonempty periodic prefix, retaining its last partial block. -/
def periodicDigits (k : ℕ) : List ℕ :=
  (List.range (k + 1)).map (fun i => if i % m = 0 then 1 else 0)

theorem scan_length (count r : ℕ) : (greedyScan hm count r).length = count := by
  induction count generalizing r with
  | zero => rfl
  | succ count ih => simp [greedyScan, ih]

private theorem scan_zero (count : ℕ) :
    greedyScan hm count 0 = List.replicate count 0 := by
  induction count with
  | zero => rfl
  | succ count ih => simp [greedyScan, ih, List.replicate_succ]

private theorem scan_zero_block (h z r : ℕ) (hr : r < U hm h) :
    greedyScan hm (h + z) r = List.replicate z 0 ++ greedyScan hm h r := by
  induction z with
  | zero => simp
  | succ z ih =>
      have hu : U hm h ≤ U hm (h + z) := (weight_growth hm).monotone (by omega)
      have ht : r < U hm (h + z) := lt_of_lt_of_le hr hu
      rw [show h + (z + 1) = (h + z) + 1 by omega, greedyScan,
        Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, ih]
      simp [List.replicate_succ]

theorem sentinel_top (k : ℕ) : topIndex hm (S hm k) = k := by
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨?_, fun _ => (scanner_bounds hm k).1, ?_⟩
  · have hb : k + 1 ≤ U hm k := by
      simpa only [show U hm 0 = 1 by simp [U, image], Nat.add_zero] using
        (weight_growth hm).add_le_nat k 0
    have hs := (scanner_bounds hm k).1
    omega
  · intro j hj _
    have hu : U hm (k + 1) ≤ U hm j := (weight_growth hm).monotone (by omega)
    have hs := (scanner_bounds hm k).2
    omega

private theorem scanner_top (k : ℕ) :
    S hm k / U hm k = 1 ∧
      S hm k % U hm k = if k < m then 0 else S hm (k - m) := by
  have hlo := (scanner_bounds hm k).1
  have hlt : S hm k < 2 * U hm k := by
    by_cases hk : k < m
    · rw [sentinel_recurrence hm k, if_pos hk]
      have hp : 0 < U hm k := by
        rw [weights_dbonacci hm]
        exact D5.S0.Tower.DBonacci.Values.dbonacci_level_pos m k (by omega)
      omega
    · rw [sentinel_recurrence hm k, if_neg hk]
      have hs := (scanner_bounds hm (k - m)).2
      have hu : U hm (k - m + 1) ≤ U hm k :=
        (weight_growth hm).monotone (by omega)
      omega
  have hq : S hm k / U hm k = 1 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  refine ⟨hq, ?_⟩
  have hrem := Nat.div_add_mod (S hm k) (U hm k)
  rw [hq, Nat.mul_one] at hrem
  by_cases hk : k < m
  · rw [if_pos hk]
    have hs : S hm k = U hm k := by simpa [hk] using sentinel_recurrence hm k
    omega
  · rw [if_neg hk]
    have hs : S hm k = U hm k + S hm (k - m) := by
      simpa [hk] using sentinel_recurrence hm k
    omega

private theorem short_period (k : ℕ) (hk : k < m) :
    periodicDigits (m := m) k = 1 :: List.replicate k 0 := by
  unfold periodicDigits
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.zero_mod, ↓reduceIte]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply,
      List.getElem_replicate]
    have hi : i + 1 < m := by omega
    rw [Nat.mod_eq_of_lt hi, if_neg (by omega)]

include hm in
private theorem long_period (k : ℕ) (hk : m ≤ k) :
    periodicDigits (m := m) k =
      1 :: List.replicate (m - 1) 0 ++ periodicDigits (m := m) (k - m) := by
  have hmpos : 0 < m := by omega
  have he : k + 1 = m + (k - m + 1) := by omega
  have hshort := short_period (m := m) (m - 1) (by omega)
  unfold periodicDigits at *
  rw [he, List.range_add, List.map_append, List.map_map]
  have hm1 : m - 1 + 1 = m := by omega
  rw [hm1] at hshort
  rw [hshort]
  congr 1
  apply List.map_congr_left
  intro i _
  simp

theorem scan_sentinel (k : ℕ) :
    greedyScan hm (k + 1) (S hm k) = periodicDigits (m := m) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rw [greedyScan, (scanner_top hm k).1, (scanner_top hm k).2]
      by_cases hk : k < m
      · rw [if_pos hk, scan_zero, short_period k hk]
      · rw [if_neg hk, long_period hm k (by omega)]
        have he : k = (k - m + 1) + (m - 1) := by omega
        have hb := scan_zero_block hm (k - m + 1) (m - 1) (S hm (k - m))
          (scanner_bounds hm (k - m)).2
        rw [← he, ih (k - m) (by omega)] at hb
        rw [hb]
        rfl

/-- Minimum complete all-start Parikh cardinality forces a full periodic greedy prefix. -/
theorem minimal_abelian_complexity_greedy (h5 : 5 ≤ m) (n : ℕ) (hn : 1 ≤ n)
    (hc : (parikhImage hm n).ncard = m) :
    ∃ k : ℕ, n = S hm k ∧ topIndex hm n = k ∧
      fullGreedy hm n = periodicDigits (m := m) k ∧
      (fullGreedy hm n).length = k + 1 ∧
      (fullGreedy hm n).head? = some 1 := by
  obtain ⟨k, hk⟩ := minimal_abelian_complexity_length hm (by omega) n hn hc
  rw [sentinel_sum hm k] at hk
  refine ⟨k, hk, ?_, ?_, ?_, ?_⟩
  · rw [hk]; exact sentinel_top hm k
  · rw [hk, fullGreedy, if_neg (by unfold S; omega), sentinel_top]
    exact scan_sentinel hm k
  · rw [hk, fullGreedy, if_neg (by unfold S; omega), sentinel_top, scan_length]
  · rw [hk, fullGreedy, if_neg (by unfold S; omega), sentinel_top, greedyScan,
      (scanner_top hm k).1]
    rfl

end D5.S1.Words.MBonacciMinimumGreedy
