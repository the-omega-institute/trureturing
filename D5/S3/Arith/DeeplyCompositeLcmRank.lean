/- GID: D5/S3/Arith/DeeplyCompositeLcmRank
   generality: I
   mirror-B: D5/B/S3/Arith/DeeplyCompositeLcmRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Deeply composite numbers contain the lcm prefix forced by their square-root rank. -/

import Mathlib.NumberTheory.Chebyshev
import D5.S3.Factorization.DeeplyCompositeNotPrimeExponentRecord

open Finset
open D5.S3.Factorization.DeeplyCompositeNotPrimeExponentRecord

namespace D5.S3.Arith.DeeplyCompositeLcmRank

noncomputable section

private noncomputable instance divPlusPrecedesDecidable (n m : ℕ) :
    Decidable (DivPlusPrecedes n m) := Classical.propDecidable _

private noncomputable instance dcDecidable (n : ℕ) : Decidable (DC n) :=
  Classical.propDecidable _

/-- The number of deeply composite numbers not exceeding `n`. -/
def rank (n : ℕ) : ℕ :=
  ((Finset.Iic n).filter DC).card

/-- Definitional cardinality form of the rank count. -/
theorem rank_eq_card_filter_le (n : ℕ) :
    rank n = ((Finset.Iic n).filter DC).card := rfl

/-- Convenience form restricting the rank count to the positive interval
from `1` through `n`. -/
theorem rank_eq_card_filter_Icc (n : ℕ) :
    rank n = ((Finset.Icc 1 n).filter DC).card := by
  unfold rank
  apply congrArg Finset.card
  ext m
  simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Icc]
  constructor
  · rintro ⟨hmle, hmDC⟩
    exact ⟨⟨hmDC.1, hmle⟩, hmDC⟩
  · rintro ⟨⟨_hmpos, hmle⟩, hmDC⟩
    exact ⟨hmle, hmDC⟩

/-- The zero-indexed enumeration of deeply composite numbers, corresponding
to OEIS A095848. -/
noncomputable def a (r : ℕ) : ℕ :=
  Nat.nth DC r

/-- The least common multiple of `1, ..., k`, OEIS A003418. -/
abbrev L (k : ℕ) : ℕ := Nat.lcmUpto k

/-- The deeply composite numbers strictly below the lcm prefix `L k`. -/
def recordsBelowL (k : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (L k)).filter DC

/-- The deeply composite numbers in the half-open lcm band from `L k` to
`L (k + 1)`. -/
def recordBand (k : ℕ) : Finset ℕ :=
  (Finset.Ico (L k) (L (k + 1))).filter DC

private theorem dvd_L {d k : ℕ} (hd : 1 ≤ d) (hdk : d ≤ k) : d ∣ L k := by
  unfold L Nat.lcmUpto
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hd, hdk⟩)

private theorem L_succ (k : ℕ) : L (k + 1) = Nat.lcm (L k) (k + 1) := by
  unfold L Nat.lcmUpto
  have hi : insert (k + 1) (Finset.Icc 1 k) = Finset.Icc 1 (k + 1) := by
    simpa only [Nat.succ_eq_succ, Nat.succ_eq_add_one] using
      (Finset.insert_Icc_right_eq_Icc_succ (α := ℕ) (a := 1) (b := k)
        (by simpa only [Nat.succ_eq_succ] using Nat.succ_le_succ (Nat.zero_le k)))
  rw [← hi, Finset.lcm_insert,
    lcm_comm, lcm_eq_nat_lcm]
  rfl

private theorem L_dvd_succ (k : ℕ) : L k ∣ L (k + 1) := by
  rw [L_succ]
  exact Nat.dvd_lcm_left _ _

private theorem L_mono_succ (k : ℕ) : L k ≤ L (k + 1) :=
  Nat.le_of_dvd (Nat.lcmUpto_pos _) (L_dvd_succ k)

/-- The next lcm prefix is at most the current prefix times its new endpoint. -/
theorem L_succ_le_mul (k : ℕ) : L (k + 1) ≤ L k * (k + 1) := by
  rw [L_succ]
  exact Nat.le_of_dvd
    (Nat.mul_pos (Nat.lcmUpto_pos k) (Nat.succ_pos k))
    (Nat.lcm_dvd_mul _ _)

/-- Prefix locking: once a deeply composite number reaches `L j`, it is
divisible by every integer through `j`, hence by `L j`. -/
theorem prefix_locking {n j : ℕ} (hn : DC n) (hjn : L j ≤ n) : L j ∣ n := by
  by_contra hnot
  have hlt : L j < n := lt_of_le_of_ne hjn (fun h => hnot (h ▸ dvd_rfl))
  have hnot' : ¬ ∀ d ∈ Finset.Icc 1 j, d ∣ n := by
    intro hall
    apply hnot
    unfold L Nat.lcmUpto
    exact Finset.lcm_dvd hall
  obtain ⟨d, hd⟩ := Classical.not_forall.mp hnot'
  obtain ⟨hdmem, hdn⟩ := Classical.not_imp.mp hd
  have hd_bounds : 1 ≤ d ∧ d ≤ j := Finset.mem_Icc.mp hdmem
  have hprec := hn.2 (L j) (Nat.lcmUpto_pos j) hlt
  obtain ⟨t, htpos, _htn, htL, hfirst⟩ := hprec
  have hjt : j < t := by
    by_contra h
    exact htL (dvd_L htpos (le_of_not_gt h))
  have hdL : d ∣ L j := dvd_L hd_bounds.1 hd_bounds.2
  exact hdn ((hfirst d hd_bounds.1 (hd_bounds.2.trans_lt hjt)).mpr hdL)

private theorem L_deeply_composite (k : ℕ) : DC (L k) := by
  refine ⟨Nat.lcmUpto_pos k, ?_⟩
  intro m hmpos hmlt
  have hex : ∃ d : ℕ, 1 ≤ d ∧ d ≤ k ∧ ¬ d ∣ m := by
    by_contra h
    push_neg at h
    have hLm : L k ∣ m := by
      unfold L Nat.lcmUpto
      exact Finset.lcm_dvd fun d hd => h d (Finset.mem_Icc.mp hd).1
        (Finset.mem_Icc.mp hd).2
    exact (not_le_of_gt hmlt) (Nat.le_of_dvd hmpos hLm)
  let d := Nat.find hex
  have hd : 1 ≤ d ∧ d ≤ k ∧ ¬ d ∣ m := Nat.find_spec hex
  refine ⟨d, hd.1, dvd_L hd.1 hd.2.1, hd.2.2, ?_⟩
  intro e hepos hed
  have hek : e ≤ k := (le_of_lt hed).trans hd.2.1
  have heL : e ∣ L k := dvd_L hepos hek
  constructor
  · intro _heL
    by_contra hem
    have hde : d ≤ e := Nat.find_min' hex ⟨hepos, hek, hem⟩
    omega
  · intro _hem
    exact heL

private theorem dc_infinite : Set.Infinite {n : ℕ | DC n} := by
  apply Set.infinite_of_forall_exists_gt
  intro bound
  refine ⟨L (bound + 1), L_deeply_composite _, ?_⟩
  have hdvd : bound + 1 ∣ L (bound + 1) :=
    dvd_L (Nat.succ_pos bound) le_rfl
  have hle : bound + 1 ≤ L (bound + 1) :=
    Nat.le_of_dvd (Nat.lcmUpto_pos _) hdvd
  omega

private theorem recordBand_card_le (k : ℕ) : (recordBand k).card ≤ k := by
  have hmap : Set.MapsTo (fun d : ℕ => d / L k)
      (recordBand k : Set ℕ) (Finset.Ico 1 (k + 1) : Set ℕ) := by
    intro d hd
    change d ∈ recordBand k at hd
    change d / L k ∈ Finset.Ico 1 (k + 1)
    simp only [recordBand, Finset.mem_filter, Finset.mem_Ico] at hd
    rw [Finset.mem_Ico]
    have hdvd : L k ∣ d := prefix_locking hd.2 hd.1.1
    constructor
    · exact Nat.div_pos hd.1.1 (Nat.lcmUpto_pos k)
    · apply (Nat.div_lt_iff_lt_mul (Nat.lcmUpto_pos k)).mpr
      calc
        d < L (k + 1) := hd.1.2
        _ ≤ L k * (k + 1) := L_succ_le_mul k
        _ = (k + 1) * L k := Nat.mul_comm _ _
  have hinj : Set.InjOn (fun d : ℕ => d / L k) (recordBand k : Set ℕ) := by
    intro a ha b hb hab
    change a / L k = b / L k at hab
    change a ∈ recordBand k at ha
    change b ∈ recordBand k at hb
    simp only [recordBand, Finset.mem_filter, Finset.mem_Ico] at ha hb
    have ha_dvd : L k ∣ a := prefix_locking ha.2 ha.1.1
    have hb_dvd : L k ∣ b := prefix_locking hb.2 hb.1.1
    calc
      a = a / L k * L k := (Nat.div_mul_cancel ha_dvd).symm
      _ = b / L k * L k := congrArg (fun q => q * L k) hab
      _ = b := Nat.div_mul_cancel hb_dvd
  calc
    (recordBand k).card ≤ (Finset.Ico 1 (k + 1)).card :=
      Finset.card_le_card_of_injOn _ hmap hinj
    _ = k := by simp

private theorem recordsBelowL_succ (k : ℕ) :
    recordsBelowL (k + 1) = recordsBelowL k ∪ recordBand k := by
  have hmono := L_mono_succ k
  rw [recordsBelowL, recordsBelowL, recordBand, ← Finset.filter_union]
  rw [Finset.Ico_union_Ico_eq_Ico (Nat.lcmUpto_pos k) hmono]

private theorem counting_bound_sum (k : ℕ) :
    (recordsBelowL k).card ≤ ∑ j ∈ Finset.range k, j := by
  induction k with
  | zero => simp [recordsBelowL, L, Nat.lcmUpto]
  | succ k ih =>
      rw [recordsBelowL_succ]
      calc
        (recordsBelowL k ∪ recordBand k).card ≤
            (recordsBelowL k).card + (recordBand k).card := Finset.card_union_le _ _
        _ ≤ (∑ j ∈ Finset.range k, j) + k :=
          Nat.add_le_add ih (recordBand_card_le k)
        _ = ∑ j ∈ Finset.range (k + 1), j := by
          rw [Finset.sum_range_succ]

/-- Counting bound: below `L k` there are at most `k * (k - 1) / 2`
deeply composite numbers. -/
theorem counting_bound (k : ℕ) :
    ((Finset.Ico 1 (L k)).filter DC).card ≤ k * (k - 1) / 2 := by
  simpa only [recordsBelowL, Finset.sum_range_id] using counting_bound_sum k

/-- A deeply composite number has positive rank. -/
theorem rank_pos {n : ℕ} (hn : DC n) : 0 < rank n := by
  rw [rank_eq_card_filter_Icc]
  apply Finset.card_pos.mpr
  refine ⟨n, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hn.1, le_rfl⟩, hn⟩

private theorem rank_le_recordsBelowL {n k : ℕ} (hn : n < L k) :
    rank n ≤ (recordsBelowL k).card := by
  rw [rank_eq_card_filter_Icc]
  apply Finset.card_le_card
  intro d hd
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd
  simp only [recordsBelowL, Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨hd.1.1, hd.1.2.trans_lt hn⟩, hd.2⟩

/-- Switkay's square-root-rank lcm divisibility conjecture for deeply
composite numbers (OEIS A095848, comment 2025-09-07). -/
theorem deeply_composite_lcm_sqrt_rank {n : ℕ} (hn : DC n) :
    L (Nat.sqrt (2 * rank n)) ∣ n := by
  let r := rank n
  let k := Nat.sqrt (2 * r)
  by_contra hnot
  have hnlt : n < L k := by
    exact lt_of_not_ge (fun hkn => hnot (prefix_locking hn hkn))
  have hrle : r ≤ (recordsBelowL k).card := rank_le_recordsBelowL hnlt
  have hrhalf : r ≤ k * (k - 1) / 2 := hrle.trans (counting_bound k)
  have htwor : r * 2 ≤ k * (k - 1) :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hrhalf
  have hrpos : 0 < r := rank_pos hn
  have hkpos : 0 < k := Nat.sqrt_pos.mpr (Nat.mul_pos (by decide) hrpos)
  have hstrict : k * (k - 1) < k * k :=
    (Nat.mul_lt_mul_left hkpos).mpr (by omega)
  have hsq : k * k ≤ 2 * r := Nat.sqrt_le _
  have htwor' : 2 * r ≤ k * (k - 1) := by simpa [Nat.mul_comm] using htwor
  have : 2 * r < k * k := htwor'.trans_lt hstrict
  exact (not_lt_of_ge hsq) this

/-- Every term of the zero-indexed enumeration is deeply composite. -/
theorem dc_nth (r : ℕ) : DC (a r) := by
  exact Nat.nth_mem_of_infinite dc_infinite r

/-- The zero-indexed term `a r` has one-indexed deeply composite rank `r + 1`. -/
theorem rank_nth (r : ℕ) : rank (a r) = r + 1 := by
  calc
    rank (a r) = ((Finset.Iic (a r)).filter DC).card := rank_eq_card_filter_le _
    _ = ((Finset.range (a r + 1)).filter DC).card := by
      rw [Nat.range_succ_eq_Iic]
    _ = Nat.count DC (a r + 1) := (Nat.count_eq_card_filter_range DC _).symm
    _ = r + 1 := by
      simpa only [a] using Nat.count_nth_succ_of_infinite dc_infinite r

/-- The sequence-indexed form of Switkay's square-root-rank lcm divisibility
conjecture from OEIS A095848. -/
theorem oeis_a095848_lcm_sqrt_rank (r : ℕ) :
    L (Nat.sqrt (2 * (r + 1))) ∣ a r := by
  simpa only [rank_nth] using deeply_composite_lcm_sqrt_rank (dc_nth r)

example : ℕ := 12

example : DC 12 := by
  refine ⟨by norm_num, ?_⟩
  intro m hm hlt
  interval_cases m
  · refine ⟨2, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e
    norm_num at *
  · refine ⟨3, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e <;> norm_num at *
  · refine ⟨2, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e
    norm_num at *
  · refine ⟨3, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e <;> norm_num at *
  · refine ⟨2, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e
    norm_num at *
  · refine ⟨4, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e <;> norm_num at *
  · refine ⟨2, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e
    norm_num at *
  · refine ⟨3, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e <;> norm_num at *
  · refine ⟨2, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e
    norm_num at *
  · refine ⟨3, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e <;> norm_num at *
  · refine ⟨2, by norm_num, by norm_num, by norm_num, fun e hepos helt => ?_⟩
    interval_cases e
    norm_num at *

example : ¬ DC 8 := by
  intro h
  obtain ⟨d, hdpos, hdvd, hndvd, hfirst⟩ := h.2 6 (by norm_num) (by norm_num)
  have hthree : 3 < d := by
    by_contra h
    have hdle : d ≤ 3 := le_of_not_gt h
    interval_cases d <;> norm_num at *
  have hbad := (hfirst 3 (by norm_num) hthree).mpr (by norm_num : 3 ∣ 6)
  norm_num at hbad

#print axioms L_succ_le_mul
#print axioms prefix_locking
#print axioms counting_bound
#print axioms rank_pos
#print axioms rank_eq_card_filter_le
#print axioms rank_eq_card_filter_Icc
#print axioms deeply_composite_lcm_sqrt_rank
#print axioms dc_nth
#print axioms rank_nth
#print axioms oeis_a095848_lcm_sqrt_rank

end

end D5.S3.Arith.DeeplyCompositeLcmRank
