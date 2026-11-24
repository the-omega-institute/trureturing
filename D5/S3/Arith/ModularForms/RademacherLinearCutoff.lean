/- GID: D5/S3/Arith/ModularForms/RademacherLinearCutoff
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/RademacherLinearCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent, mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: Quantitative comparison of the strict rectangular linear cutoff with symmetric cotangent partial fractions. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open Finset Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.ModularForms.RademacherLinearCutoff

noncomputable section

/-- The symmetric partial sum includes both endpoints and the central term. -/
def symmetricSum (u : ℂ) (m : ℕ) : ℂ :=
  ∑ k ∈ Icc (-(m : ℤ)) (m : ℤ), 1 / (u + (k : ℂ))

theorem symmetricSum_eq_pairs (u : ℂ) (m : ℕ) :
    symmetricSum u m = 1 / u + ∑ j ∈ range m, cotTerm u j := by
  induction m with
  | zero => simp [symmetricSum]
  | succ m ih =>
    have hI : Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) =
        insert (-((m + 1 : ℕ) : ℤ))
          (insert ((m + 1 : ℕ) : ℤ) (Icc (-(m : ℤ)) (m : ℤ))) := by
      ext k
      simp only [mem_Icc, mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    have hneg : (-((m + 1 : ℕ) : ℤ)) ∉
        insert ((m + 1 : ℕ) : ℤ) (Icc (-(m : ℤ)) (m : ℤ)) := by
      simp only [mem_Icc, mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    have hpos : ((m + 1 : ℕ) : ℤ) ∉ Icc (-(m : ℤ)) (m : ℤ) := by
      simp only [mem_Icc, Nat.cast_add, Nat.cast_one]
      omega
    change symmetricSum u (m + 1) = 1 / u + ∑ j ∈ range (m + 1), cotTerm u j
    unfold symmetricSum
    rw [hI, sum_insert hneg, sum_insert hpos, sum_range_succ]
    rw [← symmetricSum, ih]
    have hcast : (((m + 1 : ℕ) : ℤ) : ℂ) = (m : ℂ) + 1 := by simp
    simp only [Int.cast_neg, hcast, cotTerm, sub_eq_add_neg]
    abel

/-- Pairing at finite radius leads to the cotangent principal value. -/
theorem tendsto_symmetricSum (u : ℂ) (hu : 0 < u.im) :
    Tendsto (symmetricSum u) atTop (𝓝 ((Real.pi : ℂ) * Complex.cot (Real.pi * u))) := by
  have hz : u ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨u, hu⟩
  have h := (tendsto_logDeriv_euler_cot_sub hz).const_add (1 / u)
  have hvalue : 1 / u + ((Real.pi : ℂ) * Complex.cot (Real.pi * u) - 1 / u) =
      (Real.pi : ℂ) * Complex.cot (Real.pi * u) := by ring
  rw [hvalue] at h
  exact h.congr fun m ↦ (symmetricSum_eq_pairs u m).symm

theorem reciprocal_pair (u a : ℂ) (hadd : u + a ≠ 0) (hsub : u - a ≠ 0) :
    1 / (u + a) + 1 / (u - a) = 2 * u / (u ^ 2 - a ^ 2) := by
  rw [show u ^ 2 - a ^ 2 = (u + a) * (u - a) by ring]
  field_simp [hadd, hsub]
  ring

private theorem half_le_norm_add {u z : ℂ} {B t : ℝ} (hu : ‖u‖ ≤ B)
    (ht : 2 * B ≤ t) (hz : t ≤ ‖z‖) : t / 2 ≤ ‖u + z‖ := by
  have h := norm_sub_norm_le z (-u)
  rw [norm_neg, sub_neg_eq_add, add_comm z u] at h
  linarith only [h, hu, ht, hz]

private theorem norm_reciprocal_le {u z : ℂ} {B t : ℝ} (hu : ‖u‖ ≤ B)
    (ht : 2 * B ≤ t) (htpos : 0 < t) (hz : t ≤ ‖z‖) :
    ‖1 / (u + z)‖ ≤ 2 / t := by
  have hd := half_le_norm_add hu ht hz
  have ht' : 0 < t / 2 := by positivity
  rw [norm_div, norm_one]
  calc
    1 / ‖u + z‖ ≤ 1 / (t / 2) := div_le_div_of_nonneg_left zero_le_one ht' hd
    _ = 2 / t := by field_simp [htpos.ne']

theorem norm_cotTerm_le {u : ℂ} {B : ℝ} (hu : ‖u‖ ≤ B) (j : ℕ)
    (hj : 2 * B ≤ (j : ℝ) + 1) :
    ‖cotTerm u j‖ ≤ 8 * B / ((j : ℝ) + 1) ^ 2 := by
  let a : ℂ := (j : ℂ) + 1
  let t : ℝ := (j : ℝ) + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hnorm : ‖a‖ = t := by
    change ‖(j : ℂ) + 1‖ = (j : ℝ) + 1
    rw [← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ]
  have hd₁ : t / 2 ≤ ‖u + a‖ := half_le_norm_add hu hj hnorm.ge
  have hd₂ : t / 2 ≤ ‖u - a‖ := by
    simpa only [sub_eq_add_neg] using
      (half_le_norm_add (z := -a) hu hj (by simpa only [norm_neg] using hnorm.ge))
  have ht' : 0 < t / 2 := by positivity
  have h₁ := norm_pos_iff.mp (ht'.trans_le hd₁)
  have h₂ := norm_pos_iff.mp (ht'.trans_le hd₂)
  have hdenom : (t / 2) ^ 2 ≤ ‖u + a‖ * ‖u - a‖ := by
    rw [pow_two]
    exact mul_le_mul hd₁ hd₂ ht'.le (norm_nonneg _)
  change ‖1 / (u - a) + 1 / (u + a)‖ ≤ 8 * B / t ^ 2
  rw [add_comm (1 / (u - a)) (1 / (u + a)), reciprocal_pair u a h₁ h₂,
    show u ^ 2 - a ^ 2 = (u + a) * (u - a) by ring]
  simp only [norm_div, norm_mul, Complex.norm_two]
  calc
    2 * ‖u‖ / (‖u + a‖ * ‖u - a‖) ≤
        2 * ‖u‖ / (t / 2) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom
    _ ≤ 2 * B / (t / 2) ^ 2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by norm_num)) (by positivity)
    _ = 8 * B / t ^ 2 := by
      field_simp [ht.ne']
      ring

/-- The sum of the norms of the paired tail is bounded by a telescoping majorant. -/
theorem paired_tail_norm_le {u : ℂ} {B : ℝ} (hu : ‖u‖ ≤ B) (huim : 0 < u.im)
    (m : ℕ) (hm : 2 * B ≤ (m : ℝ) + 1) :
    (∑' j : ℕ, ‖cotTerm u (j + m)‖) ≤ 16 * B / ((m : ℝ) + 1) := by
  have hz : u ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨u, huim⟩
  have hb : 0 ≤ B := (norm_nonneg _).trans hu
  have hs : Summable (fun j : ℕ ↦ ‖cotTerm u (j + m)‖) :=
    (summable_nat_add_iff m).2 (summable_cotTerm hz).norm
  let f (j : ℕ) : ℝ := 16 * B / ((j : ℝ) + (m : ℝ) + 1)
  have hmajorant (j : ℕ) : ‖cotTerm u (j + m)‖ ≤ f j - f (j + 1) := by
    let t : ℝ := (j : ℝ) + (m : ℝ) + 1
    have ht : 0 < t := by dsimp [t]; positivity
    have ht₁ : 0 ≤ t - 1 := by
      dsimp [t]
      linarith [Nat.cast_nonneg (α := ℝ) j, Nat.cast_nonneg (α := ℝ) m]
    have htB : 2 * B ≤ ((j + m : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_add]
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have hterm := norm_cotTerm_le hu (j + m) htB
    rw [Nat.cast_add] at hterm
    calc
      ‖cotTerm u (j + m)‖ ≤ 8 * B / t ^ 2 := hterm
      _ ≤ 16 * B / (t * (t + 1)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith only [mul_nonneg hb (mul_nonneg ht.le ht₁)]
      _ = f j - f (j + 1) := by
        have hf : f j = 16 * B / t := rfl
        have hf' : f (j + 1) = 16 * B / (t + 1) := by
          simp only [f, t, Nat.cast_add, Nat.cast_one]
          congr 1
          ring
        rw [hf, hf']
        field_simp [ht.ne', (show 0 < t + 1 by positivity).ne']
        ring
  apply le_of_tendsto' hs.hasSum.tendsto_sum_nat
  intro n
  calc
    (∑ j ∈ range n, ‖cotTerm u (j + m)‖) ≤
        ∑ j ∈ range n, (f j - f (j + 1)) := sum_le_sum (fun j _ ↦ hmajorant j)
    _ = f 0 - f n := sum_range_sub' f n
    _ ≤ 16 * B / ((m : ℝ) + 1) := by
      have hf : 0 ≤ f n := by dsimp [f]; positivity
      simpa [f, zero_add] using sub_le_self (f 0) hf

theorem symmetricSum_error_le {u : ℂ} {B : ℝ} (hu : ‖u‖ ≤ B) (huim : 0 < u.im)
    (m : ℕ) (hm : 2 * B ≤ (m : ℝ) + 1) :
    ‖symmetricSum u m - (Real.pi : ℂ) * Complex.cot (Real.pi * u)‖ ≤
      16 * B / ((m : ℝ) + 1) := by
  have hz : u ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨u, huim⟩
  have hs := summable_cotTerm hz
  have htail : Summable (fun j : ℕ ↦ cotTerm u (j + m)) := (summable_nat_add_iff m).2 hs
  have hsplit := hs.sum_add_tsum_nat_add m
  rw [← cot_series_rep' hz] at hsplit
  have herr : symmetricSum u m - (Real.pi : ℂ) * Complex.cot (Real.pi * u) =
      -(∑' j : ℕ, cotTerm u (j + m)) := by
    rw [symmetricSum_eq_pairs]
    linear_combination hsplit
  rw [herr, norm_neg]
  exact (norm_tsum_le_tsum_norm htail.norm).trans (paired_tail_norm_le hu huim m hm)

/-- The strict condition is evaluated on the integer `d = r + c * k`. -/
def strictShifts (M c r : ℤ) : Finset ℤ :=
  (Icc (-(M / c + 1)) (M / c)).filter (fun k ↦ -M < r + c * k ∧ r + c * k < M)

private theorem division_bounds (M c : ℤ) (hc : 0 < c) :
    c * (M / c) ≤ M ∧ M < c * (M / c + 1) := by
  have h := Int.emod_add_mul_ediv M c
  have h₀ := Int.emod_nonneg M hc.ne'
  have h₁ := Int.emod_lt_of_pos M hc
  constructor
  · linarith only [h, h₀]
  · nlinarith only [h, h₁]

theorem mem_strictShifts_iff {M c r k : ℤ} (hc : 0 < c) (hr₀ : 0 ≤ r) (hrc : r < c) :
    k ∈ strictShifts M c r ↔ -M < r + c * k ∧ r + c * k < M := by
  simp only [strictShifts, mem_filter, mem_Icc]
  refine ⟨And.right, ?_⟩
  intro hk
  refine ⟨?_, hk⟩
  have hdiv := (division_bounds M c hc).2
  constructor
  · by_contra! hn
    have hm := mul_le_mul_of_nonneg_left (show k ≤ -(M / c + 2) by omega) hc.le
    nlinarith only [hm, hk.1, hdiv, hrc]
  · by_contra! hn
    have hm := mul_le_mul_of_nonneg_left (show M / c + 1 ≤ k by omega) hc.le
    linarith only [hm, hk.2, hdiv, hr₀]

private theorem strictShifts_contains_Ioo {M c r : ℤ} (hc : 0 < c)
    (hr₀ : 0 ≤ r) (hrc : r < c) :
    Ioo (-(M / c)) (M / c) ⊆ strictShifts M c r := by
  intro k hk
  rw [mem_Ioo] at hk
  rw [mem_strictShifts_iff hc hr₀ hrc]
  have hlo := mul_le_mul_of_nonneg_left (show -(M / c) + 1 ≤ k by omega) hc.le
  have hhi := mul_le_mul_of_nonneg_left (show k ≤ M / c - 1 by omega) hc.le
  have hdiv := (division_bounds M c hc).1
  constructor
  · nlinarith only [hlo, hdiv, hr₀, hc]
  · nlinarith only [hhi, hdiv, hrc]

/-- For fixed `c,r`, only the endpoints contribute to the cutoff error beyond the paired tail. -/
theorem strictShifts_error_le {M c r : ℤ} {q : ℕ} {u : ℂ} {B : ℝ}
    (hc : 0 < c) (hr₀ : 0 ≤ r) (hrc : r < c) (hq : M / c = (q : ℤ))
    (hqpos : 0 < q) (hu : ‖u‖ ≤ B) (huim : 0 < u.im) (hqB : 2 * B ≤ (q : ℝ)) :
    ‖(∑ k ∈ strictShifts M c r, 1 / (u + (k : ℂ))) -
      (Real.pi : ℂ) * Complex.cot (Real.pi * u)‖ ≤ (16 * B + 4) / (q : ℝ) := by
  classical
  let K := strictShifts M c r
  let S := Icc (-(q : ℤ)) (q : ℤ)
  let A := K \ S
  let O := S \ K
  let f (k : ℤ) : ℂ := 1 / (u + (k : ℂ))
  have hcore : Ioo (-(q : ℤ)) (q : ℤ) ⊆ K := by
    simpa only [hq] using strictShifts_contains_Ioo (M := M) hc hr₀ hrc
  have houter : K ⊆ Icc (-((q : ℤ) + 1)) (q : ℤ) := by
    intro k hk
    have h : k ∈ Icc (-(M / c + 1)) (M / c) := (mem_filter.mp hk).1
    simpa only [hq] using h
  have ha : A ⊆ { -((q : ℤ) + 1) } := by
    intro k hk
    obtain ⟨hkK, hkS⟩ := mem_sdiff.mp hk
    have hk' := mem_Icc.mp (houter hkK)
    change k ∉ Icc (-(q : ℤ)) (q : ℤ) at hkS
    simp only [mem_Icc] at hkS
    rw [mem_singleton]
    omega
  have ho : O ⊆ { -(q : ℤ), (q : ℤ) } := by
    intro k hk
    obtain ⟨hkS, hkK⟩ := mem_sdiff.mp hk
    have hk' := mem_Icc.mp hkS
    have hn : k ∉ Ioo (-(q : ℤ)) (q : ℤ) := fun h ↦ hkK (hcore h)
    simp only [mem_Ioo] at hn
    simp only [mem_insert, mem_singleton]
    omega
  have hadd (h : -((q : ℤ) + 1) ∈ K) : -(q : ℤ) ∈ K := by
    have h := (mem_strictShifts_iff hc hr₀ hrc).1 h
    have hmul : c * (q : ℤ) ≤ M := by simpa only [hq] using (division_bounds M c hc).1
    have hmul' : 0 ≤ c * (q : ℤ) := mul_nonneg hc.le (by positivity)
    have hq₁ : (1 : ℤ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt hqpos
    have hcr : c ≤ c * (q : ℤ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hq₁ hc.le
    apply (mem_strictShifts_iff hc hr₀ hrc).2
    constructor
    · nlinarith only [h.1, hc]
    · nlinarith only [hrc, hmul, hmul', hcr]
  have hcard : A.card + O.card ≤ 2 := by
    by_cases h : -((q : ℤ) + 1) ∈ K
    · have hO : O ⊆ { (q : ℤ) } := by
        intro k hk
        have hk' := ho hk
        simp only [mem_insert, mem_singleton] at hk'
        rcases hk' with rfl | hk'
        · exact ((mem_sdiff.mp hk).2 (hadd h)).elim
        · simpa only [mem_singleton] using hk'
      have h₁ : A.card ≤ 1 := by simpa using card_le_card ha
      have h₂ : O.card ≤ 1 := by simpa using card_le_card hO
      omega
    · have hA : A = ∅ := by
        apply eq_empty_iff_forall_notMem.2
        intro k hk
        have hk' := mem_singleton.mp (ha hk)
        exact h (hk' ▸ (mem_sdiff.mp hk).1)
      have h₂ : O.card ≤ 2 := (card_le_card ho).trans (by
        by_cases he : -(q : ℤ) = (q : ℤ) <;> simp [he])
      simpa only [hA, card_empty, zero_add] using h₂
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hf (k : ℤ) (hk : k ∈ A ∨ k ∈ O) : ‖f k‖ ≤ 2 / (q : ℝ) := by
    apply norm_reciprocal_le hu hqB hqR
    rw [Complex.norm_intCast]
    rcases hk with hk | hk
    · rw [mem_singleton.mp (ha hk), Int.cast_neg, Int.cast_add, Int.cast_one, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ ((q : ℤ) : ℝ) + 1), Int.cast_natCast]
      linarith
    · have hk' := ho hk
      simp only [mem_insert, mem_singleton] at hk'
      rcases hk' with rfl | rfl <;> simp [abs_of_nonneg hqR.le]
  have hsum_bounds (T : Finset ℤ) (hT : T ⊆ A ∨ T ⊆ O) :
      ‖∑ k ∈ T, f k‖ ≤ (T.card : ℝ) * (2 / (q : ℝ)) := by
    calc
      ‖∑ k ∈ T, f k‖ ≤ ∑ k ∈ T, ‖f k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ T, 2 / (q : ℝ) := sum_le_sum (fun k hk ↦
        hf k (hT.imp (fun h ↦ h hk) (fun h ↦ h hk)))
      _ = (T.card : ℝ) * (2 / (q : ℝ)) := by simp [nsmul_eq_mul]
  have hsplitK := sum_sdiff (f := f) (s₁ := K ∩ S) (s₂ := K) inter_subset_left
  have hsplitS := sum_sdiff (f := f) (s₁ := K ∩ S) (s₂ := S) inter_subset_right
  have hA : K \ (K ∩ S) = A := by ext k; simp only [A, Finset.mem_sdiff, mem_inter]; tauto
  have hO : S \ (K ∩ S) = O := by ext k; simp only [O, Finset.mem_sdiff, mem_inter]; tauto
  rw [hA] at hsplitK
  rw [hO] at hsplitS
  have hdiff : (∑ k ∈ K, f k) - ∑ k ∈ S, f k =
      (∑ k ∈ A, f k) - ∑ k ∈ O, f k := by
    rw [← hsplitK, ← hsplitS]
    abel
  have hend : ‖(∑ k ∈ K, f k) - symmetricSum u q‖ ≤ 4 / (q : ℝ) := by
    change ‖(∑ k ∈ K, f k) - ∑ k ∈ S, f k‖ ≤ 4 / (q : ℝ)
    rw [hdiff]
    have hcardR : (A.card : ℝ) + (O.card : ℝ) ≤ 2 := by exact_mod_cast hcard
    calc
      ‖(∑ k ∈ A, f k) - ∑ k ∈ O, f k‖ ≤
          ‖∑ k ∈ A, f k‖ + ‖∑ k ∈ O, f k‖ := norm_sub_le _ _
      _ ≤ ((A.card : ℝ) + (O.card : ℝ)) * (2 / (q : ℝ)) := by
        rw [add_mul]
        exact add_le_add (hsum_bounds A (.inl (fun _ h ↦ h)))
          (hsum_bounds O (.inr (fun _ h ↦ h)))
      _ ≤ 2 * (2 / (q : ℝ)) := mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = 4 / (q : ℝ) := by ring
  have htail := symmetricSum_error_le hu huim q (by linarith : 2 * B ≤ (q : ℝ) + 1)
  let v := (Real.pi : ℂ) * Complex.cot (Real.pi * u)
  calc
    ‖(∑ k ∈ K, f k) - v‖ ≤
        ‖(∑ k ∈ K, f k) - symmetricSum u q‖ + ‖symmetricSum u q - v‖ := by
      simpa only [sub_add_sub_cancel] using
        (norm_add_le ((∑ k ∈ K, f k) - symmetricSum u q) (symmetricSum u q - v))
    _ ≤ 4 / (q : ℝ) + 16 * B / ((q : ℝ) + 1) := add_le_add hend htail
    _ ≤ 4 / (q : ℝ) + 16 * B / (q : ℝ) := by
      have hb : 0 ≤ B := (norm_nonneg u).trans hu
      exact add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity) hqR
        (le_add_of_nonneg_right zero_le_one))
    _ = (16 * B + 4) / (q : ℝ) := by ring

/-- The argument of the cotangent after reducing the denominator modulo `c`. -/
def shiftedArgument (τ : ℂ) (c r : ℤ) : ℂ := τ + (r : ℂ) / (c : ℂ)

private theorem shiftedArgument_bounds {τ : ℂ} {c r : ℤ} {B : ℝ}
    (hτ : ‖τ‖ ≤ B) (hτim : 0 < τ.im) (hc : 0 < c) (hr₀ : 0 ≤ r) (hrc : r < c) :
    ‖shiftedArgument τ c r‖ ≤ B + 1 ∧ 0 < (shiftedArgument τ c r).im := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hrR : 0 ≤ (r : ℝ) := by exact_mod_cast hr₀
  have hrcR : (r : ℝ) < (c : ℝ) := by exact_mod_cast hrc
  have hshift : (r : ℂ) / (c : ℂ) = Complex.ofReal ((r : ℝ) / (c : ℝ)) := by
    simp only [Complex.ofReal_div, Complex.ofReal_intCast]
  have hnorm : ‖(r : ℂ) / (c : ℂ)‖ ≤ 1 := by
    rw [hshift, Complex.norm_of_nonneg (div_nonneg hrR hcR.le)]
    exact (div_le_iff₀ hcR).2 (by simpa using hrcR.le)
  constructor
  · exact (norm_add_le _ _).trans (add_le_add hτ hnorm)
  · simpa only [shiftedArgument, hshift, Complex.add_im, Complex.ofReal_im, add_zero] using hτim

/-- Uniform constant for the unweighted strict rectangle comparison. -/
def comparisonConstant (B : ℝ) : ℝ := 32 * (B + 1) + 8

theorem rectangular_residue_error_le {N c : ℕ} {r : ℤ} {τ : ℂ} {B : ℝ}
    (hc : 0 < c) (hcN : c < N) (hr₀ : 0 ≤ r) (hrc : r < (c : ℤ))
    (hτ : ‖τ‖ ≤ B) (hτim : 0 < τ.im) (hN : 2 * (B + 1) ≤ (N : ℝ)) :
    ‖(∑ k ∈ strictShifts ((N : ℤ) ^ 2) (c : ℤ) r,
        1 / (shiftedArgument τ c r + (k : ℂ))) -
      (Real.pi : ℂ) * Complex.cot (Real.pi * shiftedArgument τ c r)‖ ≤
      comparisonConstant B * (c : ℝ) / (N : ℝ) ^ 2 := by
  let q := N ^ 2 / c
  have hcZ : 0 < (c : ℤ) := by exact_mod_cast hc
  have hq : (N : ℤ) ^ 2 / (c : ℤ) = (q : ℤ) := by
    simp only [q, Int.natCast_div, Nat.cast_pow]
  have hNq : N ≤ q := by
    apply (Nat.le_div_iff_mul_le hc).2
    simpa only [pow_two] using Nat.mul_le_mul_left N hcN.le
  have hNpos : 0 < N := hc.trans hcN
  have hqpos := hNpos.trans_le hNq
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt hqpos
  have hNqR : (N : ℝ) ≤ q := by exact_mod_cast hNq
  have hupper : (N : ℝ) ^ 2 < (c : ℝ) * ((q : ℝ) + 1) := by
    change (N : ℝ) ^ 2 < (c : ℝ) * (((N ^ 2 / c : ℕ) : ℝ) + 1)
    exact_mod_cast Nat.lt_mul_div_succ (N ^ 2) hc
  have hscale : (N : ℝ) ^ 2 ≤ 2 * (c : ℝ) * (q : ℝ) := by
    nlinarith only [hupper, mul_nonneg (Nat.cast_nonneg (α := ℝ) c) (sub_nonneg.mpr hq1)]
  have ⟨hu, huim⟩ := shiftedArgument_bounds hτ hτim hcZ hr₀ hrc
  refine (strictShifts_error_le hcZ hr₀ hrc hq hqpos hu huim (hN.trans hNqR)).trans ?_
  apply (div_le_div_iff₀ hqR (by positivity)).2
  have hb : 0 ≤ B := (norm_nonneg τ).trans hτ
  have hmul := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 16 * (B + 1) + 4 by positivity)
  unfold comparisonConstant
  nlinarith only [hmul]

def reducedResidues (c : ℤ) : Finset ℤ :=
  (Ico 0 c).filter (fun r ↦ r.gcd c = 1)

def strictDenominators (M c : ℤ) : Finset ℤ :=
  (Ioo (-M) M).filter (fun d ↦ d.gcd c = 1)

/-- The Euclidean division of each strict denominator gives a finite bijection. -/
theorem sum_strictDenominators_eq_residue_shifts {M c : ℤ} (hc : 0 < c) (f : ℤ → ℂ) :
    (∑ d ∈ strictDenominators M c, f d) =
      ∑ r ∈ reducedResidues c, ∑ k ∈ strictShifts M c r, f (r + c * k) := by
  rw [Finset.sum_sigma']
  let toPair (d : ℤ) : Σ _ : ℤ, ℤ := ⟨d % c, d / c⟩
  let toDenom (p : Σ _ : ℤ, ℤ) : ℤ := p.1 + c * p.2
  refine Finset.sum_nbij' toPair toDenom ?_ ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hdI, hdg⟩ := mem_filter.mp hd
    have hr₀ := Int.emod_nonneg d hc.ne'
    have hrc := Int.emod_lt_of_pos d hc
    apply mem_sigma.mpr
    change d % c ∈ reducedResidues c ∧ d / c ∈ strictShifts M c (d % c)
    refine ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨hr₀, hrc⟩, ?_⟩, ?_⟩
    · simpa only [Int.gcd_emod] using hdg
    · rw [mem_strictShifts_iff hc hr₀ hrc, Int.emod_add_mul_ediv]
      exact mem_Ioo.mp hdI
  · rintro ⟨r, k⟩ hp
    obtain ⟨hr, hk⟩ := mem_sigma.mp hp
    obtain ⟨hrI, hrg⟩ := mem_filter.mp hr
    obtain ⟨hr₀, hrc⟩ := mem_Ico.mp hrI
    have hdiv : (r + c * k) % c = r := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr₀ hrc]
    apply mem_filter.mpr
    change r + c * k ∈ Ioo (-M) M ∧ (r + c * k).gcd c = 1
    refine ⟨mem_Ioo.mpr ((mem_strictShifts_iff hc hr₀ hrc).1 hk), ?_⟩
    rw [← Int.gcd_emod, hdiv]
    exact hrg
  · intro d _
    exact Int.emod_add_mul_ediv d c
  · rintro ⟨r, k⟩ hp
    obtain ⟨hr, _⟩ := mem_sigma.mp hp
    obtain ⟨hr₀, hrc⟩ := mem_Ico.mp (mem_filter.mp hr).1
    have hdiv : (r + c * k) / c = k ∧ (r + c * k) % c = r :=
      (Int.ediv_emod_unique'' hc.ne').2 ⟨rfl, hr₀, by simpa [abs_of_pos hc] using hrc⟩
    change (⟨(r + c * k) % c, (r + c * k) / c⟩ : Σ _ : ℤ, ℤ) = ⟨r, k⟩
    rw [hdiv.1, hdiv.2]
  · intro d _
    change f d = f (d % c + c * (d / c))
    rw [Int.emod_add_mul_ediv]

/-- The least nonnegative Bézout inverse, including the value zero at modulus one. -/
def inverseMod (c r : ℤ) : ℤ := r.gcdA c % c

theorem inverseMod_spec {c r : ℤ} (hc : 0 < c) (hr : r.gcd c = 1) :
    0 ≤ inverseMod c r ∧ inverseMod c r < c ∧ r * inverseMod c r ≡ 1 [ZMOD c] := by
  have hbez : r * r.gcdA c + c * r.gcdB c = 1 := by
    simpa [hr] using (Int.gcd_eq_gcd_ab r c).symm
  refine ⟨Int.emod_nonneg _ hc.ne', Int.emod_lt_of_pos _ hc, ?_⟩
  calc
    r * inverseMod c r ≡ r * r.gcdA c [ZMOD c] := (Int.mod_modEq _ _).mul_left r
    _ ≡ 1 [ZMOD c] := Int.modEq_iff_dvd.mpr ⟨r.gcdB c, by linarith only [hbez]⟩

def linearPhase (c r : ℤ) : ℂ :=
  Complex.exp (((-(2 * Real.pi * (inverseMod c r : ℝ) / (c : ℝ)) : ℝ) : ℂ) * Complex.I)

def linearWeight (c r : ℤ) : ℂ :=
  linearPhase c r * (2 * (Real.pi : ℂ) * Complex.I / (c : ℂ) ^ 2)

private theorem norm_linearWeight (c : ℕ) (r : ℤ) :
    ‖linearWeight (c : ℤ) r‖ = 2 * Real.pi / (c : ℝ) ^ 2 := by
  have hphase : ‖linearPhase c r‖ = 1 := by
    simp [linearPhase, Complex.norm_exp, Complex.mul_re]
  simp only [linearWeight, norm_mul, norm_div, norm_pow, Int.cast_natCast, hphase,
    Complex.norm_natCast, Complex.norm_I, Complex.norm_two,
    Complex.norm_of_nonneg Real.pi_pos.le, one_mul, mul_one]

/-- The linear terms in the original strict rectangular order. -/
def linearRectangularCutoff (N : ℕ) (τ : ℂ) : ℂ :=
  ∑ c ∈ (range N).erase 0, ∑ d ∈ strictDenominators ((N : ℤ) ^ 2) (c : ℤ),
    linearPhase c (d % (c : ℤ)) *
      (2 * (Real.pi : ℂ) * Complex.I / ((c : ℂ) * ((c : ℂ) * τ + (d : ℂ))))

/-- The same outer truncation with symmetric principal values in each residue class. -/
def linearPrincipalValueCutoff (N : ℕ) (τ : ℂ) : ℂ :=
  ∑ c ∈ (range N).erase 0, ∑ r ∈ reducedResidues (c : ℤ),
    linearWeight c r * ((Real.pi : ℂ) * Complex.cot (Real.pi * shiftedArgument τ c r))

theorem linearRectangularCutoff_eq_residue_shifts (N : ℕ) (τ : ℂ) :
    linearRectangularCutoff N τ =
      ∑ c ∈ (range N).erase 0, ∑ r ∈ reducedResidues (c : ℤ),
        linearWeight c r *
          (∑ k ∈ strictShifts ((N : ℤ) ^ 2) (c : ℤ) r,
            1 / (shiftedArgument τ c r + (k : ℂ))) := by
  unfold linearRectangularCutoff
  apply sum_congr rfl
  intro c hc
  have hcN : 0 < c := Nat.pos_of_ne_zero (mem_erase.mp hc).1
  have hcZ : 0 < (c : ℤ) := by exact_mod_cast hcN
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcN.ne'
  rw [sum_strictDenominators_eq_residue_shifts hcZ]
  apply sum_congr rfl
  intro r hr
  obtain ⟨hr₀, hrc⟩ := mem_Ico.mp (mem_filter.mp hr).1
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  have hmod : (r + (c : ℤ) * k) % (c : ℤ) = r := by
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr₀ hrc]
  have hdenom : (c : ℂ) * ((c : ℂ) * τ + ((r : ℂ) + (c : ℂ) * (k : ℂ))) =
      (c : ℂ) ^ 2 * (τ + (r : ℂ) / (c : ℂ) + (k : ℂ)) := by
    field_simp [hcC]
    ring
  rw [hmod, Int.cast_add, Int.cast_mul, Int.cast_natCast, hdenom]
  simp only [linearWeight, shiftedArgument, Int.cast_natCast, div_eq_mul_inv, mul_inv_rev,
    one_mul]
  ring

theorem weighted_rectangular_residue_error_le {N c : ℕ} {r : ℤ} {τ : ℂ} {B : ℝ}
    (hc : 0 < c) (hcN : c < N) (hr₀ : 0 ≤ r) (hrc : r < (c : ℤ))
    (hτ : ‖τ‖ ≤ B) (hτim : 0 < τ.im) (hN : 2 * (B + 1) ≤ (N : ℝ)) :
    ‖linearWeight c r *
      ((∑ k ∈ strictShifts ((N : ℤ) ^ 2) (c : ℤ) r,
        1 / (shiftedArgument τ c r + (k : ℂ))) -
        (Real.pi : ℂ) * Complex.cot (Real.pi * shiftedArgument τ c r))‖ ≤
      (2 * Real.pi * comparisonConstant B) / ((c : ℝ) * (N : ℝ) ^ 2) := by
  have h := rectangular_residue_error_le hc hcN hr₀ hrc hτ hτim hN
  rw [norm_mul, norm_linearWeight]
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hc.trans hcN
  field_simp [hcR.ne', hNR.ne']

/-- Uniform `O(1/N)` error after summing all reduced residues and `0 < c < N`. -/
theorem linearRectangularCutoff_error_le {N : ℕ} {τ : ℂ} {B : ℝ}
    (hτ : ‖τ‖ ≤ B) (hτim : 0 < τ.im) (hN : 2 * (B + 1) ≤ (N : ℝ)) :
    ‖linearRectangularCutoff N τ - linearPrincipalValueCutoff N τ‖ ≤
      (2 * Real.pi * comparisonConstant B) / (N : ℝ) := by
  have hb : 0 ≤ B := (norm_nonneg τ).trans hτ
  have hNR : 0 < (N : ℝ) := by linarith only [hN, hb]
  let D : ℝ := 2 * Real.pi * comparisonConstant B
  have hD : 0 ≤ D := by dsimp [D, comparisonConstant]; positivity
  let E (c : ℕ) (r : ℤ) : ℂ :=
    linearWeight c r *
      ((∑ k ∈ strictShifts ((N : ℤ) ^ 2) (c : ℤ) r,
        1 / (shiftedArgument τ c r + (k : ℂ))) -
        (Real.pi : ℂ) * Complex.cot (Real.pi * shiftedArgument τ c r))
  have hrewrite : linearRectangularCutoff N τ - linearPrincipalValueCutoff N τ =
      ∑ c ∈ (range N).erase 0, ∑ r ∈ reducedResidues (c : ℤ), E c r := by
    rw [linearRectangularCutoff_eq_residue_shifts, linearPrincipalValueCutoff, ← sum_sub_distrib]
    apply sum_congr rfl
    intro c _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    exact (mul_sub _ _ _).symm
  have hperC (c : ℕ) (hc : c ∈ (range N).erase 0) :
      ‖∑ r ∈ reducedResidues (c : ℤ), E c r‖ ≤ D / (N : ℝ) ^ 2 := by
    obtain ⟨hc₀, hcN⟩ := mem_erase.mp hc
    have hcpos := Nat.pos_of_ne_zero hc₀
    have hcR : 0 < (c : ℝ) := by exact_mod_cast hcpos
    have hcard : (reducedResidues (c : ℤ)).card ≤ c := by
      calc
        (reducedResidues (c : ℤ)).card ≤ (Ico (0 : ℤ) (c : ℤ)).card :=
          card_le_card (filter_subset _ _)
        _ = c := by rw [Int.card_Ico]; simp
    have hcardR : ((reducedResidues (c : ℤ)).card : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcard
    calc
      ‖∑ r ∈ reducedResidues (c : ℤ), E c r‖ ≤
          ∑ r ∈ reducedResidues (c : ℤ), ‖E c r‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ reducedResidues (c : ℤ), D / ((c : ℝ) * (N : ℝ) ^ 2) := by
        apply sum_le_sum
        intro r hr
        obtain ⟨hr₀, hrc⟩ := mem_Ico.mp (mem_filter.mp hr).1
        exact weighted_rectangular_residue_error_le hcpos (mem_range.mp hcN)
          hr₀ hrc hτ hτim hN
      _ = ((reducedResidues (c : ℤ)).card : ℝ) * (D / ((c : ℝ) * (N : ℝ) ^ 2)) := by
        simp [nsmul_eq_mul]
      _ ≤ (c : ℝ) * (D / ((c : ℝ) * (N : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = D / (N : ℝ) ^ 2 := by field_simp [hcR.ne', hNR.ne']
  have hcard : ((range N).erase 0).card ≤ N := by
    simpa only [card_range] using card_le_card (erase_subset 0 (range N))
  have hcardR : (((range N).erase 0).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
  rw [hrewrite]
  calc
    ‖∑ c ∈ (range N).erase 0, ∑ r ∈ reducedResidues (c : ℤ), E c r‖ ≤
        ∑ c ∈ (range N).erase 0, ‖∑ r ∈ reducedResidues (c : ℤ), E c r‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ (range N).erase 0, D / (N : ℝ) ^ 2 := sum_le_sum hperC
    _ = (((range N).erase 0).card : ℝ) * (D / (N : ℝ) ^ 2) := by simp [nsmul_eq_mul]
    _ ≤ (N : ℝ) * (D / (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = D / (N : ℝ) := by field_simp [hNR.ne']

/-- The rectangular-to-principal-value error vanishes uniformly on each bounded
part of the upper half-plane. -/
theorem linearRectangularCutoff_sub_tendstoUniformlyOn (B : ℝ) :
    TendstoUniformlyOn (fun N : ℕ ↦ fun τ : ℂ ↦
      linearRectangularCutoff N τ - linearPrincipalValueCutoff N τ) (fun _ ↦ 0) atTop
      {τ : ℂ | ‖τ‖ ≤ B ∧ 0 < τ.im} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * (B + 1))
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi * comparisonConstant B)
  have htε : ∀ᶠ N : ℕ in atTop, (2 * Real.pi * comparisonConstant B) / (N : ℝ) < ε :=
    ht.eventually (gt_mem_nhds hε)
  filter_upwards [eventually_ge_atTop N₀, htε] with N hN htN
  intro τ hτ
  have hN' : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  rw [dist_zero_left]
  exact (linearRectangularCutoff_error_le hτ.1 hτ.2 (hN₀.trans hN')).trans_lt htN

end

end D5.S3.Arith.ModularForms.RademacherLinearCutoff
