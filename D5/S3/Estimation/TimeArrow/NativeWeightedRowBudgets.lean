/- GID: D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeWeightedRowBudgets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite native row transfer restores both actual and reference tails. -/

import D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
import D5.S3.Estimation.TimeArrow.NativeRowCountTail
import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeRowCountTail
open private D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.truncated_bounds
  from D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
noncomputable section

/-- All nonnegative count pairs inside the original all-row cutoff. -/
def countBox (L : ℕ) : Finset (ℕ × ℕ) :=
  ((range (8 * L + 1)).product (range (8 * L + 1))).filter fun c => c.1 + c.2 ≤ 8 * L

private theorem mem_countBox (L : ℕ) (c : ℕ × ℕ) :
    c ∈ countBox L ↔ c.1 + c.2 ≤ 8 * L := by
  rcases c with ⟨a, b⟩
  simp only [countBox, mem_filter, Finset.product_eq_sprod, Finset.mem_product, mem_range]
  omega

private theorem reference_exponential_sum {M q L : ℕ} (S : Support M q) (r κ z : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hz : 0 ≤ z) (i : Fin M) :
    HasSum (fun c : ℕ × ℕ => z ^ (c.1 + c.2) * rowReference S r L i c)
      (Real.exp ((z - 1) * (L : ℝ))) := by
  let a := (L : ℝ) * (1 + b r S (.inl i)) / 2
  let d := (L : ℝ) * (1 - b r S (.inl i)) / 2
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hb : -(1 - κ) ≤ b r S (.inl i) ∧ b r S (.inl i) ≤ 1 - κ := by
    simp only [b]
    split_ifs <;> constructor <;> linarith
  have ha : 0 ≤ a := by dsimp [a]; nlinarith [hb.1]
  have hd : 0 ≤ d := by dsimp [d]; nlinarith [hb.2]
  let f := fun n : ℕ => Real.exp (-a) * (z * a) ^ n / n.factorial
  let g := fun n : ℕ => Real.exp (-d) * (z * d) ^ n / n.factorial
  have hf : HasSum f (Real.exp ((z - 1) * a)) := by
    have hh := (NormedSpace.expSeries_div_hasSum_exp (z * a)).mul_left (Real.exp (-a))
    simpa only [f, mul_div_assoc, ← Real.exp_add, show -a + z * a = (z - 1) * a by ring,
      ← Real.exp_eq_exp_ℝ] using hh
  have hg : HasSum g (Real.exp ((z - 1) * d)) := by
    have hh := (NormedSpace.expSeries_div_hasSum_exp (z * d)).mul_left (Real.exp (-d))
    simpa only [g, mul_div_assoc, ← Real.exp_add, show -d + z * d = (z - 1) * d by ring,
      ← Real.exp_eq_exp_ℝ] using hh
  have hfg := hf.mul hg (hf.summable.mul_of_nonneg hg.summable
    (fun n => by dsimp [f]; positivity) (fun n => by dsimp [g]; positivity))
  have he (c : ℕ × ℕ) : f c.1 * g c.2 = z ^ (c.1 + c.2) * rowReference S r L i c := by
    dsimp [f, g, rowReference, a, d]
    rw [pow_add, mul_pow, mul_pow]
    ring
  have hsum : a + d = (L : ℝ) := by dsimp [a, d]; ring
  simpa only [he, ← Real.exp_add, ← mul_add, hsum] using hfg

private theorem reference_weighted_tail {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (i : Fin M) (g : ℕ × ℕ → ℝ) (hg : ∀ c, 0 ≤ g c ∧ g c ≤ 1) :
    Summable (fun c => g c * rowReference S r L i c) ∧
      0 ≤ (∑' c, g c * rowReference S r L i c) -
        ∑ c ∈ countBox L, g c * rowReference S r L i c ∧
      (∑' c, g c * rowReference S r L i c) -
        (∑ c ∈ countBox L, g c * rowReference S r L i c) ≤
          Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
  classical
  let Q := rowReference S r L i
  have hQ (c : ℕ × ℕ) : 0 ≤ Q c :=
    (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hQs : Summable Q := by
    simpa only [one_pow, one_mul, sub_self, zero_mul, Real.exp_zero] using
      (reference_exponential_sum S r κ 1 hκ hr hrκ hcκ hL (by norm_num) i).summable
  let f := fun c => g c * Q c
  have hf0 : ∀ c, 0 ≤ f c := fun c => mul_nonneg (hg c).1 (hQ c)
  have hfQ : ∀ c, f c ≤ Q c := fun c => by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hg c).2 (hQ c)
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hfQ hQs
  let tail := fun c => if c ∈ countBox L then (0 : ℝ) else f c
  have ht0 : ∀ c, 0 ≤ tail c := by intro c; dsimp [tail]; split_ifs <;> [exact le_rfl; exact hf0 c]
  have htf : ∀ c, tail c ≤ f c := by intro c; dsimp [tail]; split_ifs <;> simp [hf0]
  have ht : Summable tail := Summable.of_nonneg_of_le ht0 htf hf
  have hsplit : (∑' c, f c) - (∑ c ∈ countBox L, f c) = ∑' c, tail c := by
    have hpart : (fun c => if c ∈ countBox L then f c else 0) + tail = f := by
      funext c; dsimp [tail]; split_ifs <;> simp
    have hfin : Summable (fun c => if c ∈ countBox L then f c else 0) :=
      summable_of_ne_finset_zero (s := countBox L) (by intro c hc; simp [hc])
    have he := hfin.tsum_add ht
    change (∑' c, ((fun c => if c ∈ countBox L then f c else 0) + tail) c) = _ at he
    rw [hpart] at he
    have hefin : (∑' c, if c ∈ countBox L then f c else 0) = ∑ c ∈ countBox L, f c := by
      rw [tsum_eq_sum (s := countBox L) (fun c hc => if_neg hc)]
      exact sum_congr rfl fun c hc => if_pos hc
    rw [hefin] at he
    linarith
  have hmgf := reference_exponential_sum S r κ 4 hκ hr hrκ hcκ hL (by norm_num) i
  have hdom (c : ℕ × ℕ) : tail c ≤
      ((4 : ℝ) ^ (8 * L))⁻¹ * ((4 : ℝ) ^ (c.1 + c.2) * Q c) := by
    by_cases hc : c ∈ countBox L
    · dsimp [tail]; rw [if_pos hc]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hQ c))
    · have hn : 8 * L < c.1 + c.2 := by
        have := (mem_countBox L c).not.mp hc; omega
      have hp : (4 : ℝ) ^ (8 * L) ≤ (4 : ℝ) ^ (c.1 + c.2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      dsimp [tail]; rw [if_neg hc]
      apply (hfQ c).trans
      have he : Q c = ((4 : ℝ) ^ (8 * L))⁻¹ * ((4 : ℝ) ^ (8 * L) * Q c) := by
        field_simp
      calc
        Q c = _ := he
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (hQ c)) (by positivity)
  have hbound : (∑' c, tail c) ≤ ((4 : ℝ) ^ (8 * L))⁻¹ * Real.exp (3 * (L : ℝ)) := by
    calc
      _ ≤ ∑' c, ((4 : ℝ) ^ (8 * L))⁻¹ * ((4 : ℝ) ^ (c.1 + c.2) * Q c) :=
        ht.tsum_le_tsum hdom (hmgf.summable.mul_left _)
      _ = _ := by rw [tsum_mul_left, hmgf.tsum_eq]; norm_num
  have hpow : (4 : ℝ) ^ (8 * L) = Real.exp (8 * (L : ℝ) * Real.log 4) := by
    conv_lhs => rw [show (4 : ℝ) = Real.exp (Real.log 4) from (Real.exp_log (by norm_num)).symm]
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
  have hexp : ((4 : ℝ) ^ (8 * L))⁻¹ * Real.exp (3 * (L : ℝ)) ≤
      Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
    rw [hpow, ← Real.exp_neg, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hLn : (0 : ℝ) ≤ L := by positivity
    nlinarith
  refine ⟨hf, ?_, ?_⟩
  · change 0 ≤ (∑' c, f c) - ∑ c ∈ countBox L, f c
    rw [hsplit]
    exact tsum_nonneg ht0
  · change (∑' c, f c) - (∑ c ∈ countBox L, f c) ≤ _
    rw [hsplit]
    exact hbound.trans hexp

private theorem truncatedRow_countBox {M s : ℕ} (e : Experiment)
    (L : ℕ) (g : Fin M → ℕ × ℕ → ℝ) (i : Fin M) (o : Obs M s e) :
    truncatedRow e (countBox L) g i o =
      if count e o i 1 + count e o i (-1) ≤ 8 * L
      then g i (count e o i 1, count e o i (-1)) else 0 := by
  classical
  unfold truncatedRow
  simp_rw [show ∀ c : ℕ × ℕ,
    (count e o i 1 = c.1 ∧ count e o i (-1) = c.2) ↔
      c = (count e o i 1, count e o i (-1)) by
    intro c; simp [Prod.ext_iff, eq_comm]]
  simp [mem_countBox]

set_option maxHeartbeats 800000 in
-- The complete-row estimate combines finite moments with two restored tails.
/-- Restoring both tails yields a complete native weighted-row second
moment, with the same reference sum and every original row retained. -/
theorem native_full_weighted_moments (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        6 ≤ M → (L : ℝ) / M ≤ 1 / 45 →
        ∀ (S : Support M q) (e : Experiment) (I : Finset (Fin M))
          (g : Fin M → ℕ × ℕ → ℝ),
          (∀ i c, 0 ≤ g i c ∧ g i c ≤ 1) →
          let a := fun i => ∑' c, g i c * rowReference S r L i c
          let Z := fun o : Obs M (2 * M * L) e =>
            ∑ i ∈ I, g i (count e o i 1, count e o i (-1))
          let ζ := Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
          (|(∑ o, probability r e S o * Z o) - ∑ i ∈ I, a i| ≤
            (A * (L : ℝ) ^ 2 / M) * (∑ i ∈ I, a i) + 2 * I.card * ζ) ∧
          ((∑ o, probability r e S o * (Z o - ∑ i ∈ I, a i) ^ 2) ≤
            3 * (∑ i ∈ I, a i) +
              8 * (A * (L : ℝ) ^ 3 / M) * (∑ i ∈ I, a i) ^ 2 +
              10 * (I.card : ℝ) ^ 2 * ζ) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_truncated_weighted_moments κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e I g hg
  let a := fun i => ∑' c, g i c * rowReference S r L i c
  let ad := fun i => ∑ c ∈ countBox L, g i c * rowReference S r L i c
  let B := ∑ i ∈ I, a i
  let Bd := ∑ i ∈ I, ad i
  let Z := fun o : Obs M (2 * M * L) e => ∑ i ∈ I, g i (count e o i 1, count e o i (-1))
  let Zd := fun o : Obs M (2 * M * L) e => ∑ i ∈ I, truncatedRow e (countBox L) g i o
  let ζ := Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
  let n : ℝ := I.card
  let δ₁ := A * (L : ℝ) ^ 2 / M
  let δ₂ := A * (L : ℝ) ^ 3 / M
  let E := fun f : Obs M (2 * M * L) e → ℝ => ∑ o, probability r e S o * f o
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  have law := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1
  have hp := law.1 S
  have hsum := law.2 S
  have hz0 : 0 ≤ ζ := (Real.exp_pos _).le
  have hz1 : ζ ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hl4 : 1 ≤ Real.log (4 : ℝ) := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_gt_d9]
    have hLn : (0 : ℝ) ≤ L := by positivity
    nlinarith
  have hδ1 : 0 ≤ δ₁ := by dsimp [δ₁]; positivity
  have hδ2 : 0 ≤ δ₂ := by dsimp [δ₂]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have htail (i : Fin M) := reference_weighted_tail S r κ hκ hr hrκ hcκ hL i (g i) (hg i)
  have ha (i : Fin M) : 0 ≤ a i :=
    tsum_nonneg fun c => mul_nonneg (hg i c).1
      (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have had (i : Fin M) : 0 ≤ ad i :=
    sum_nonneg fun c _ => mul_nonneg (hg i c).1
      (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hBB : 0 ≤ B - Bd ∧ B - Bd ≤ n * ζ := by
    have he : B - Bd = ∑ i ∈ I, (a i - ad i) := by dsimp [B, Bd]; rw [sum_sub_distrib]
    rw [he]
    refine ⟨sum_nonneg (fun i _ => (htail i).2.1), ?_⟩
    calc
      _ ≤ ∑ _i ∈ I, ζ := sum_le_sum fun i _ => (htail i).2.2
      _ = n * ζ := by simp [n]
  have hB : 0 ≤ B := sum_nonneg fun i _ => ha i
  have hBd : 0 ≤ Bd := sum_nonneg fun i _ => had i
  have hBdB : Bd ≤ B := by linarith [hBB.1]
  have hD (c : ℕ × ℕ) (hc : c ∈ countBox L) :
      (c.1 : ℝ) ≤ 8 * L ∧ (c.2 : ℝ) ≤ 8 * L := by
    have hh := (mem_countBox L c).mp hc
    constructor
    · exact_mod_cast (show c.1 ≤ 8 * L by omega)
    · exact_mod_cast (show c.2 ≤ 8 * L by omega)
  have hm := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I (countBox L) g hD
    (fun i c _ => hg i c)
  have hdz (i : Fin M) (o : Obs M (2 * M * L) e) :
      0 ≤ g i (count e o i 1, count e o i (-1)) - truncatedRow e (countBox L) g i o ∧
      g i (count e o i 1, count e o i (-1)) - truncatedRow e (countBox L) g i o ≤
        if 8 * L < count e o i 1 + count e o i (-1) then (1 : ℝ) else 0 := by
    rw [truncatedRow_countBox]
    by_cases ho : count e o i 1 + count e o i (-1) ≤ 8 * L
    · rw [if_pos ho, if_neg (by omega)]
      simp
    · rw [if_neg ho, if_pos (by omega), sub_zero]
      exact hg i _
  have hZdiff (o : Obs M (2 * M * L) e) : 0 ≤ Z o - Zd o := by
    dsimp [Z, Zd]; rw [← sum_sub_distrib]
    exact sum_nonneg fun i _ => (hdz i o).1
  have hEZdiff : 0 ≤ E Z - E Zd ∧ E Z - E Zd ≤ n * ζ := by
    have he : E Z - E Zd = ∑ i ∈ I, E (fun o =>
        g i (count e o i 1, count e o i (-1)) - truncatedRow e (countBox L) g i o) := by
      dsimp [E, Z, Zd]
      rw [← sum_sub_distrib]
      simp_rw [← mul_sub, ← sum_sub_distrib, mul_sum]
      rw [sum_comm]
    refine ⟨?_, ?_⟩
    · dsimp [E]
      rw [← sum_sub_distrib]
      apply sum_nonneg
      intro o _
      rw [← mul_sub]
      exact mul_nonneg (hp o) (hZdiff o)
    · rw [he]
      calc
        _ ≤ ∑ _i ∈ I, ζ := by
          apply sum_le_sum
          intro i _
          have hh := native_row_count_tail r S hq hqm hr hr1 hc1 hM6 hL hLM e i
          apply le_trans _ hh
          apply sum_le_sum
          intro o _
          have ht := mul_le_mul_of_nonneg_left (hdz i o).2 (hp o)
          dsimp [E]
          split_ifs at ht ⊢ <;> simpa using ht
        _ = n * ζ := by simp [n]
  have hD2 : E (fun o => (Z o - Zd o) ^ 2) ≤ n ^ 2 * ζ := by
    have hpw (o : Obs M (2 * M * L) e) : (Z o - Zd o) ^ 2 ≤
        n * ∑ i ∈ I, if 8 * L < count e o i 1 + count e o i (-1) then (1 : ℝ) else 0 := by
      have hs := sq_sum_le_card_mul_sum_sq (s := I) (f := fun i =>
        g i (count e o i 1, count e o i (-1)) - truncatedRow e (countBox L) g i o)
      dsimp [Z, Zd]
      rw [← sum_sub_distrib]
      apply hs.trans
      apply mul_le_mul_of_nonneg_left _ hn
      apply sum_le_sum
      intro i _
      have hh := hdz i o
      split_ifs at hh ⊢ <;> nlinarith only [hh.1, hh.2]
    calc
      _ ≤ E (fun o => n * ∑ i ∈ I,
          if 8 * L < count e o i 1 + count e o i (-1) then (1 : ℝ) else 0) :=
        sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (hpw o) (hp o)
      _ = n * ∑ i ∈ I, (∑ o : Obs M (2 * M * L) e,
          if 8 * L < count e o i 1 + count e o i (-1) then probability r e S o else 0) := by
        dsimp [E]
        simp_rw [mul_sum]
        simp_rw [show ∀ o : Obs M (2 * M * L) e, ∀ v : ℝ,
          probability r e S o * (n * v) = n * (probability r e S o * v) by intro o v; ring]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro o _
        split_ifs <;> ring
      _ ≤ n * (n * ζ) := mul_le_mul_of_nonneg_left
        ((sum_le_sum fun i _ => native_row_count_tail r S hq hqm hr hr1 hc1 hM6 hL hLM e i).trans_eq
          (by simp [n, ζ])) hn
      _ = n ^ 2 * ζ := by ring
  refine ⟨?_, ?_⟩
  · change |E Z - B| ≤ δ₁ * B + 2 * n * ζ
    have hmd : |E Zd - Bd| ≤ δ₁ * Bd := hm.1
    have hb := abs_le.mp hmd
    have hmono := mul_le_mul_of_nonneg_left hBdB hδ1
    apply abs_le.mpr
    constructor <;> linarith only [hb.1, hb.2, hmono, hBB.1, hBB.2, hEZdiff.1, hEZdiff.2,
      mul_nonneg hn hz0]
  · change E (fun o => (Z o - B) ^ 2) ≤ 3 * B + 8 * δ₂ * B ^ 2 + 10 * n ^ 2 * ζ
    have hpt (o : Obs M (2 * M * L) e) : (Z o - B) ^ 2 ≤
        2 * (Zd o - Bd) ^ 2 + 2 * (Z o - Zd o) ^ 2 + 2 * (B - Bd) ^ 2 := by
      have hh := hZdiff o
      nlinarith only [sq_nonneg ((Zd o - Bd) - ((Z o - Zd o) - (B - Bd))),
        mul_nonneg hh hBB.1]
    have he := sum_le_sum (fun o (_ : o ∈ univ) => mul_le_mul_of_nonneg_left (hpt o) (hp o))
    have hexp : E (fun o => 2 * (Zd o - Bd) ^ 2 + 2 * (Z o - Zd o) ^ 2 + 2 * (B - Bd) ^ 2) =
        2 * E (fun o => (Zd o - Bd) ^ 2) + 2 * E (fun o => (Z o - Zd o) ^ 2) +
          2 * (B - Bd) ^ 2 := by
      dsimp [E]
      simp_rw [mul_add]
      rw [sum_add_distrib, sum_add_distrib]
      simp_rw [show ∀ o : Obs M (2 * M * L) e, ∀ v : ℝ,
        probability r e S o * (2 * v) = 2 * (probability r e S o * v) by intro o v; ring]
      rw [← mul_sum, ← mul_sum, ← mul_sum, ← sum_mul, hsum, one_mul]
    change E (fun o => (Z o - B) ^ 2) ≤ E (fun o =>
      2 * (Zd o - Bd) ^ 2 + 2 * (Z o - Zd o) ^ 2 + 2 * (B - Bd) ^ 2) at he
    rw [hexp] at he
    have hsq : Bd ^ 2 ≤ B ^ 2 := by nlinarith only [hBd, hB, hBdB]
    have hmono := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 3 * δ₂ by positivity)
    have hbq : (B - Bd) ^ 2 ≤ n ^ 2 * ζ := by
      have hh := mul_self_le_mul_self hBB.1 hBB.2
      have hh2 := mul_le_mul_of_nonneg_left hz1 hz0
      have hh3 := mul_le_mul_of_nonneg_left hh2 (sq_nonneg n)
      nlinarith only [hh, hh3]
    have hmd : E (fun o => (Zd o - Bd) ^ 2) ≤ (3 / 2) * Bd + 3 * δ₂ * Bd ^ 2 := hm.2
    nlinarith only [he, hmd, hmono, hBdB, hD2, hbq,
      mul_nonneg hδ2 (sq_nonneg B), mul_nonneg (sq_nonneg n) hz0]

theorem finite_square_markov {Ω : Type*} [Fintype Ω] (p X : Ω → ℝ)
    (a h B : ℝ) (hp : ∀ o, 0 ≤ p o) (hh : 0 < h)
    (hB : (∑ o, p o * (X o - a) ^ 2) ≤ B) :
    (∑ o, if h < |X o - a| then p o else 0) ≤ B / h ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
  rw [sum_mul]
  apply le_trans _ hB
  apply sum_le_sum
  intro o _
  split_ifs with ho
  · have ht := mul_self_le_mul_self hh.le ho.le
    have hs : h ^ 2 ≤ (X o - a) ^ 2 := by
      simpa only [← pow_two, sq_abs] using ht
    exact mul_le_mul_of_nonneg_left hs (hp o)
  · simp only [zero_mul]
    exact mul_nonneg (hp o) (sq_nonneg _)

/-- Complete native deterministic row-function deviations follow from the
full weighted second moment, with both restored tails in the same budget. -/
theorem native_full_weighted_deviation (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        6 ≤ M → (L : ℝ) / M ≤ 1 / 45 →
        ∀ (S : Support M q) (e : Experiment) (I : Finset (Fin M))
          (g : Fin M → ℕ × ℕ → ℝ),
          (∀ i c, 0 ≤ g i c ∧ g i c ≤ 1) → ∀ h : ℝ, 0 < h →
          let B := ∑ i ∈ I, ∑' c, g i c * rowReference S r L i c
          let Z := fun o : Obs M (2 * M * L) e =>
            ∑ i ∈ I, g i (count e o i 1, count e o i (-1))
          let ζ := Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
          (∑ o, if h < |Z o - B| then probability r e S o else 0) ≤
            (3 * B + 8 * (A * (L : ℝ) ^ 3 / M) * B ^ 2 +
              10 * (I.card : ℝ) ^ 2 * ζ) / h ^ 2 := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_full_weighted_moments κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e I g hg t ht
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  exact finite_square_markov _ _ _ t _
    ((finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1.1 S) ht
    (h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e I g hg).2

end
end D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open private
  D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
  D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
from D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeReferenceCalibration
noncomputable section

/-- Complete count-level calibration at zero common odds shift. -/
def referenceParameter (M q : ℕ) (r : ℝ) (c : ℕ × ℕ) : ℝ :=
  Real.sigmoid (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
    c.2 * Real.log ((1 - r) / (1 + compensation M q r)) -
    Real.log (((M - q : ℕ) : ℝ) / q))

private theorem reference_factor {M q : ℕ} (S : Support M q) (r : ℝ) (L : ℕ)
    (i : Fin M) (c : ℕ × ℕ) :
    rowReference S r L i c = Real.exp (-(L : ℝ)) *
      (((L : ℝ) * (1 + b r S (.inl i)) / 2) ^ c.1 *
        ((L : ℝ) * (1 - b r S (.inl i)) / 2) ^ c.2) /
          (c.1.factorial * c.2.factorial : ℕ) := by
  unfold rowReference
  push_cast
  have hexp : Real.exp (-((L : ℝ) * (1 + b r S (.inl i)) / 2)) *
      Real.exp (-((L : ℝ) * (1 - b r S (.inl i)) / 2)) = Real.exp (-(L : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-((L : ℝ) * (1 + b r S (.inl i)) / 2)) *
        Real.exp (-((L : ℝ) * (1 - b r S (.inl i)) / 2))) *
      (((L : ℝ) * (1 + b r S (.inl i)) / 2) ^ c.1 *
        ((L : ℝ) * (1 - b r S (.inl i)) / 2) ^ c.2) /
          ((c.1.factorial : ℝ) * c.2.factorial) := by ring
    _ = _ := by rw [hexp]

theorem reference_likelihood_ratio {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) (c : ℕ × ℕ) :
    rowReference S r L i c =
      Real.exp (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
        c.2 * Real.log ((1 - r) / (1 + compensation M q r))) * rowReference S r L j c := by
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  have hp : 0 < (1 + r) / (1 - compensation M q r) := div_pos (by linarith) (by linarith)
  have hm : 0 < (1 - r) / (1 + compensation M q r) := div_pos (by linarith) (by linarith)
  have hexp : Real.exp (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
      c.2 * Real.log ((1 - r) / (1 + compensation M q r))) =
      ((1 + r) / (1 - compensation M q r)) ^ c.1 *
        ((1 - r) / (1 + compensation M q r)) ^ c.2 := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hp, Real.exp_log hm]
  rw [hexp, reference_factor, reference_factor]
  simp only [b, if_pos hi, if_neg hj, sub_neg_eq_add]
  have hplus : ((1 + r) / (1 - compensation M q r)) *
      ((L : ℝ) * (1 + -compensation M q r) / 2) = (L : ℝ) * (1 + r) / 2 := by
    field_simp [ne_of_gt (sub_pos.mpr hc1)]
    <;> ring
  have hminus : ((1 - r) / (1 + compensation M q r)) *
      ((L : ℝ) * (1 + compensation M q r) / 2) = (L : ℝ) * (1 - r) / 2 := by
    field_simp
    <;> ring
  have he :
      (((1 + r) / (1 - compensation M q r)) ^ c.1 *
        ((1 - r) / (1 + compensation M q r)) ^ c.2) *
      (((L : ℝ) * (1 + -compensation M q r) / 2) ^ c.1 *
        ((L : ℝ) * (1 + compensation M q r) / 2) ^ c.2) =
      ((L : ℝ) * (1 + r) / 2) ^ c.1 * ((L : ℝ) * (1 - r) / 2) ^ c.2 := by
    rw [show ∀ a b d e : ℝ, (a * b) * (d * e) = (a * d) * (b * e) by intros; ring,
      ← mul_pow, ← mul_pow, hplus, hminus]
  calc
    _ = Real.exp (-(L : ℝ)) *
      ((((1 + r) / (1 - compensation M q r)) ^ c.1 *
        ((1 - r) / (1 + compensation M q r)) ^ c.2) *
      (((L : ℝ) * (1 + -compensation M q r) / 2) ^ c.1 *
        ((L : ℝ) * (1 + compensation M q r) / 2) ^ c.2)) /
        (c.1.factorial * c.2.factorial : ℕ) := by rw [he]
    _ = _ := by ring

private theorem pointwise_calibration {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) (c : ℕ × ℕ) :
    ((q : ℝ) * rowReference S r L i c + ((M - q : ℕ) : ℝ) * rowReference S r L j c) *
      referenceParameter M q r c = (q : ℝ) * rowReference S r L i c := by
  let W := c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
      c.2 * Real.log ((1 - r) / (1 + compensation M q r))
  let B : ℝ := ((M - q : ℕ) : ℝ) / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hN : (0 : ℝ) < (M - q : ℕ) := by exact_mod_cast (show 0 < M - q by omega)
  have hB : 0 < B := div_pos hN hqR
  have hR : rowReference S r L i c = Real.exp W * rowReference S r L j c :=
    reference_likelihood_ratio S r κ hκ hr hrκ hcκ hL i j hi hj c
  rw [hR]
  change _ * Real.sigmoid (W - Real.log B) = _
  rw [Real.sigmoid_def, neg_sub, Real.exp_sub, Real.exp_log hB]
  dsimp [B]
  field_simp
  <;> ring

/-- The complete reference mean is exactly q. Its complete calibration
variance is the signal reference expectation of one minus the same parameter. -/
theorem reference_calibration_mean_variance {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) :
    ((q : ℝ) * (∑' c, referenceParameter M q r c * rowReference S r L i c) +
      ((M - q : ℕ) : ℝ) * (∑' c, referenceParameter M q r c * rowReference S r L j c) = q) ∧
    ((q : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L i c) +
      ((M - q : ℕ) : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L j c) =
      (q : ℝ) * (∑' c, (1 - referenceParameter M q r c) * rowReference S r L i c)) := by
  let p := referenceParameter M q r
  have hp (c : ℕ × ℕ) : 0 ≤ p c ∧ p c ≤ 1 :=
    ⟨Real.sigmoid_nonneg _, Real.sigmoid_le_one _⟩
  have hv (c : ℕ × ℕ) : 0 ≤ p c * (1 - p c) ∧ p c * (1 - p c) ≤ 1 := by
    constructor
    · exact mul_nonneg (hp c).1 (by linarith [(hp c).2])
    · nlinarith [(hp c).1, (hp c).2, sq_nonneg (p c - 1 / 2)]
  have hs (g : ℕ × ℕ → ℝ) (hg : ∀ c, 0 ≤ g c ∧ g c ≤ 1) (k : Fin M) :
      Summable (fun c => g c * rowReference S r L k c) :=
    (D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
      S r κ hκ hr hrκ hcκ hL k g hg).1
  have hpoint := pointwise_calibration S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj
  have hnorm : (∑' c, rowReference S r L i c) = 1 := by
    have hh := D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
      S r κ 1 hκ hr hrκ hcκ hL (by norm_num) i
    simpa using hh.tsum_eq
  constructor
  · have hadd := ((hs p hp i).mul_left (q : ℝ)).tsum_add
      ((hs p hp j).mul_left ((M - q : ℕ) : ℝ))
    rw [← tsum_mul_left, ← tsum_mul_left, ← hadd]
    have he (c : ℕ × ℕ) : (q : ℝ) * (p c * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * (p c * rowReference S r L j c) =
        (q : ℝ) * rowReference S r L i c := by
      have hh := hpoint c
      change (_ * p c) = _ at hh
      nlinarith
    simp_rw [he]
    rw [tsum_mul_left, hnorm, mul_one]
  · have hadd := ((hs (fun c => p c * (1 - p c)) hv i).mul_left (q : ℝ)).tsum_add
      ((hs (fun c => p c * (1 - p c)) hv j).mul_left ((M - q : ℕ) : ℝ))
    rw [← tsum_mul_left, ← tsum_mul_left, ← hadd]
    have he (c : ℕ × ℕ) : (q : ℝ) * ((p c * (1 - p c)) * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * ((p c * (1 - p c)) * rowReference S r L j c) =
        (q : ℝ) * ((1 - p c) * rowReference S r L i c) := by
      have hh := congrArg (fun x : ℝ => x * (1 - p c)) (hpoint c)
      change _ = _ at hh
      nlinarith
    simp_rw [he]
    rw [tsum_mul_left]

private theorem all_row_reference_sum {M q L : ℕ} (S : Support M q) (r : ℝ)
    (g : ℕ × ℕ → ℝ) (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) :
    (∑ k : Fin M, ∑' c, g c * rowReference S r L k c) =
      (q : ℝ) * (∑' c, g c * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * (∑' c, g c * rowReference S r L j c) := by
  classical
  have hk (k : Fin M) : (∑' c, g c * rowReference S r L k c) =
      if k ∈ S.val then (∑' c, g c * rowReference S r L i c)
      else (∑' c, g c * rowReference S r L j c) := by
    by_cases h : k ∈ S.val
    · rw [if_pos h]
      congr 1
      funext c
      simp only [rowReference, b, if_pos h, if_pos hi]
    · rw [if_neg h]
      congr 1
      funext c
      simp only [rowReference, b, if_neg h, if_neg hj]
  rw [sum_congr rfl (fun k _ => hk k)]
  rw [sum_ite]
  have hsig : (univ.filter fun k : Fin M => k ∈ S.val) = S.val := by ext k; simp
  have hbg : (univ.filter fun k : Fin M => k ∉ S.val).card = M - q := by
    have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin M))) (p := fun k => k ∈ S.val)
    rw [hsig, S.property] at hc
    simp only [card_univ, Fintype.card_fin] at hc
    omega
  simp [hsig, hbg, S.property]

/-- The reference calibration identities control all-row mean and variance
deviations under each original law, with a common restored-tail budget. -/
theorem native_reference_calibration_deviation (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        6 ≤ M → (L : ℝ) / M ≤ 1 / 45 →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val → ∀ b h : ℝ, 0 < b → 0 < h →
          let p := referenceParameter M q r
          let V := ∑ k : Fin M, ∑' c, (p c * (1 - p c)) * rowReference S r L k c
          let P := fun o : Obs M (2 * M * L) e =>
            ∑ k : Fin M, p (count e o k 1, count e o k (-1))
          let D := fun o : Obs M (2 * M * L) e =>
            ∑ k : Fin M, p (count e o k 1, count e o k (-1)) *
              (1 - p (count e o k 1, count e o k (-1)))
          let B := 3 * (q : ℝ) + 8 * (A * (L : ℝ) ^ 3 / M) * (q : ℝ) ^ 2 +
            10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
          0 ≤ V ∧ V ≤ q ∧
            (∑ o, if b < |P o - q| ∨ h < |D o - V| then probability r e S o else 0) ≤
              B / b ^ 2 + B / h ^ 2 := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_full_weighted_deviation κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e i j hi hj b t hb ht
  let p := referenceParameter M q r
  let v := fun c : ℕ × ℕ => p c * (1 - p c)
  let V := ∑ k : Fin M, ∑' c, v c * rowReference S r L k c
  let B := 3 * (q : ℝ) + 8 * (A * (L : ℝ) ^ 3 / M) * (q : ℝ) ^ 2 +
      10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
  have hp (c : ℕ × ℕ) : 0 ≤ p c ∧ p c ≤ 1 :=
    ⟨Real.sigmoid_nonneg _, Real.sigmoid_le_one _⟩
  have hv (c : ℕ × ℕ) : 0 ≤ v c ∧ v c ≤ 1 := by
    dsimp [v]
    constructor
    · exact mul_nonneg (hp c).1 (by linarith [(hp c).2])
    · nlinarith only [(hp c).1, (hp c).2, sq_nonneg (p c - 1 / 2)]
  have hcal := reference_calibration_mean_variance S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj
  have hmean : (∑ k : Fin M, ∑' c, p c * rowReference S r L k c) = (q : ℝ) := by
    rw [all_row_reference_sum S r p i j hi hj]
    exact hcal.1
  have hVar : V = (q : ℝ) * (∑' c, (1 - p c) * rowReference S r L i c) := by
    dsimp [V]
    rw [all_row_reference_sum S r v i j hi hj]
    exact hcal.2
  have hQ (c : ℕ × ℕ) : 0 ≤ rowReference S r L i c :=
    (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hcomplement (c : ℕ × ℕ) : 0 ≤ 1 - p c ∧ 1 - p c ≤ 1 := by
    constructor <;> linarith [(hp c).1, (hp c).2]
  have hs := (D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
    S r κ hκ hr hrκ hcκ hL i (fun c => 1 - p c) hcomplement).1
  have hnorm := D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
    S r κ 1 hκ hr hrκ hcκ hL (by norm_num) i
  have htotal : (∑' c, rowReference S r L i c) = 1 := by simpa using hnorm.tsum_eq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hV0 : 0 ≤ V := by
    rw [hVar]
    exact mul_nonneg hq0 (tsum_nonneg fun c => mul_nonneg (hcomplement c).1 (hQ c))
  have hVq : V ≤ q := by
    rw [hVar]
    have hh := hs.tsum_le_tsum (fun c => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcomplement c).2 (hQ c))
      (by simpa only [one_pow, one_mul] using hnorm.summable)
    rw [htotal] at hh
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hq0
  have hP := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e univ
    (fun _ => p) (fun _ c => hp c) b hb
  simp only [hmean, card_univ, Fintype.card_fin] at hP
  have hD := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e univ
    (fun _ => v) (fun _ c => hv c) t ht
  have hδ : 0 ≤ A * (L : ℝ) ^ 3 / M := by positivity
  have hbudget : 3 * V + 8 * (A * (L : ℝ) ^ 3 / M) * V ^ 2 +
      10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) ≤ B := by
    have hsq : V ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith only [hV0, hVq, hq0]
    have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 8 * (A * (L : ℝ) ^ 3 / M) by positivity)
    dsimp [B]
    linarith only [hVq, hh]
  have hD' : (∑ o : Obs M (2 * M * L) e,
      if t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V|
      then probability r e S o else 0) ≤ B / t ^ 2 := by
    apply hD.trans
    simp only [card_univ, Fintype.card_fin]
    exact div_le_div_of_nonneg_right hbudget (sq_nonneg t)
  refine ⟨hV0, hVq, ?_⟩
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  have hprob := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1.1 S
  apply le_trans _ (add_le_add hP hD')
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro o _
  change (if b < |(∑ k : Fin M, p (count e o k 1, count e o k (-1))) - q| ∨
      t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V|
      then probability r e S o else 0) ≤
    (if b < |(∑ k : Fin M, p (count e o k 1, count e o k (-1))) - q|
      then probability r e S o else 0) +
    (if t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V|
      then probability r e S o else 0)
  by_cases hp' : b < |(∑ k : Fin M, p (count e o k 1, count e o k (-1))) - q| <;>
    by_cases hd' : t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V| <;>
    simp only [hp', hd', or_true, true_or, or_false, false_or, if_true, if_false]
  · exact le_add_of_nonneg_right (hprob o)
  · simp
  · simp
  · simp

end
end D5.S3.Estimation.TimeArrow.NativeReferenceCalibration

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeReferenceCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
noncomputable section

private theorem row_reference_successors {M q L : ℕ} (S : Support M q) (r : ℝ)
    (i : Fin M) (k l : ℕ) :
    rowReference S r L i (k + 1, l) =
      ((L : ℝ) * (1 + b r S (.inl i)) / 2 / (k + 1)) * rowReference S r L i (k, l) ∧
    rowReference S r L i (k, l + 1) =
      ((L : ℝ) * (1 - b r S (.inl i)) / 2 / (l + 1)) * rowReference S r L i (k, l) := by
  unfold rowReference
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  constructor <;> field_simp <;> ring

/-- Large central signal counts give simultaneous reference ratios for all
four cells, using the original compensated model rather than a new law. -/
theorem signal_four_reference_ratios {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val) (k l : ℕ)
    (hkp : 15 / 16 ≤ ((L : ℝ) * (1 + r) / 2 / (k + 1)))
    (hkp' : ((L : ℝ) * (1 + r) / 2 / (k + 1)) ≤ 1)
    (hlp : 15 / 16 ≤ ((L : ℝ) * (1 - r) / 2 / (l + 1)))
    (hlp' : ((L : ℝ) * (1 - r) / 2 / (l + 1)) ≤ 1) :
    ∀ j : Fin 4,
      7 / 8 * rowReference S r L i (k, l) ≤
        rowReference S r L i (![(k,l), (k+1,l), (k,l+1), (k+1,l+1)] j) ∧
      rowReference S r L i (![(k,l), (k+1,l), (k,l+1), (k+1,l+1)] j) ≤
        9 / 8 * rowReference S r L i (k, l) := by
  have hpos := D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos
    S r κ hκ hr hrκ hcκ hL i (k,l)
  have hk := (row_reference_successors (L := L) S r i k l).1
  have hl := (row_reference_successors (L := L) S r i k l).2
  have hkl := (row_reference_successors (L := L) S r i k (l+1)).1
  simp only [b, if_pos hi] at hk hl hkl
  have hprodlo : 7 / 8 ≤
      ((L : ℝ) * (1 + r) / 2 / (k + 1)) * ((L : ℝ) * (1 - r) / 2 / (l + 1)) := by
    have hh := mul_le_mul hkp hlp (by norm_num : (0 : ℝ) ≤ 15 / 16) (by linarith)
    norm_num at hh
    linarith only [hh]
  have hprodhi :
      ((L : ℝ) * (1 + r) / 2 / (k + 1)) * ((L : ℝ) * (1 - r) / 2 / (l + 1)) ≤ 1 := by
    nlinarith only [hkp, hkp', hlp, hlp',
      mul_nonneg (by linarith : 0 ≤ 1 - ((L : ℝ) * (1 + r) / 2 / (k + 1)))
        (by linarith : 0 ≤ ((L : ℝ) * (1 - r) / 2 / (l + 1)))]
  intro j
  fin_cases j
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k,l) ∧
      rowReference S r L i (k,l) ≤ 9/8 * rowReference S r L i (k,l)
    constructor <;> nlinarith only [hpos]
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k+1,l) ∧
      rowReference S r L i (k+1,l) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hk]
    constructor <;> nlinarith only [hpos, hkp, hkp']
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k,l+1) ∧
      rowReference S r L i (k,l+1) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hl]
    constructor <;> nlinarith only [hpos, hlp, hlp']
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k+1,l+1) ∧
      rowReference S r L i (k+1,l+1) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hkl, hl, ← mul_assoc]
    exact ⟨mul_le_mul_of_nonneg_right hprodlo hpos.le,
      (mul_le_mul_of_nonneg_right hprodhi hpos.le).trans (by nlinarith only [hpos])⟩


theorem original_count_rounding (r : ℝ) (L : ℕ) (hr : 0 < r) (hr1 : r < 1)
    (hL : 1 ≤ L) (hplus : 15 ≤ ((1+r)/2)*(L : ℝ))
    (hminus : 30 ≤ ((1-r)/2)*(L : ℝ)) :
    let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
    let l := L-k
    k ≤ L ∧ 0 < k ∧ 0 < l ∧
      15/16 ≤ ((L : ℝ)*(1+r)/2/(k+1)) ∧ ((L : ℝ)*(1+r)/2/(k+1)) ≤ 1 ∧
      15/16 ≤ ((L : ℝ)*(1-r)/2/(l+1)) ∧ ((L : ℝ)*(1-r)/2/(l+1)) ≤ 1 := by
  let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
  let l := L-k
  have ha0 : 0 ≤ ((1+r)/2)*(L : ℝ) := by positivity
  have hklo := Nat.floor_le ha0
  have hkhi := Nat.lt_floor_add_one (((1+r)/2)*(L : ℝ))
  change (k : ℝ) ≤ _ at hklo
  change _ < (k : ℝ)+1 at hkhi
  have hkL : k ≤ L := by
    apply Nat.floor_le_of_le
    nlinarith only [hr1, show (0 : ℝ) ≤ L by positivity]
  have hlr : (l : ℝ) = (L : ℝ)-k := by
    exact Nat.cast_sub hkL
  have hkp : 0 < k := by
    have hh : (0 : ℝ) < k := by linarith only [hplus,hkhi]
    exact_mod_cast hh
  have hlp : 0 < l := by
    have hh : (0 : ℝ) < l := by rw [hlr]; linarith only [hminus,hklo]
    exact_mod_cast hh
  refine ⟨hkL,hkp,hlp,?_,?_,?_,?_⟩
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
    nlinarith only [hplus,hklo]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
    linarith only [hkhi]
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < l+1)).mpr
    rw [hlr]
    nlinarith only [hminus,hkhi]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < l+1)).mpr
    rw [hlr]
    nlinarith only [hklo]

/-- The central four-cell comparison retains the original natural floor
and l=lambda-k. Only explicit lower scale bounds are needed. -/
theorem floored_signal_four_reference_ratios {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1-κ)
    (hcκ : compensation M q r ≤ 1-κ) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val)
    (hplus : 15 ≤ ((1+r)/2)*(L : ℝ)) (hminus : 30 ≤ ((1-r)/2)*(L : ℝ)) :
    let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
    let l := L-k
    ∀ j : Fin 4, 7/8 * rowReference S r L i (k,l) ≤
      rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] j) ∧
      rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] j) ≤
        9/8 * rowReference S r L i (k,l) := by
  have hr1 : r < 1 := by linarith only [hrκ,hκ]
  have hh := original_count_rounding r L hr hr1 hL hplus hminus
  dsimp only at hh ⊢
  exact signal_four_reference_ratios S r κ hκ hr hrκ hcκ hL i hi _ _
    hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.1 hh.2.2.2.2.2.2

/-- The background A mean is exactly the signal A mean times the negative
original A logit. The finite-size compensation and M-q are preserved. -/
theorem background_reference_cell_ratio {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (hq : 1 ≤ q) (hqm : q < M) (i j : Fin M)
    (hi : i ∈ S.val) (hj : j ∉ S.val) (k l : ℕ) :
    ((M - q : ℕ) : ℝ) * rowReference S r L j (k,l) =
      ((q : ℝ) * rowReference S r L i (k,l)) *
        Real.exp (-(k * Real.log ((1+r)/(1-compensation M q r)) +
          l * Real.log ((1-r)/(1+compensation M q r)) -
          Real.log (((M-q : ℕ) : ℝ) / q))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hMR : (0 : ℝ) < (M-q : ℕ) := by exact_mod_cast (show 0 < M-q by omega)
  rw [reference_likelihood_ratio S r κ hκ hr hrκ hcκ hL i j hi hj (k,l)]
  rw [neg_sub, Real.exp_sub, Real.exp_log (div_pos hMR hqR)]
  field_simp
  <;> ring

end
end D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
