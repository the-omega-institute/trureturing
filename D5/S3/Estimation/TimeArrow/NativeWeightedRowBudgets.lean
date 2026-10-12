/- GID: D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeWeightedRowBudgets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite native row transfer restores both actual and reference tails. -/

import D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
import D5.S3.Estimation.TimeArrow.NativeRowCountTail

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeRowCountTail
open private D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos
  D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.truncated_bounds
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

private theorem finite_square_markov {Ω : Type*} [Fintype Ω] (p X : Ω → ℝ)
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
