/- GID: D5/S3/CharacterSums/DyadicPrimeClassCount
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DyadicPrimeClassCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative Chebotarev estimates give dyadic prime counts uniform in the modulus. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Dyadic prime counts from the relative cyclotomic Chebotarev main term. -/

open Real Set MeasureTheory
noncomputable section

namespace D5.S3.CharacterSums.DyadicPrimeClassCount

/-- The logarithmic integral normalized at 2. -/
def logarithmicIntegral (t : ℝ) : ℝ := ∫ u in (2 : ℝ)..t, 1 / log u

/-- Main term in one reduced residue class, including the exceptional character value. -/
def mainTerm (θ : ℤ) (β t : ℝ) : ℝ :=
  logarithmicIntegral t - θ * logarithmicIntegral (t ^ β)

private lemma reciprocal_log_cont :
    ContinuousOn (fun u : ℝ => 1 / log u) (Ioi 1) :=
  continuousOn_const.div (continuousOn_log.mono fun _ hx => ne_of_gt (lt_trans zero_lt_one hx))
    fun _ hx => (log_pos hx).ne'

private lemma integral_deriv {t : ℝ} (ht : 1 < t) :
    HasDerivAt logarithmicIntegral (1 / log t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
  · apply (reciprocal_log_cont.mono ?_).intervalIntegrable
    exact (ordConnected_Ioi.uIcc_subset (by norm_num : (2 : ℝ) ∈ Ioi 1) ht)
  · exact reciprocal_log_cont.stronglyMeasurableAtFilter isOpen_Ioi t ht
  · exact reciprocal_log_cont.continuousAt (Ioi_mem_nhds ht)

private lemma integral_diff_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    logarithmicIntegral b - logarithmicIntegral a ≤ (b - a) / log a := by
  have il {u v : ℝ} (hu : 1 < u) (hv : 1 < v) :
      IntervalIntegrable (fun z : ℝ => 1 / log z) volume u v :=
    (reciprocal_log_cont.mono (ordConnected_Ioi.uIcc_subset hu hv)).intervalIntegrable
  have h := intervalIntegral.integral_add_adjacent_intervals
    (il (by norm_num : (1 : ℝ) < 2) ha) (il ha (ha.trans_le hab))
  have hmono := intervalIntegral.integral_mono_on hab (il ha (ha.trans_le hab))
    (intervalIntegrable_const (μ := volume)) (g := fun _ => 1 / log a)
    (fun x hx => one_div_le_one_div_of_le (log_pos ha) (log_le_log (by linarith) hx.1))
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  change (∫ t in 2..b, 1 / log t) - (∫ t in 2..a, 1 / log t) ≤ _
  rw [← h]
  linarith [show (b - a) * (1 / log a) = (b - a) / log a by ring]

private lemma mono_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    logarithmicIntegral a ≤ logarithmicIntegral b := by
  have hm : MonotoneOn logarithmicIntegral (Ioi 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi _)
    · exact fun _ hx => (integral_deriv hx).continuousAt.continuousWithinAt
    · exact fun _ hx => (integral_deriv (interior_subset hx)).hasDerivWithinAt
    · exact fun _ hx => div_nonneg zero_le_one (log_pos (interior_subset hx)).le
  exact hm ha (ha.trans_le hab) hab

private lemma integral_bound {t : ℝ} (ht : 16 ≤ t) : logarithmicIntegral t ≤ 4 * t / log t := by
  have hlog : log 16 = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
  have h0 : logarithmicIntegral 2 = 0 := by simp [logarithmicIntegral]
  have h1 := integral_diff_le (a := 2) (b := 16) (by norm_num) (by norm_num)
  have h2 : logarithmicIntegral 16 ≤ 4 * 16 / log 16 := by
    rw [h0, sub_zero] at h1
    rw [hlog]; calc
      _ ≤ (16 - 2) / log 2 := h1
      _ ≤ _ := by have h := log_pos (by norm_num : (1 : ℝ) < 2); field_simp; norm_num
  have mono : MonotoneOn (fun u : ℝ => 4 * u / log u - logarithmicIntegral u) (Ici 16) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
    · intro u hu
      have hu1 : 1 < u := by have := mem_Ici.1 hu; linarith
      exact (((continuousAt_const.mul continuousAt_id).div (continuousAt_log (by linarith))
        (log_pos hu1).ne').sub (integral_deriv hu1).continuousAt).continuousWithinAt
    · intro u hu
      have hu1 : 1 < u := by have := mem_Ici.1 (interior_subset hu); linarith
      exact ((((hasDerivAt_id u).const_mul 4).div (hasDerivAt_log (by linarith))
        (log_pos hu1).ne').sub (integral_deriv hu1)).hasDerivWithinAt
    · intro u hu
      have hu16 : 16 ≤ u := interior_subset hu
      have hu0 : 0 < u := by linarith
      have hlarge : 2 ≤ log u := by
        have := log_le_log (by norm_num : (0 : ℝ) < 16) hu16
        rw [hlog] at this
        linarith [log_two_gt_d9]
      have hlpos := log_pos (by linarith : 1 < u)
      field_simp
      simp only [id_eq]
      nlinarith [mul_le_mul_of_nonneg_right hlarge hu0.le]
  linarith [mono (show (16 : ℝ) ∈ Ici 16 by simp) ht ht]

private lemma main_deriv {β t : ℝ} (θ : ℤ) (hβ : 0 < β) (ht : 1 < t) :
    HasDerivAt (mainTerm θ β) ((1 - θ * t ^ (β - 1)) / log t) t := by
  have ht0 : 0 < t := by linarith
  have h := (integral_deriv ht).sub (((integral_deriv (one_lt_rpow ht hβ)).comp t
    (hasDerivAt_rpow_const (p := β) (Or.inl ht0.ne'))).const_mul (θ : ℝ))
  convert h using 1
  · rfl
  · rw [log_rpow ht0]
    have hl := (log_pos ht).ne'
    field_simp

private lemma main_increment {β Y W : ℝ} (θ : ℤ) (hβ : 0 < β) (hY : 1 < Y) (hW : 0 ≤ W)
    (hw : ∀ t ∈ Icc Y (2 * Y), W ≤ 1 - θ * t ^ (β - 1)) :
    W * Y / log (2 * Y) ≤ mainTerm θ β (2 * Y) - mainTerm θ β Y := by
  have h2 : Y ≤ 2 * Y := by linarith
  have hder {t : ℝ} (ht : t ∈ Icc Y (2 * Y)) :=
    (main_deriv θ hβ (hY.trans_le ht.1)).sub
      (((hasDerivAt_id t).const_mul W).div_const (log (2 * Y)))
  have mono : MonotoneOn (fun t => mainTerm θ β t - W * t / log (2 * Y)) (Icc Y (2 * Y)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · exact fun t ht => (hder ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hder (interior_subset ht)).hasDerivWithinAt
    · intro t hti
      have ht := interior_subset hti
      have hlog := log_le_log (by linarith [ht.1]) ht.2
      simp only [mul_one, sub_nonneg]
      exact div_le_div₀ (le_trans hW (hw t ht)) (hw t ht) (log_pos (hY.trans_le ht.1)) hlog
  have h := mono (left_mem_Icc.2 h2) (right_mem_Icc.2 h2) h2
  dsimp only at h
  linarith [show W * (2 * Y) / log (2 * Y) = 2 * (W * Y / log (2 * Y)) by ring]

private lemma exceptional_endpoint {β t : ℝ} (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (ht : 1 < t) :
    mainTerm 1 β t ≤ 2 * t * (1 - t ^ (β - 1)) / log t := by
  have htpos : 0 < t := by linarith
  have hβpos : 0 < β := by linarith
  have hp := rpow_le_rpow_of_exponent_le ht.le hβ1
  rw [rpow_one] at hp
  have h := integral_diff_le (one_lt_rpow ht hβpos) hp
  simp only [mainTerm, Int.cast_one, one_mul]
  rw [log_rpow htpos] at h
  have hpow : t ^ (β - 1) * t = t ^ β := by rw [← rpow_add_one htpos.ne']; ring_nf
  refine h.trans ?_
  rw [div_le_div_iff₀ (mul_pos hβpos (log_pos ht)) (log_pos ht)]
  nlinarith [mul_nonneg (sub_nonneg.2 hp)
    (show 0 ≤ (2 * β - 1) * log t from mul_nonneg (by linarith) (log_pos ht).le),
    congrArg (fun z => z * β * log t) hpow]

private lemma endpoint_sum {θ : ℤ} {β Y : ℝ}
    (hsign : θ = -1 ∨ θ = 0 ∨ θ = 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hY : 16 ≤ Y) :
    mainTerm θ β Y + mainTerm θ β (2 * Y) ≤
      24 * (if θ = 1 then 1 - Y ^ (β - 1) else 1) * (Y / log Y) := by
  have hY1 : 1 < Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hlog := log_pos hY1
  have hlog2 := log_le_log hY0 (show Y ≤ 2 * Y by linarith)
  have hlog2pos : 0 < log (2 * Y) := hlog.trans_le hlog2
  by_cases hθ : θ = 1
  · subst θ
    simp only [ite_true]
    let W := 1 - Y ^ (β - 1)
    have hYe : Y ^ (β - 1) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hY1.le (by linarith)
    have hW : 0 ≤ W := sub_nonneg.2 hYe
    have hpow : (Y * Y) ^ (β - 1) ≤ (2 * Y) ^ (β - 1) :=
      rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
    rw [mul_rpow hY0.le hY0.le] at hpow
    have hdouble : 1 - (2 * Y) ^ (β - 1) ≤ 2 * W := by
      dsimp [W]
      nlinarith [sq_nonneg (1 - Y ^ (β - 1))]
    have hfirst := exceptional_endpoint hβ hβ1 hY1
    have hlast := exceptional_endpoint hβ hβ1 (show 1 < 2 * Y by linarith)
    have hdouble' :
        2 * (2 * Y) * (1 - (2 * Y) ^ (β - 1)) / log (2 * Y) ≤ 2 * (2 * Y) * (2 * W) / log Y :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hdouble (by positivity)) hlog hlog2
    calc
      _ ≤ 2 * Y * W / log Y + 2 * (2 * Y) * (2 * W) / log Y :=
        add_le_add hfirst (hlast.trans hdouble')
      _ ≤ 24 * W * (Y / log Y) := by
        have hp : 0 ≤ W * (Y / log Y) := by positivity
        linarith only [show 2 * Y * W / log Y + 2 * (2 * Y) * (2 * W) / log Y =
            10 * (W * (Y / log Y)) by ring,
          show 24 * W * (Y / log Y) = 24 * (W * (Y / log Y)) by ring, hp]
  · simp only [hθ, ite_false]
    have hterm {t : ℝ} (ht : 16 ≤ t) : mainTerm θ β t ≤ 8 * t / log t := by
      have ht1 : 1 < t := by linarith
      have hp := rpow_le_rpow_of_exponent_le ht1.le hβ1
      rw [rpow_one] at hp
      have hi := mono_integral (one_lt_rpow ht1 (by linarith : 0 < β)) hp
      have hnon := mono_integral (a := 2) (b := t) (by norm_num) (by linarith)
      have hz : logarithmicIntegral 2 = 0 := by simp [logarithmicIntegral]
      have hl := integral_bound ht
      rw [show 8 * t / log t = 2 * (4 * t / log t) by ring]
      rcases hsign with rfl|rfl|h
      · simp only [mainTerm, Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add]
        linarith
      · simp only [mainTerm, Int.cast_zero, zero_mul, sub_zero]
        linarith
      · exact False.elim (hθ h)
    have hlarge : 8 * (2 * Y) / log (2 * Y) ≤ 8 * (2 * Y) / log Y :=
      div_le_div_of_nonneg_left (by positivity) hlog hlog2
    calc _ ≤ 8 * Y / log Y + 8 * (2 * Y) / log Y :=
           add_le_add (hterm hY) ((hterm (by linarith)).trans hlarge)
         _ = _ := by ring

private lemma stark_weight {Q Y s β : ℝ} (hs : 0 < s) (hQ : 1 < Q) (hQY : Q ≤ Y)
    (hgap : s / (Q ^ 2 * log Q) ≤ 1 - β) :
    min 1 s / (2 * Q ^ 2) ≤ 1 - Y ^ (β - 1) := by
  have hQ0 : 0 < Q := by linarith
  have hY0 : 0 < Y := hQ0.trans_le hQY
  have hlog := log_pos hQ
  have hlogY := log_le_log hQ0 hQY
  have hβ : 0 ≤ 1 - β := (by positivity : 0 ≤ s / (Q ^ 2 * log Q)).trans hgap
  let A := min 1 s / Q ^ 2
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : A ≤ 1 := by
    dsimp [A]; rw [div_le_iff₀ (by positivity)]; nlinarith [min_le_left (1 : ℝ) s]
  have hA : A ≤ (1 - β) * log Y := by
    calc
      A ≤ s / Q ^ 2 := div_le_div_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
      _ ≤ (1 - β) * log Q := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ (by positivity)] at hgap
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogY hβ
  have he := add_one_le_exp ((1 - β) * log Y)
  have hh : 1 ≤ (1 - A / 2) * exp ((1 - β) * log Y) := by
    calc
      1 ≤ (1 - A / 2) * (1 + A) := by nlinarith [mul_nonneg hA0 (sub_nonneg.2 hA1)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [rpow_def_of_pos hY0]
  have hrewrite : log Y * (β - 1) = -((1 - β) * log Y) := by ring
  rw [hrewrite, exp_neg]
  have hle : (exp ((1 - β) * log Y))⁻¹ ≤ 1 - A / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (exp_pos _)]; exact hh
  dsimp [A] at hle
  linarith [show min 1 s / (2 * Q ^ 2) = (min 1 s / Q ^ 2) / 2 by ring]

/-- Primes in a single residue class, with open lower and closed upper endpoint. -/
def classPrimes (m a : ℕ) (lo hi : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter fun p => Nat.Prime p ∧ p ≡ a [MOD m]

/-- Real-valued counting measure of the indicated half-open prime interval. -/
def classCount (m a : ℕ) (lo hi : ℝ) : ℝ := (classPrimes m a lo hi).card

private lemma count_add (m a : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    (classPrimes m a 0 Y).card + (classPrimes m a Y (2 * Y)).card =
    (classPrimes m a 0 (2 * Y)).card := by
  have hun := Finset.Ioc_union_Ioc_eq_Ioc (a := ⌊(0 : ℝ)⌋₊) (Nat.floor_mono hY)
    (Nat.floor_mono (show Y ≤ 2 * Y by linarith))
  unfold classPrimes
  rw [← hun, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter <| Finset.Ioc_disjoint_Ioc_of_le le_rfl

/-- The nonnegative lower bound on the dyadic main increment after the endpoint errors. -/
def dyadicMargin (η Y : ℝ) : ℝ :=
  max 0 (Y / log (2 * Y) - 24 * η * (Y / log Y))

/-- Endpoint extraction with a common offset and any nonnegative relative error. -/
theorem dyadic_class_count {m a : ℕ} {θ : ℤ} {β Y Q s offset η : ℝ}
    (hY : 16 ≤ Y) (hQ : 1 < Q) (hQY : θ = 1 → Q ≤ Y) (hs : 0 < s) (hη : 0 ≤ η)
    (hθ : θ = -1 ∨ θ = 0 ∨ θ = 1) (hβ : θ ≠ 0 → 1 / 2 ≤ β ∧ β ≤ 1)
    (hgap : θ = 1 → s / (Q ^ 2 * log Q) ≤ 1 - β)
    (hend : ∀ t ∈ ({Y, 2 * Y} : Finset ℝ),
      |(m.totient : ℝ) * (classCount m a 0 t + offset) - mainTerm θ β t| ≤
        η * mainTerm θ β t) :
    min 1 s / (2 * Q ^ 2) * dyadicMargin η Y ≤
      (m.totient : ℝ) * classCount m a Y (2 * Y) := by
  let γ := if θ = 0 then 1 else β
  have hγ : 1 / 2 ≤ γ ∧ γ ≤ 1 := by
    by_cases h : θ = 0
    · norm_num [γ,h]
    · simpa [γ,h] using hβ h
  have hF : mainTerm θ γ = mainTerm θ β := by
    by_cases h : θ = 0
    · subst θ; funext t; simp [mainTerm]
    · simp [γ,h]
  let W := if θ = 1 then 1 - Y ^ (γ - 1) else 1
  have hY1 : 1 < Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hq0 : 0 < Q := by linarith
  have hw : min 1 s / (2 * Q ^ 2) ≤ W := by
    by_cases h : θ = 1
    · simpa [W, γ, h] using stark_weight hs hQ (hQY h) (hgap h)
    · simp only [W, h, ite_false]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [min_le_left (1 : ℝ) s]
  have hw0 : 0 ≤ W := (by positivity : 0 ≤ min 1 s / (2 * Q ^ 2)).trans hw
  have hincr := main_increment θ (by linarith [hγ.1] : 0 < γ) hY1 hw0 (fun t ht => by
    rcases hθ with rfl | rfl | rfl
    · simp [W, (rpow_nonneg (hY0.le.trans ht.1) (γ - 1))]
    · simp [W]
    · simp only [W, ite_true, Int.cast_one, one_mul, sub_le_sub_iff_left]
      exact rpow_le_rpow_of_nonpos hY0 ht.1 (by linarith [hγ.2]))
  have hsum := endpoint_sum hθ hγ.1 hγ.2 hY
  change _ ≤ 24 * W * (Y / log Y) at hsum
  rw [hF] at hincr hsum
  have hlow := (abs_le.mp (hend (2 * Y) (by simp))).1
  have hhigh := (abs_le.mp (hend Y (by simp))).2
  have hcards : classCount m a 0 Y + classCount m a Y (2 * Y) = classCount m a 0 (2 * Y) := by
    unfold classCount
    exact_mod_cast count_add m a hY0.le
  rw [← hcards] at hlow
  have hR : 0 ≤ (m.totient : ℝ) * classCount m a Y (2 * Y) := by unfold classCount; positivity
  by_cases hM : 0 ≤ Y / log (2 * Y) - 24 * η * (Y / log Y)
  · unfold dyadicMargin
    rw [max_eq_right hM]
    refine (mul_le_mul_of_nonneg_right hw hM).trans ?_
    calc
      _ = W * Y / log (2 * Y) - η * (24 * W * (Y / log Y)) := by ring
      _ ≤ _ := by linarith only [hincr, mul_le_mul_of_nonneg_left hsum hη, hlow, hhigh]
  · simp only [dyadicMargin,max_eq_left (le_of_not_ge hM),mul_zero]
    exact hR

/-- The relative error in the cyclotomic specialization of the effective Chebotarev theorem. -/
def relativeError (A c Q t : ℝ) : ℝ :=
  A * (exp (-(c * log t / log Q)) + exp (-sqrt (c * log t)))

/-- The relative cyclotomic estimate restricted to the two prefixes used by one interval. -/
def cyclotomicEndpoints (count : ℕ → ℕ → ℝ → ℝ → ℝ) (m a : ℕ) (B A c s Y : ℝ) : Prop :=
  ∃ (Q : ℝ) (θ : ℤ) (β offset : ℝ),
    1 < Q ∧ Q ≤ m ∧ (θ = -1 ∨ θ = 0 ∨ θ = 1) ∧ (θ ≠ 0 → 1 / 2 ≤ β ∧ β ≤ 1) ∧
    (θ = 1 → s / (Q ^ 2 * log Q) ≤ 1 - β) ∧
    ∀ t ∈ ({Y, 2 * Y} : Finset ℝ), Q ^ B ≤ t →
      |(m.totient : ℝ) * (count m a 0 t + offset) - mainTerm θ β t| ≤
        relativeError A c Q t * mainTerm θ β t

private lemma exp_error {A u η : ℝ} (hη : 0 < η) (h : 2 * A / η ≤ u) :
    A * exp (-u) ≤ η / 2 := by
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
  rw [div_le_iff₀ hη] at h
  nlinarith [mul_le_mul_of_nonneg_left (add_one_le_exp u) hη.le]

/-- Each chosen relative-error tolerance has a polynomial modulus threshold for all classes. -/
theorem uniform_dyadic_class_count {B A c s : ℝ} (hA : 0 < A) (hc : 0 < c) (hs : 0 < s)
    (η : ℝ) (hη : 0 < η) :
    ∃ K D₀ : ℝ, 1 ≤ K ∧ 0 < D₀ ∧ ∀ (m a : ℕ) (D : ℝ),
      D₀ ≤ D → 2 * (m : ℝ) ^ K ≤ D → cyclotomicEndpoints classCount m a B A c s (D / 2) →
      min 1 s / (2 * (m : ℝ) ^ 2) * dyadicMargin η (D / 2) ≤
        (m.totient : ℝ) * classCount m a (D / 2) D := by
  let u := 2 * A / η
  have hu0 : 0 ≤ u := by unfold u; positivity
  let k := max (max 1 B) (u / c)
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
  have hkB : B ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
  have hkc : u / c ≤ k := le_max_right _ _
  refine ⟨k, 2 * max 16 (exp (u ^ 2 / c)), hk1, by positivity,?_⟩
  intro m a D hD₀ hD H
  obtain ⟨Q, θ, β, e, hQ, hQm, hθ, hβ, hgap, Ht⟩ := H
  have hQ0 : 0 < Q := by linarith
  let Y := D / 2
  have hY16 : 16 ≤ Y := by dsimp [Y]; linarith [le_max_left (16 : ℝ) (exp (u ^ 2 / c))]
  have hYa : exp (u ^ 2 / c) ≤ Y := by
    dsimp [Y]
    linarith [le_max_right (16 : ℝ) (exp (u ^ 2 / c))]
  have hY0 : 0 < Y := by linarith
  have hqk : Q ^ k ≤ Y := by
    exact (rpow_le_rpow hQ0.le hQm (by linarith : 0 ≤ k)).trans (by dsimp [Y]; linarith)
  have hQY : Q ≤ Y := by
    calc Q = Q ^ (1 : ℝ) := (rpow_one Q).symm
         _ ≤ _ := (rpow_le_rpow_of_exponent_le hQ.le hk1).trans hqk
  have hend : ∀ t ∈ ({Y, 2 * Y}:Finset ℝ),
      |(m.totient : ℝ) * (classCount m a 0 t + e) - mainTerm θ β t| ≤
        η * mainTerm θ β t := by
    intro t ht
    have hYt : Y ≤ t := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> linarith
    have ht0 : 0 < t := hY0.trans_le hYt
    have hlarge := Ht t ht ((rpow_le_rpow_of_exponent_le hQ.le hkB).trans (hqk.trans hYt))
    have hF : 0 ≤ mainTerm θ β t := by
      have hpos : 0 < relativeError A c Q t := by unfold relativeError; positivity
      exact (mul_nonneg_iff_of_pos_left hpos).1 ((abs_nonneg _).trans hlarge)
    have hlogQ := log_pos hQ
    have hlk := log_le_log (rpow_pos_of_pos hQ0 k) (hqk.trans hYt)
    rw [log_rpow hQ0] at hlk
    have hu : u ≤ c * log t / log Q := by
      rw [le_div_iff₀ hlogQ]
      rw [div_le_iff₀ hc] at hkc
      nlinarith [mul_le_mul_of_nonneg_left hlk hc.le, mul_le_mul_of_nonneg_right hkc hlogQ.le]
    have hv : u ≤ sqrt (c * log t) := by
      apply le_sqrt_of_sq_le
      have := (le_log_iff_exp_le ht0).2 (hYa.trans hYt)
      rw [div_le_iff₀ hc] at this
      linarith
    apply hlarge.trans
    apply mul_le_mul_of_nonneg_right _ hF
    unfold relativeError
    linarith only [exp_error hη hu, exp_error hη hv]
  have h := dyadic_class_count hY16 hQ (fun _ => hQY) hs hη.le hθ hβ hgap hend
  have h2Y : 2 * Y = D := by dsimp [Y]; ring
  rw [h2Y] at h
  refine le_trans ?_ h
  have hcoeff : min 1 s / (2 * (m : ℝ) ^ 2) ≤ min 1 s / (2 * Q ^ 2) :=
    div_le_div_of_nonneg_left (le_min zero_le_one hs.le) (by positivity)
      (by gcongr)
  exact mul_le_mul_of_nonneg_right hcoeff (le_max_left _ _)

end D5.S3.CharacterSums.DyadicPrimeClassCount
