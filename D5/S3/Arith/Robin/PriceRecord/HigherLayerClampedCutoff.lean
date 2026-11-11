/- GID: D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Constructed strict cutoffs, boundary-aware movement and all-layer root bounds. -/
import D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! A cutoff equal to 2 excludes 2, and an ordinary root excludes its endpoint. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open Finset Real
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope

theorem root_exists {j : ℕ} (hj : 2 ≤ j) {η : ℝ}
    (hη : 0 < η) (hactive : η < beta j 2) :
    ∃ u : ℝ, 2 < u ∧ beta j u = η := by
  obtain ⟨v, hv, hsmall⟩ := beta_small_endpoint (by omega : 1 ≤ j) hη
  obtain ⟨u, hu, hroot⟩ := intermediate_value_Icc' hv
    ((beta_continuousOn (by omega : 1 ≤ j)).mono (fun t ht => ht.1))
    ⟨hsmall.le, hactive.le⟩
  refine ⟨u, lt_of_le_of_ne hu.1 ?_, hroot⟩
  intro h
  subst u
  linarith

def cutoff (j : ℕ) (η : ℝ) : ℝ :=
  if h : 2 ≤ j ∧ 0 < η ∧ η < beta j 2 then
    Classical.choose (root_exists h.1 h.2.1 h.2.2) else 2

theorem cutoff_spec {j : ℕ} (hj : 2 ≤ j) {η : ℝ} (hη : 0 < η) :
    2 ≤ cutoff j η ∧ beta j (cutoff j η) ≤ η ∧
    (2 < cutoff j η → beta j (cutoff j η) = η) ∧
    (η < beta j 2 ↔ 2 < cutoff j η) := by
  by_cases h : η < beta j 2
  · have hs := Classical.choose_spec (root_exists hj hη h)
    have he : cutoff j η = Classical.choose (root_exists hj hη h) := by simp [cutoff, hj, hη, h]
    rw [he]
    exact ⟨hs.1.le, hs.2.le, fun _ => hs.2, iff_of_true h hs.1⟩
  · simp only [cutoff, hj, hη, h, and_false, ↓reduceDIte]
    exact ⟨le_rfl, le_of_not_gt h, by simp, by simp [h]⟩

theorem cutoff_antitone {j : ℕ} (hj : 2 ≤ j) {η ζ : ℝ}
    (hη : 0 < η) (hζ : 0 < ζ) (hηζ : η ≤ ζ) : cutoff j ζ ≤ cutoff j η := by
  obtain ⟨hx, hbx, _, _⟩ := cutoff_spec hj hη
  obtain ⟨hy, _, hby, _⟩ := cutoff_spec hj hζ
  by_contra! hxy
  have h := beta_strictAntiOn hj hx hy hxy
  rw [hby (hx.trans_lt hxy)] at h
  linarith

/-- Exact strict occupancy, including p=2 and every root tie. -/
theorem cutoff_occupancy {j : ℕ} (hj : 2 ≤ j) {η u : ℝ}
    (hη : 0 < η) (hu : 2 ≤ u) : η < beta j u ↔ u < cutoff j η := by
  obtain ⟨hx, hbx, hroot, hactive⟩ := cutoff_spec hj hη
  constructor
  · intro h
    by_contra! hnot
    have hh := (beta_strictAntiOn hj).antitoneOn hx hu hnot
    linarith
  · intro h
    have hr := hroot (hu.trans_lt h)
    have hh := beta_strictAntiOn hj hu hx h
    rwa [hr] at hh

theorem log_price_ratio_le {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) :
    log ((1 + s) / (1 - s)) ≤ 3 * s := by
  have hm : 0 < 1 - s := by linarith
  have hp : 0 < 1 + s := by linarith
  have h1 := log_le_sub_one_of_pos hp
  have h2 := log_le_sub_one_of_pos (inv_pos.mpr hm)
  rw [log_inv] at h2
  have hi : (1 - s)⁻¹ - 1 ≤ 2 * s := by
    apply (sub_le_iff_le_add).mpr
    field_simp [hm.ne']
    nlinarith [mul_nonneg hs.le (show 0 ≤ 1 - 2 * s by linarith)]
  rw [log_div hp.ne' hm.ne']
  linarith

/-- Movement for a relative price change. The clamped endpoint is included. -/
theorem cutoff_movement {j : ℕ} (hj : 2 ≤ j) {«λ» s : ℝ}
    («hλ» : 0 < «λ») (hs : 0 < s) (hs2 : s ≤ 1 / 2) :
    cutoff j ((1 - s) * «λ») - cutoff j ((1 + s) * «λ») ≤
      9 * s * cutoff j ((1 - s) * «λ») / j := by
  let a := cutoff j ((1 + s) * «λ»)
  let b := cutoff j ((1 - s) * «λ»)
  have hm : 0 < (1 - s) * «λ» := mul_pos (by linarith) «hλ»
  have hp : 0 < (1 + s) * «λ» := mul_pos (by linarith) «hλ»
  have ha := cutoff_spec hj hp
  have hb := cutoff_spec hj hm
  have hab : a ≤ b := cutoff_antitone hj hm hp
    (mul_le_mul_of_nonneg_right (by linarith) «hλ».le)
  have ha2 : 2 ≤ a := ha.1
  have hb2 : 2 ≤ b := hb.1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  by_cases hb0 : b = 2
  · have ha0 : a = 2 := by linarith
    change b - a ≤ 9 * s * b / j
    rw [hb0, ha0, sub_self]
    positivity
  have hbgt : 2 < b := lt_of_le_of_ne hb2 (Ne.symm hb0)
  have hroot : beta j b = (1 - s) * «λ» := hb.2.2.1 hbgt
  have hslope := log_beta_drop hj ha2 hab
  have hratio : beta j a / beta j b ≤ (1 + s) / (1 - s) := by
    rw [hroot]
    apply (div_le_div_iff₀ hm (by linarith : 0 < 1 - s)).mpr
    have hs0 : 0 ≤ 1 - s := by linarith
    nlinarith only [mul_le_mul_of_nonneg_right ha.2.1 hs0]
  have hlog := log_le_log (div_pos (beta_pos ha2 (by omega))
    (beta_pos hb2 (by omega))) hratio
  have hbound : (j : ℝ) / 3 * log (b / a) ≤ 3 * s :=
    hslope.trans (hlog.trans (log_price_ratio_le hs hs2))
  have hround := log_le_sub_one_of_pos (div_pos (by linarith : 0 < a) (by linarith : 0 < b))
  rw [log_div (by linarith : a ≠ 0) (by linarith : b ≠ 0)] at hround
  have hlogab : log (b / a) = log b - log a := log_div (by linarith) (by linarith)
  rw [hlogab] at hbound
  have hsmall : (b - a) / b ≤ log b - log a := by
    have he : a / b - 1 = -(b - a) / b := by
      field_simp
      ring
    rw [he] at hround
    have hbpos : 0 < b := by linarith
    have hn := neg_le_neg hround
    rw [neg_sub] at hn
    convert hn using 1 <;> field_simp [hbpos.ne'] <;> ring
  have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (j : ℝ) / 3 by positivity)
  change b - a ≤ 9 * s * b / j
  apply (le_div_iff₀ hj0).mpr
  have hdiv : (b - a) / b * b = b - a := div_mul_cancel₀ _ (by linarith : b ≠ 0)
  have hmul := mul_le_mul_of_nonneg_right (hh.trans hbound) (show 0 ≤ 3 * b by positivity)
  nlinarith

theorem two_mul_index_le_two_pow {j : ℕ} (hj : 2 ≤ j) : 2 * j ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    rw [pow_succ]
    have hp : 0 < (2 : ℕ) ^ j := Nat.pow_pos (by norm_num)
    nlinarith

/-- Uniform root bound and active-layer bound. j is not fixed as X grows. -/
theorem active_root_bounds {X s : ℝ} (hX : exp 2 ≤ X)
    (hs : 0 < s) (hs2 : s ≤ 1 / 2) {j : ℕ} (hj : 2 ≤ j)
    (hactive : 2 < cutoff j ((1 - s) / (X * log X))) :
    cutoff j ((1 - s) / (X * log X)) ≤ (2 * j * X) ^ (1 / (j : ℝ)) ∧
    (2 * j * X) ^ (1 / (j : ℝ)) ≤ 2 * X ^ (1 / (j : ℝ)) ∧
    (j : ℝ) < 6 * log X := by
  let u := cutoff j ((1 - s) / (X * log X))
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  have hL : 2 ≤ log X := (le_log_iff_exp_le hX0).mpr hX
  have hL0 : 0 < log X := by linarith
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hη : 0 < (1 - s) / (X * log X) :=
    div_pos (by linarith) (mul_pos hX0 hL0)
  have hu : 2 < u := hactive
  have hu0 : 0 < u := by linarith
  have hr := (cutoff_spec hj hη).2.2.1 hactive
  have hβ := beta_le_inv_pow_log hu.le (by omega : 1 ≤ j)
  have hhalf : 1 / (2 * X * log X) ≤ (1 - s) / (X * log X) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * X * log X) (mul_pos hX0 hL0)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * (1 - s) by linarith)
      (mul_pos hX0 hL0).le]
  have hbase : u ^ j * log u ≤ 2 * X * log X := by
    rw [hr] at hβ
    have h := hhalf.trans hβ
    have huL : 0 < log u := log_pos (by linarith)
    exact (one_div_le_one_div (by positivity : 0 < 2 * X * log X)
      (by positivity : 0 < u ^ j * log u)).mp h
  have hpow : u ^ j ≤ 2 * j * X := by
    by_contra! hnot
    have hy : X < u ^ j := by
      have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
      have hh := mul_le_mul_of_nonneg_right hj2 hX0.le
      nlinarith only [hnot, hh, hX0]
    have hlog := log_lt_log hX0 hy
    rw [log_pow] at hlog
    have hm := mul_lt_mul_of_pos_right hnot hL0
    have hm2 := mul_lt_mul_of_pos_left hlog (pow_pos (by linarith : 0 < u) j)
    nlinarith [mul_le_mul_of_nonneg_left hbase hj0.le]
  have hrootpow : u ≤ (2 * j * X) ^ (1 / (j : ℝ)) := by
    have hh := rpow_le_rpow (pow_nonneg (by linarith : 0 ≤ u) j) hpow
      (show 0 ≤ (j : ℝ)⁻¹ by positivity)
    simpa only [one_div, pow_rpow_inv_natCast (by linarith : 0 ≤ u) (by omega : j ≠ 0)] using hh
  have htwo : (2 * (j : ℝ)) ^ (1 / (j : ℝ)) ≤ 2 := by
    have hh : 2 * (j : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast two_mul_index_le_two_pow hj
    have ht := rpow_le_rpow (by positivity : 0 ≤ 2 * (j : ℝ)) hh
      (show 0 ≤ (j : ℝ)⁻¹ by positivity)
    simpa only [one_div, pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2) (by omega : j ≠ 0)] using ht
  have hroot2 : (2 * j * X) ^ (1 / (j : ℝ)) ≤ 2 * X ^ (1 / (j : ℝ)) := by
    rw [mul_rpow (by positivity : 0 ≤ 2 * (j : ℝ)) hX0.le]
    exact mul_le_mul_of_nonneg_right htwo (rpow_nonneg hX0.le _)
  have hlog2 : (1 / 2 : ℝ) < log 2 := by
    have hh := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
    norm_num at hh ⊢
    linarith
  have hβ2 := beta_le_inv_pow_log (by norm_num : (2 : ℝ) ≤ 2) (by omega : 1 ≤ j)
  have hlt : (1 - s) / (X * log X) < beta j 2 := (cutoff_spec hj hη).2.2.2.mpr hactive
  have h2pow : (2 : ℝ) ^ j < 4 * X * log X := by
    have hc := hhalf.trans_lt (hlt.trans_le hβ2)
    have hm := (div_lt_div_iff₀ (by positivity : 0 < 2 * X * log X)
      (by positivity : 0 < (2 : ℝ) ^ j * log 2)).mp hc
    have hmp := mul_lt_mul_of_pos_left hlog2 (pow_pos (by norm_num : (0 : ℝ) < 2) j)
    nlinarith
  have hlogpow := log_lt_log (pow_pos (by norm_num : (0 : ℝ) < 2) j) h2pow
  rw [log_pow, log_mul (by positivity : 4 * X ≠ 0) hL0.ne',
    log_mul (by norm_num : (4 : ℝ) ≠ 0) hX0.ne'] at hlogpow
  have hlog4 : log (4 : ℝ) ≤ 2 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have he : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
      rfl
    linarith
  have hlogL := log_le_sub_one_of_pos hL0
  have hjL : (j : ℝ) < 6 * log X := by
    nlinarith [mul_lt_mul_of_pos_left hlog2 hj0]
  exact ⟨hrootpow, hroot2, hjL⟩

/-- Elementary maximum t exp(-t/6) <= 6/e, without a separate
optimization theorem: log(y/e) <= y/e-1 proves log(y) <= y/e. -/
theorem log_cuberoot_lt_three_sqrt {X : ℝ} (hX : exp 2 ≤ X) :
    log X * X ^ (1 / 3 : ℝ) < 3 * sqrt X := by
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  let y : ℝ := X ^ (1 / 6 : ℝ)
  have hy : 0 < y := rpow_pos_of_pos hX0 _
  have he : 2 < exp 1 := by
    have hh := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have hlog := log_le_sub_one_of_pos (div_pos hy (exp_pos 1))
  rw [log_div hy.ne' (exp_pos 1).ne', log_exp] at hlog
  have hylog : log X / 6 ≤ y / exp 1 := by
    dsimp [y] at hlog
    rw [log_rpow hX0] at hlog
    linarith
  have hfrac : y / exp 1 < y / 2 := div_lt_div_of_pos_left hy (by norm_num) he
  have hsmall : log X < 3 * y := by linarith
  have hmul := mul_lt_mul_of_pos_right hsmall (rpow_pos_of_pos hX0 (1 / 3 : ℝ))
  have hprod : y * X ^ (1 / 3 : ℝ) = sqrt X := by
    dsimp [y]
    rw [← rpow_add hX0]
    norm_num
    exact (sqrt_eq_rpow X).symm
  nlinarith [hprod]

/-- At most length+1 actual integer points, with no prime-density input. -/
theorem integer_interval_card (S : Finset ℕ) {a b : ℝ} (hab : a ≤ b)
    (hS : ∀ p ∈ S, a ≤ (p : ℝ) ∧ (p : ℝ) < b) : (S.card : ℝ) ≤ b - a + 1 := by
  classical
  by_cases hne : S.Nonempty
  · let l := S.min' hne
    let u := S.max' hne
    have hlu : l ≤ u := S.min'_le_max' hne
    have hsub : S ⊆ Icc l u := fun p hp =>
      mem_Icc.mpr ⟨S.min'_le p hp, S.le_max' p hp⟩
    have hc := card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hc' : (S.card : ℝ) ≤ (u : ℝ) + 1 - l := by
      have hh : (S.card : ℝ) ≤ ((u + 1 - l : ℕ) : ℝ) := by exact_mod_cast hc
      rw [Nat.cast_sub (by omega : l ≤ u + 1), Nat.cast_add, Nat.cast_one] at hh
      exact hh
    have hl := (hS l (S.min'_mem hne)).1
    have hu := (hS u (S.max'_mem hne)).2
    linarith
  · simp only [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
    linarith

/-- A finite active layer set, regardless of how it was obtained. -/
theorem active_layer_card {X s : ℝ} (hX : exp 2 ≤ X) (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (J : Finset ℕ) (hJ : ∀ j ∈ J, 2 ≤ j ∧ 2 < cutoff j ((1 - s) / (X * log X))) :
    (J.card : ℝ) ≤ 6 * log X := by
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  have hL : 0 ≤ 6 * log X := by have := (le_log_iff_exp_le hX0).mpr hX; linarith
  have hsub : J ⊆ Icc 1 ⌊6 * log X⌋₊ := by
    intro j hj
    have hjb := (active_root_bounds hX hs hs2 (hJ j hj).1 (hJ j hj).2).2.2
    exact mem_Icc.mpr ⟨by have := (hJ j hj).1; omega, (Nat.le_floor_iff hL).mpr hjb.le⟩
  have hc := card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hnat : J.card ≤ ⌊6 * log X⌋₊ := by omega
  exact (by exact_mod_cast hnat : (J.card : ℝ) ≤ (⌊6 * log X⌋₊ : ℝ)).trans (Nat.floor_le hL)

theorem active_cutoff_sum {X s : ℝ} (hX : exp 2 ≤ X) (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (J : Finset ℕ) (hJ : ∀ j ∈ J, 2 ≤ j ∧ 2 < cutoff j ((1 - s) / (X * log X))) :
    (∑ j ∈ J, cutoff j ((1 - s) / (X * log X)) / j) < 37 * sqrt X := by
  classical
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  have hX1 : 1 ≤ X := by
    have he := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hcard := active_layer_card hX hs hs2 J hJ
  have hterm (j : ℕ) (hj : j ∈ J) :
      cutoff j ((1 - s) / (X * log X)) / j ≤
        (if j = 2 then sqrt X else 0) + 2 * X ^ (1 / 3 : ℝ) := by
    obtain ⟨hj2, hact⟩ := hJ j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hb := (active_root_bounds hX hs hs2 hj2 hact).1.trans
      (active_root_bounds hX hs hs2 hj2 hact).2.1
    by_cases hjEq : j = 2
    · subst j
      norm_num only [↓reduceIte, Nat.cast_ofNat] at hb ⊢
      rw [← sqrt_eq_rpow] at hb
      nlinarith [rpow_nonneg hX0.le (1 / 3 : ℝ)]
    · have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast (show 3 ≤ j by omega)
      have hexp : 1 / (j : ℝ) ≤ 1 / 3 := by
        exact one_div_le_one_div_of_le (by norm_num) hj3
      have hr := rpow_le_rpow_of_exponent_le hX1 hexp
      rw [if_neg hjEq, zero_add]
      apply (div_le_iff₀ hj0).mpr
      have hroot := hb.trans (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith [rpow_nonneg hX0.le (1 / 3 : ℝ)]
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
  have hone : (∑ j ∈ J, if j = 2 then sqrt X else 0) ≤ sqrt X := by
    simp only [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact sqrt_nonneg X
  have hbound := mul_le_mul_of_nonneg_right hcard (show 0 ≤ 2 * X ^ (1 / 3 : ℝ) by positivity)
  have hsmall := log_cuberoot_lt_three_sqrt hX
  linarith
end D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
