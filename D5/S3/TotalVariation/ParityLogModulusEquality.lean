/- GID: D5/S3/TotalVariation/ParityLogModulusEquality
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParityLogModulusEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive-distance equality of the logarithmic parity modulus has a strict attainment threshold. -/

import D5.S3.TotalVariation.ParityLogModulus
import D5.S3.TotalVariation.GroupedParityBias

/-! Equality in the finite-distance bound for affine parity bias recovery. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.TotalVariation.ParityLogModulusEquality

open D5.S3.TotalVariation.Pinsker (totalVariation)
open D5.S3.TotalVariation.ParityLogStability
open D5.S3.TotalVariation.ParityLogModulus
open D5.S3.TotalVariation.GroupedParityBias (law groupBias moment_factor law_from_moments loginvert)

private theorem equality_moment_alignment {A : Type*} [AddCommGroup A] [Fintype A]
    (two : ∀ x : A, x + x = 0) (hcard : 1 < Fintype.card A)
    (p q : A → ℝ) (hmass : ∑ x, p x = ∑ x, q x) (a : A) (e : ℝ) (he : 0 < e)
    (hp : ∀ ψ, e ≤ |moment p ψ|) (hq : ∀ ψ, e ≤ |moment q ψ|)
    (heq :
      let beta : ℝ := ((Fintype.card A : ℝ) - 1) / (Fintype.card A : ℝ)
      |logCoefficient a p - logCoefficient a q| =
        2 * beta * Real.log (1 + totalVariation p q / (beta * e))) :
    let beta : ℝ := ((Fintype.card A : ℝ) - 1) / (Fintype.card A : ℝ)
    let gap := Real.log (1 + totalVariation p q / (beta * e))
    let diff := fun ψ : AddChar A ℂ => sign ψ a *
      (Real.log (|moment p ψ|) - Real.log (|moment q ψ|))
    (∀ ψ : AddChar A ℂ, ψ ≠ 0 →
      |moment p ψ - moment q ψ| = totalVariation p q / beta ∧
        |Real.log (|moment p ψ|) - Real.log (|moment q ψ|)| = gap) ∧
    ((∀ ψ, ψ ≠ 0 → diff ψ = gap) ∨ (∀ ψ, ψ ≠ 0 → diff ψ = -gap)) := by
  classical
  let n : ℝ := Fintype.card A
  let t := (Finset.univ : Finset (AddChar A ℂ)).erase 0
  let d (ψ : AddChar A ℂ) := |moment p ψ - moment q ψ|
  let z (ψ : AddChar A ℂ) := 1 + d ψ / e
  let f (ψ : AddChar A ℂ) := sign ψ a *
    (Real.log |moment p ψ| - Real.log |moment q ψ|)
  have hn₁ : 1 < n := by
    dsimp [n]
    exact_mod_cast hcard
  have hn : 0 < n := by linarith
  have hdenom : 0 < n - 1 := sub_pos.mpr hn₁
  have ht : (t.card : ℝ) = n - 1 := by
    dsimp [t, n]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, AddChar.card_eq,
      Nat.cast_sub (Nat.le_of_lt hcard)]
    norm_num
  have hzero : moment p (0 : AddChar A ℂ) = moment q (0 : AddChar A ℂ) := by
    simpa [moment, sign] using hmass
  have hd_total : ∑ ψ ∈ t, d ψ ≤ n * totalVariation p q := by
    have h := Finset.sum_erase_add Finset.univ d (Finset.mem_univ (0 : AddChar A ℂ))
    change (∑ ψ ∈ t, d ψ) + d 0 = _ at h
    rw [show d 0 = 0 by simp [d, hzero], add_zero] at h
    rw [h]
    exact moment_distance_sum_le two p q hmass
  have hsum_w : ∑ _ψ ∈ t, (n - 1)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ht, mul_inv_cancel₀ hdenom.ne']
  have hz (ψ : AddChar A ℂ) : 0 < z ψ :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (abs_nonneg _) he.le)
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := t) (w := fun _ => (n - 1)⁻¹) (p := z)
    (fun _ _ => inv_nonneg.mpr hdenom.le) hsum_w (fun ψ _ => hz ψ)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  have hmean : (n - 1)⁻¹ * (∑ ψ ∈ t, z ψ) ≤
      1 + totalVariation p q / ((n - 1) / n * e) := by
    have hsum : (∑ ψ ∈ t, z ψ) = n - 1 + (∑ ψ ∈ t, d ψ) / e := by
      dsimp [z]
      rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul, ht,
        mul_one]
    rw [hsum]
    calc
      _ ≤ (n - 1)⁻¹ * (n - 1 + n * totalVariation p q / e) := by
        gcongr
      _ = _ := by field_simp
  have hzavg : 0 < (n - 1)⁻¹ * (∑ ψ ∈ t, z ψ) := by
    apply mul_pos (inv_pos.mpr hdenom)
    have ht_real : 0 < (t.card : ℝ) := by rwa [ht]
    have ht₀ : 0 < t.card := by exact_mod_cast ht_real
    exact Finset.sum_pos (fun ψ _ => hz ψ) (Finset.card_pos.mp ht₀)
  have hlogs : (∑ ψ ∈ t, Real.log (z ψ)) ≤ (n - 1) *
      Real.log (1 + totalVariation p q / ((n - 1) / n * e)) := by
    apply (inv_mul_le_iff₀ hdenom).mp
    exact hj.trans (Real.log_le_log hzavg hmean)
  have hf0 : f 0 = 0 := by simp [f, hzero]
  have hfsum : ∑ ψ : AddChar A ℂ, f ψ = ∑ ψ ∈ t, f ψ := by
    have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : AddChar A ℂ))
    change (∑ ψ ∈ t, f ψ) + f 0 = _ at h
    simpa [hf0] using h.symm
  have hcoef : logCoefficient a p - logCoefficient a q =
      (-2 / n) * ∑ ψ : AddChar A ℂ, f ψ := by
    unfold logCoefficient
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    simp only [f, n, mul_sub]
  let target := 1 + totalVariation p q / ((n - 1) / n * e)
  have hf_bound (ψ : AddChar A ℂ) : |f ψ| ≤ Real.log (z ψ) := by
    rw [show f ψ = _ by rfl, abs_mul, abs_sign two, one_mul]
    exact log_abs_difference_le he (hp ψ) (hq ψ)
  have hpartial : (∑ ψ ∈ t, |f ψ|) ≤ ∑ ψ ∈ t, Real.log (z ψ) :=
    Finset.sum_le_sum fun ψ _ => hf_bound ψ
  have htri := (Finset.abs_sum_le_sum_abs f t).trans hpartial
  have heq' : (2 / n) * |∑ ψ ∈ t, f ψ| = 2 * ((n - 1) / n) * Real.log target := by
    dsimp at heq
    rw [hcoef, hfsum, abs_mul, abs_div, abs_of_pos hn,
      show |(-2 : ℝ)| = 2 by norm_num] at heq
    exact heq
  have hvalue : (n - 1) * Real.log target = |∑ ψ ∈ t, f ψ| := by
    have hpos : 0 < 2 / n := by positivity
    apply (mul_right_inj' hpos.ne').mp
    rw [heq']
    ring
  have hsaturated : (∑ ψ ∈ t, Real.log (z ψ)) = (n - 1) * Real.log target :=
    le_antisymm hlogs (hvalue.le.trans htri)
  have hpw (ψ : AddChar A ℂ) (hψ : ψ ∈ t) : |f ψ| = Real.log (z ψ) := by
    apply le_antisymm (hf_bound ψ)
    by_contra! hlt
    have hsum := Finset.sum_lt_sum (fun i _ => hf_bound i) ⟨ψ, hψ, hlt⟩
    rw [hsaturated, hvalue] at hsum
    exact (not_lt_of_ge (Finset.abs_sum_le_sum_abs f t)) hsum
  let mean := (n - 1)⁻¹ * (∑ ψ ∈ t, z ψ)
  have htgt_log : Real.log target = (n - 1)⁻¹ * (∑ ψ ∈ t, Real.log (z ψ)) := by
    rw [hsaturated, ← mul_assoc, inv_mul_cancel₀ hdenom.ne', one_mul]
  have hlog_eq : Real.log mean = Real.log target := by
    refine le_antisymm (Real.log_le_log hzavg hmean) ?_
    rwa [htgt_log]
  have hmean_eq : mean = target :=
    Real.strictMonoOn_log.injOn hzavg (hzavg.trans_le hmean) hlog_eq
  have hj_eq : Real.log (∑ ψ ∈ t, (n - 1)⁻¹ • z ψ) =
      ∑ ψ ∈ t, (n - 1)⁻¹ • Real.log (z ψ) := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
    exact hlog_eq.trans htgt_log
  have hdist (ψ : AddChar A ℂ) (hψ : ψ ≠ 0) :
      d ψ = totalVariation p q / ((n - 1) / n) := by
    have hz_eq := (strictConcaveOn_log_Ioi.map_sum_eq_iff
      (t := t) (w := fun _ => (n - 1)⁻¹) (p := z)
      (fun _ _ => inv_pos.mpr hdenom) hsum_w (fun j _ => hz j)).mp hj_eq
      ψ (Finset.mem_erase.mpr ⟨hψ, Finset.mem_univ _⟩)
    simp only [smul_eq_mul, ← Finset.mul_sum] at hz_eq
    have hdisplacement : d ψ / e = totalVariation p q / ((n - 1) / n * e) :=
      add_left_cancel (hz_eq.trans hmean_eq)
    rw [div_mul_eq_div_div] at hdisplacement
    exact (div_left_inj' he.ne').mp hdisplacement
  have hlogs_point (ψ : AddChar A ℂ) (hψ : ψ ≠ 0) : |f ψ| = Real.log target := by
    rw [hpw ψ (Finset.mem_erase.mpr ⟨hψ, Finset.mem_univ _⟩)]
    change Real.log (1 + d ψ / e) = _
    rw [hdist ψ hψ]
    simp only [target, div_mul_eq_div_div]
  have hsum_abs : (∑ ψ ∈ t, |f ψ|) = |∑ ψ ∈ t, f ψ| := by
    apply le_antisymm
    · rw [← hvalue, ← hsaturated]
      exact hpartial
    · exact Finset.abs_sum_le_sum_abs f t
  refine ⟨fun ψ hψ => ⟨hdist ψ hψ, ?_⟩, ?_⟩
  · simpa only [f, abs_mul, abs_sign two ψ a, one_mul] using hlogs_point ψ hψ
  · rcases le_total 0 (∑ ψ ∈ t, f ψ) with hsum | hsum
    · left
      intro ψ hψ
      have hequal : f ψ = |f ψ| := by
        apply le_antisymm (le_abs_self _)
        by_contra! hlt
        have hless := Finset.sum_lt_sum (fun j _ => le_abs_self (f j))
          ⟨ψ, Finset.mem_erase.mpr ⟨hψ, Finset.mem_univ _⟩, hlt⟩
        rw [hsum_abs, abs_of_nonneg hsum] at hless
        exact (lt_irrefl _) hless
      exact hequal.trans (hlogs_point ψ hψ)
    · right
      intro ψ hψ
      have hequal : -f ψ = |f ψ| := by
        apply le_antisymm (neg_le_abs _)
        by_contra! hlt
        have hless := Finset.sum_lt_sum (fun j _ => neg_le_abs (f j))
          ⟨ψ, Finset.mem_erase.mpr ⟨hψ, Finset.mem_univ _⟩, hlt⟩
        rw [Finset.sum_neg_distrib, hsum_abs, abs_of_nonpos hsum] at hless
        exact (lt_irrefl _) hless
      linarith [hequal, hlogs_point ψ hψ]

private theorem log_abs_difference_eq_of_pos {e x y : ℝ} (he : 0 < e)
    (hx : e ≤ |x|) (hy : e ≤ |y|) (hd : 0 < |x - y|)
    (h : |Real.log (|x|) - Real.log (|y|)| = Real.log (1 + |x - y| / e)) :
    0 < x * y ∧ (|x| = e ∧ |y| = e + |x - y| ∨ |y| = e ∧ |x| = e + |x - y|) := by
  have ordered {u v : ℝ} (hu : e ≤ |u|) (huv : |u| ≤ |v|)
      (hdv : 0 < |v - u|)
      (hlog : Real.log |v| - Real.log |u| = Real.log (1 + |v - u| / e)) :
      0 < u * v ∧ |u| = e ∧ |v| = e + |v - u| := by
    have hu₀ := he.trans_le hu
    have hv₀ := hu₀.trans_le huv
    have hratio : |v| / |u| = 1 + |v - u| / e := by
      apply Real.strictMonoOn_log.injOn (div_pos hv₀ hu₀)
        (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (abs_nonneg _) he.le))
      rwa [Real.log_div hv₀.ne' hu₀.ne']
    have hr : (|v| - |u|) / |u| = |v - u| / e := by
      calc
        _ = |v| / |u| - 1 := by rw [sub_div, div_self hu₀.ne']
        _ = _ := by rw [hratio]; ring
    have hdle : |v| - |u| ≤ |v - u| :=
      (le_abs_self _).trans (abs_abs_sub_abs_le_abs_sub v u)
    have hdivide : (|v| - |u|) / |u| ≤ |v - u| / |u| :=
      div_le_div_of_nonneg_right hdle hu₀.le
    have hue : |u| = e := by
      by_contra hne
      have hlt := div_lt_div_of_pos_left hdv he (lt_of_le_of_ne hu (Ne.symm hne))
      exact (not_lt_of_ge (hr ▸ hdivide)) hlt
    have hd_eq : |v| - |u| = |v - u| := by
      rw [hue] at hr
      rw [hue]
      exact (div_left_inj' he.ne').mp hr
    have hsign : 0 < u * v := by
      rcases lt_or_gt_of_ne (abs_pos.mp hu₀) with hu_neg | hu_pos
      · rcases lt_or_gt_of_ne (abs_pos.mp hv₀) with hv_neg | hv_pos
        · exact mul_pos_of_neg_of_neg hu_neg hv_neg
        · rw [abs_of_pos hv_pos, abs_of_neg hu_neg, abs_of_pos (sub_pos.mpr
            (hu_neg.trans hv_pos))] at hd_eq
          linarith
      · rcases lt_or_gt_of_ne (abs_pos.mp hv₀) with hv_neg | hv_pos
        · rw [abs_of_neg hv_neg, abs_of_pos hu_pos, abs_of_neg (sub_neg.mpr
            (hv_neg.trans hu_pos))] at hd_eq
          linarith
        · exact mul_pos hu_pos hv_pos
    exact ⟨hsign, hue, by linarith⟩
  rcases le_total (|x|) (|y|) with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.strictMonoOn_log.monotoneOn
        (he.trans_le hx) (he.trans_le hy) hxy)), neg_sub, abs_sub_comm x y] at h
    rw [abs_sub_comm x y] at hd ⊢
    obtain ⟨hs, hmin, hmax⟩ := ordered hx hxy hd h
    exact ⟨hs, Or.inl ⟨hmin, hmax⟩⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn
        (he.trans_le hy) (he.trans_le hx) hyx))] at h
    obtain ⟨hs, hmin, hmax⟩ := ordered hy hyx hd h
    exact ⟨by simpa [mul_comm] using hs, Or.inr ⟨hmin, hmax⟩⟩

private theorem sign_cases {A : Type*} [AddCommGroup A]
    (two : ∀ x : A, x + x = 0) (ψ : AddChar A ℂ) (a : A) :
    sign ψ a = 1 ∨ sign ψ a = -1 := by
  have h := abs_sign two ψ a
  rcases le_total 0 (sign ψ a) with h₀ | h₀
  · exact Or.inl (by simpa [abs_of_nonneg h₀] using h)
  · exact Or.inr (by rw [abs_of_nonpos h₀] at h; linarith)

private theorem coefficient_of_profile {A : Type*} [AddCommGroup A] [Fintype A]
    (p : A → ℝ) (hmass : ∑ x, p x = 1) (a : A) (ha : a ≠ 0) (b h : ℝ)
    (hterm : ∀ ψ : AddChar A ℂ, ψ ≠ 0 →
      sign ψ a * Real.log (|moment p ψ|) =
        b * sign ψ a + h / 2 * (sign ψ a - 1)) :
    logCoefficient a p = 2 * b / (Fintype.card A : ℝ) + h := by
  classical
  let n : ℝ := Fintype.card A
  let t := (Finset.univ : Finset (AddChar A ℂ)).erase 0
  have hn : n ≠ 0 := by positivity
  have hsignall : (∑ ψ : AddChar A ℂ, sign ψ a) = 0 := by
    simpa [sign, Complex.re_sum] using congrArg Complex.re
      ((AddChar.sum_apply_eq_zero_iff_ne_zero (α := A)).mpr ha)
  have hs : (∑ ψ ∈ t, sign ψ a) = -1 := by
    have ht := Finset.sum_erase_add Finset.univ (fun ψ : AddChar A ℂ => sign ψ a)
      (Finset.mem_univ (0 : AddChar A ℂ))
    change (∑ ψ ∈ t, sign ψ a) + sign 0 a = _ at ht
    rw [hsignall, show sign 0 a = 1 by simp [sign]] at ht
    linarith
  have ht : (t.card : ℝ) = n - 1 := by
    dsimp [t, n]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, AddChar.card_eq,
      Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos)]
    norm_num
  have hz : moment p (0 : AddChar A ℂ) = 1 := by simpa [moment, sign] using hmass
  let f (ψ : AddChar A ℂ) := sign ψ a * Real.log (|moment p ψ|)
  have hsum : (∑ ψ : AddChar A ℂ, f ψ) = ∑ ψ ∈ t, f ψ := by
    have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : AddChar A ℂ))
    change (∑ ψ ∈ t, f ψ) + f 0 = _ at h
    simpa [f, hz] using h.symm
  have hp : (∑ ψ ∈ t, f ψ) = -b - h * n / 2 := by
    calc
      _ = ∑ ψ ∈ t, (b * sign ψ a + h / 2 * (sign ψ a - 1)) := by
        apply Finset.sum_congr rfl
        intro ψ hψ
        exact hterm ψ (Finset.mem_erase.mp hψ).1
      _ = b * (∑ ψ ∈ t, sign ψ a) + h / 2 * ((∑ ψ ∈ t, sign ψ a) - (t.card : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib]
        simp
      _ = _ := by rw [hs, ht]; ring
  change (-2 / n) * (∑ ψ : AddChar A ℂ, f ψ) = 2 * b / n + h
  rw [hsum, hp]
  field_simp
  ring

private theorem equality_criterion_necessary {A : Type*} [AddCommGroup A] [Fintype A]
    (two : ∀ x : A, x + x = 0) (hcard : 1 < Fintype.card A)
    (p q : A → ℝ) (hp_mass : ∑ x, p x = 1) (hq_mass : ∑ x, q x = 1)
    (a : A) (ha : a ≠ 0) (e : ℝ) (he : 0 < e)
    (hp : ∀ ψ, e ≤ |moment p ψ|) (hq : ∀ ψ, e ≤ |moment q ψ|)
    (hp_neg : logCoefficient a p < 0) (hq_neg : logCoefficient a q < 0)
    (hd : 0 < totalVariation p q)
    (heq :
      let beta : ℝ := ((Fintype.card A : ℝ) - 1) / (Fintype.card A : ℝ)
      |logCoefficient a p - logCoefficient a q| =
        2 * beta * Real.log (1 + totalVariation p q / (beta * e))) :
    let n : ℝ := Fintype.card A
    let beta := (n - 1) / n
    let gap := Real.log (1 + totalVariation p q / (beta * e))
    Real.log e + n / 2 * gap < 0 ∧
      ∀ ψ : AddChar A ℂ, ψ ≠ 0 → 0 < moment p ψ * moment q ψ := by
  let n : ℝ := Fintype.card A
  let beta := (n - 1) / n
  let d := totalVariation p q / beta
  let gap := Real.log (1 + d / e)
  have hn₁ : 1 < n := by dsimp [n]; exact_mod_cast hcard
  have hn : 0 < n := by linarith
  have hbeta : 0 < beta := div_pos (sub_pos.mpr hn₁) hn
  have hdist : 0 < d := div_pos hd hbeta
  have hgap : 0 < gap := Real.log_pos (lt_add_of_pos_right _ (div_pos hdist he))
  have hformula : Real.log (e + d) = Real.log e + gap := by
    dsimp [gap]
    rw [← Real.log_mul he.ne' (add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg hdist.le he.le)).ne']
    congr 1
    field_simp
  obtain ⟨hdetail, horientation⟩ :=
    equality_moment_alignment two hcard p q (hp_mass.trans hq_mass.symm) a e he hp hq heq
  have hbranch (ψ : AddChar A ℂ) (hψ : ψ ≠ 0) :
      0 < moment p ψ * moment q ψ ∧
        (|moment p ψ| = e ∧ |moment q ψ| = e + d ∨
         |moment q ψ| = e ∧ |moment p ψ| = e + d) := by
    obtain ⟨hdiff, hlog⟩ := hdetail ψ hψ
    change |moment p ψ - moment q ψ| = d at hdiff
    have hpos : 0 < |moment p ψ - moment q ψ| := hdiff ▸ hdist
    have h : |Real.log (|moment p ψ|) - Real.log (|moment q ψ|)| =
        Real.log (1 + |moment p ψ - moment q ψ| / e) := by
      rw [hdiff]
      simpa only [d, beta, n, div_mul_eq_div_div] using hlog
    simpa only [hdiff] using log_abs_difference_eq_of_pos he (hp ψ) (hq ψ) hpos h
  have hordered (r s : A → ℝ) (hs_mass : ∑ x, s x = 1) (hs_lt : logCoefficient a s < 0)
      (halign : ∀ ψ : AddChar A ℂ, ψ ≠ 0 →
        sign ψ a * (Real.log (|moment r ψ|) - Real.log (|moment s ψ|)) = gap)
      (hvalues : ∀ ψ : AddChar A ℂ, ψ ≠ 0 →
        (|moment r ψ| = e ∧ |moment s ψ| = e + d ∨
         |moment s ψ| = e ∧ |moment r ψ| = e + d)) :
      Real.log e + n / 2 * gap < 0 := by
    have ht := coefficient_of_profile s hs_mass a ha (Real.log e) gap (by
      intro ψ hψ
      have hh := halign ψ hψ
      rcases sign_cases two ψ a with hsign | hsign <;>
        rcases hvalues ψ hψ with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;>
        rw [hsign, hlo, hhi, hformula] at hh <;>
        simp only [hsign, hlo, hhi, hformula] <;> linarith)
    change logCoefficient a s = 2 * Real.log e / n + gap at ht
    rw [ht] at hs_lt
    have hm := mul_neg_of_pos_of_neg hn hs_lt
    rw [mul_add, show n * (2 * Real.log e / n) = 2 * Real.log e by field_simp] at hm
    nlinarith
  change Real.log e + n / 2 * Real.log (1 + totalVariation p q / (beta * e)) < 0 ∧ _
  rw [div_mul_eq_div_div]
  change Real.log e + n / 2 * gap < 0 ∧ _
  refine ⟨?_, fun ψ hψ => (hbranch ψ hψ).1⟩
  rcases horientation with hs | hs
  · apply hordered p q hq_mass hq_neg
    · intro ψ hψ
      simpa [gap, d, beta, n, div_mul_eq_div_div] using hs ψ hψ
    · exact fun ψ hψ => (hbranch ψ hψ).2
  · apply hordered q p hp_mass hp_neg
    · intro ψ hψ
      have h : sign ψ a * (Real.log (|moment p ψ|) - Real.log (|moment q ψ|)) = -gap := by
        simpa only [gap, d, beta, n, div_mul_eq_div_div] using hs ψ hψ
      rw [← neg_sub, mul_neg, h, neg_neg]
    · intro ψ hψ
      exact (hbranch ψ hψ).2.symm

private theorem log_cutoff_iff {e n r : ℝ} (he : 0 < e) (hr : 0 < r) :
    Real.log e + n / 2 * Real.log r < 0 ↔ e * r ^ (n / 2) < 1 := by
  rw [Real.rpow_def_of_pos hr, mul_comm (Real.log r) (n / 2), ← Real.exp_log he,
    ← Real.exp_add, Real.exp_lt_one_iff, Real.log_exp]

open Classical in
/-- Equality at positive distance requires the strict threshold
and agreement of the affine offsets. -/
theorem equality_requires_cutoff_and_offset {A I : Type*}
    [AddCommGroup A] [Fintype A] [Fintype I]
    (two : ∀ x : A, x + x = 0) (hcard : 1 < Fintype.card A)
    (c : I → A) (s t a : A) (ha : a ≠ 0) (hcol : ∃ i, c i = a)
    (f g : I → ℝ) (hf : ∀ i, 0 < f i ∧ f i < 1) (hg : ∀ i, 0 < g i ∧ g i < 1)
    (e : ℝ) (he : 0 < e)
    (hp : ∀ ψ, e ≤ |moment (law c s f) ψ|) (hq : ∀ ψ, e ≤ |moment (law c t g) ψ|)
    (hd : 0 < totalVariation (law c s f) (law c t g))
    (heq :
      let n : ℝ := Fintype.card A
      let beta := (n - 1) / n
      |Real.log (groupBias c f a) - Real.log (groupBias c g a)| =
        2 * beta * Real.log (1 + totalVariation (law c s f) (law c t g) / (beta * e))) :
    let n : ℝ := Fintype.card A
    let beta := (n - 1) / n
    e * (1 + totalVariation (law c s f) (law c t g) / (beta * e)) ^ (n / 2) < 1 ∧ s = t := by
  intro n beta
  let p := law c s f
  let q := law c t g
  have hfactor (u : A) (v : I → ℝ) (ψ : AddChar A ℂ) :
      moment (law c u v) ψ = sign ψ u * ∏ x with sign ψ x = -1, groupBias c v x :=
    moment_factor two c u v ψ
  have hmass (u : A) (v : I → ℝ) : (∑ x, law c u v x) = 1 := by
    simpa [moment, sign, show (1 : ℝ) ≠ -1 by norm_num] using hfactor u v 0
  have hgroup_pos (v : I → ℝ) (hv : ∀ i, 0 < v i ∧ v i < 1) (x : A) :
      0 < groupBias c v x := Finset.prod_pos fun i _ => (hv i).1
  have hcoeff (v : I → ℝ) (hv : ∀ i, 0 < v i ∧ v i < 1) (u : A) :
      Real.log (groupBias c v a) = logCoefficient a (law c u v) :=
    loginvert two c u v (fun i => (hv i).1) a ha
  have hneg (v : I → ℝ) (hv : ∀ i, 0 < v i ∧ v i < 1) (u : A) :
      logCoefficient a (law c u v) < 0 := by
    rw [← hcoeff v hv u]
    apply Real.log_neg (hgroup_pos v hv a)
    obtain ⟨i, hi⟩ := hcol
    unfold groupBias
    simpa using Finset.prod_lt_prod_of_nonempty₀ (f := v) (g := fun _ => (1 : ℝ))
      (fun j _ => (hv j).1) (fun j _ => (hv j).2)
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have htight : |logCoefficient a p - logCoefficient a q| =
      2 * beta * Real.log (1 + totalVariation p q / (beta * e)) := by
    rw [← hcoeff f hf s, ← hcoeff g hg t]
    exact heq
  obtain ⟨hcut, hphase⟩ := equality_criterion_necessary two hcard p q
    (hmass s f) (hmass t g) a ha e he hp hq (hneg f hf s) (hneg g hg t) hd htight
  have hn : 1 < n := by dsimp [n]; exact_mod_cast hcard
  have hβ : 0 < beta := div_pos (sub_pos.mpr hn) (by linarith)
  have hr : 0 < 1 + totalVariation p q / (beta * e) :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_pos hd (mul_pos hβ he)).le
  refine ⟨(log_cutoff_iff he hr).mp hcut, AddChar.doubleDualEmb_injective ?_⟩
  ext ψ
  change ψ s = ψ t
  by_cases hψ : ψ = 0
  · simp [hψ]
  have hprod (v : I → ℝ) (hv : ∀ i, 0 < v i ∧ v i < 1) :
      0 < ∏ x with sign ψ x = -1, groupBias c v x :=
    Finset.prod_pos fun x _ => hgroup_pos v hv x
  have h := hphase ψ hψ
  change 0 < moment (law c s f) ψ * moment (law c t g) ψ at h
  rw [hfactor, hfactor] at h
  have cases (u : A) : ψ u = 1 ∨ ψ u = -1 := by
    apply mul_self_eq_one_iff.mp
    rw [← AddChar.map_add_eq_mul, two, AddChar.map_zero_eq_one]
  rcases cases s with hs | hs <;> rcases cases t with ht | ht
  · rw [hs, ht]
  · have hs' : sign ψ s = 1 := by simp [sign, hs]
    have ht' : sign ψ t = -1 := by simp [sign, ht]
    rw [hs', ht', one_mul, neg_one_mul] at h
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (hprod f hf).le
      (neg_nonpos.mpr (hprod g hg).le)) h).elim
  · have hs' : sign ψ s = -1 := by simp [sign, hs]
    have ht' : sign ψ t = 1 := by simp [sign, ht]
    rw [hs', ht', neg_one_mul, one_mul] at h
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hprod f hf).le)
      (hprod g hg).le) h).elim
  · rw [hs, ht]

variable {A : Type*} [AddCommGroup A] [Fintype A]

private theorem sum_eval_eq_zero (ψ : AddChar A ℂ) (hψ : ψ ≠ 0) :
    (∑ c : A, sign ψ c) = 0 := by
  simpa [sign, Complex.re_sum] using congrArg Complex.re
    ((AddChar.sum_eq_zero_iff_ne_zero (ψ := ψ)).mpr hψ)

open Classical in
private theorem negative_count (two : ∀ x : A, x + x = 0)
    (ψ : AddChar A ℂ) (hψ : ψ ≠ 0) :
    (((Finset.univ : Finset A).filter fun c => sign ψ c = -1).card : ℝ) =
      (Fintype.card A : ℝ) / 2 := by
  calc
    _ = ∑ c : A, if sign ψ c = -1 then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ c : A, (1 - sign ψ c) / 2 := by
      apply Finset.sum_congr rfl
      intro c _
      rcases sign_cases two ψ c with h | h <;> norm_num [h]
    _ = _ := by rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_eval_eq_zero ψ hψ]; simp

open Classical in
private theorem groupBias_subtype (f : {x : A // x ≠ 0} → ℝ) (c : A) (hc : c ≠ 0) :
    groupBias (Subtype.val : {x : A // x ≠ 0} → A) f c = f ⟨c, hc⟩ := by
  unfold groupBias
  rw [Finset.prod_eq_single ⟨c, hc⟩]
  · intro i hi hne
    exact (hne (Subtype.ext (Finset.mem_filter.mp hi).2)).elim
  · simp

open Classical in
private theorem moment_of_perturbed_factors (two : ∀ x : A, x + x = 0)
    (a : A) (b k : ℝ) (ψ : AddChar A ℂ) (hψ : ψ ≠ 0) :
    let c : {x : A // x ≠ 0} → A := Subtype.val
    let f : {x : A // x ≠ 0} → ℝ := fun i => Real.exp (b + if i.val = a then k else 0)
    moment (law c 0 f) ψ =
      Real.exp ((Fintype.card A : ℝ) / 2 * b + if sign ψ a = -1 then k else 0) := by
  intro c f
  have h := moment_factor two c 0 f ψ
  change moment (law c 0 f) ψ =
    sign ψ 0 * ∏ x with sign ψ x = -1, groupBias c f x at h
  rw [h, show sign ψ 0 = 1 by simp [sign], one_mul]
  let t := (Finset.univ : Finset A).filter fun x => sign ψ x = -1
  change (∏ x ∈ t, groupBias c f x) = _
  calc
    _ = ∏ x ∈ t, Real.exp (b + if x = a then k else 0) := by
      apply Finset.prod_congr rfl
      intro x hx
      have hne : x ≠ 0 := by
        intro h
        have hs := (Finset.mem_filter.mp hx).2
        rw [h] at hs
        norm_num [sign] at hs
      exact groupBias_subtype f x hne
    _ = _ := by
      rw [← Real.exp_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      change Real.exp (((t.card : ℕ) : ℝ) * b + ∑ x ∈ t, if x = a then k else 0) = _
      have hx : a ∈ t ↔ sign ψ a = -1 := by simp [t]
      rw [show (t.card : ℝ) = (Fintype.card A : ℝ) / 2 from negative_count two ψ hψ,
        Finset.sum_ite_eq']
      simp only [hx]

open Classical in
private theorem law_mass_one (two : ∀ x : A, x + x = 0)
    (f : {x : A // x ≠ 0} → ℝ) :
    (∑ x, law (Subtype.val : {x : A // x ≠ 0} → A) 0 f x) = 1 := by
  classical
  have h := moment_factor two (Subtype.val : {x : A // x ≠ 0} → A) 0 f (0 : AddChar A ℂ)
  change moment (law (Subtype.val : {x : A // x ≠ 0} → A) 0 f) (0 : AddChar A ℂ) =
    sign (0 : AddChar A ℂ) (0 : A) *
      ∏ x with sign (0 : AddChar A ℂ) x = -1,
        groupBias (Subtype.val : {x : A // x ≠ 0} → A) f x at h
  simpa [moment, sign, show (1 : ℝ) ≠ -1 by norm_num] using h

open Classical in
private theorem difference_from_profile (two : ∀ x : A, x + x = 0)
    (p q : A → ℝ) (hmass : ∑ x, p x = ∑ x, q x) (a : A) (d : ℝ)
    (hprofile : ∀ ψ : AddChar A ℂ, ψ ≠ 0 → moment p ψ - moment q ψ = d * sign ψ a) :
    ∀ x : A, p x - q x = d * ((if x = a then 1 else 0) - 1 / (Fintype.card A : ℝ)) := by
  let n : ℝ := Fintype.card A
  let u (x : A) := p x - q x
  let v (x : A) := d * ((if x = a then 1 else 0) - 1 / n)
  have hproj (ψ : AddChar A ℂ) : moment u ψ = moment p ψ - moment q ψ := by
    simp only [moment, u, sub_mul, Finset.sum_sub_distrib]
  have hv (ψ : AddChar A ℂ) :
      moment v ψ = d * (sign ψ a - (1 / n) * ∑ x : A, sign ψ x) := by
    dsimp [moment, v]
    simp_rw [mul_assoc, sub_mul, ← Finset.mul_sum, Finset.sum_sub_distrib]
    congr 2
    · simp_rw [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      simp
    · rw [Finset.mul_sum]
  have hsame (ψ : AddChar A ℂ) : moment u ψ = moment v ψ := by
    rw [hproj, hv]
    by_cases hψ : ψ = 0
    · subst ψ
      have hn : n ≠ 0 := by positivity
      have hsum : (∑ x : A, sign (0 : AddChar A ℂ) x) = n := by simp [sign, n]
      have h0 : moment p (0 : AddChar A ℂ) = moment q (0 : AddChar A ℂ) := by
        simpa [moment, sign] using hmass
      rw [h0, sub_self, hsum, one_div, inv_mul_cancel₀ hn]
      simp [sign]
    · rw [hprofile ψ hψ, sum_eval_eq_zero ψ hψ, mul_zero, sub_zero]
  exact congrFun (law_from_moments two u v hsame)

open Classical in
private theorem tv_of_profile (p q : A → ℝ) (a : A) (d : ℝ) (hd : 0 < d)
    (hcard : 1 < Fintype.card A)
    (h : ∀ x : A, p x - q x = d * ((if x = a then 1 else 0) - 1 / (Fintype.card A : ℝ))) :
    totalVariation p q = ((Fintype.card A : ℝ) - 1) / (Fintype.card A : ℝ) * d := by
  let n : ℝ := Fintype.card A
  have hn₁ : 1 < n := by dsimp [n]; exact_mod_cast hcard
  have hn : 0 < n := by linarith
  have hle : 0 ≤ 1 - 1 / n := sub_nonneg.mpr (div_le_one_of_le₀ hn₁.le hn.le)
  let f (x : A) : ℝ := |(if x = a then 1 else 0) - 1 / n|
  have hterm : f a = 1 - 1 / n := by
    simp only [f, ite_true, abs_of_nonneg hle]
  have hothers : ∀ x ∈ Finset.univ.erase a, f x = 1 / n := by
    intro x hx
    simp only [f, (Finset.mem_erase.mp hx).1, ite_false, zero_sub, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ 1 / n)]
  have hsum : (∑ x : A, f x) = (n - 1) * (1 / n) + (1 - 1 / n) := by
    have hsum := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
    rw [hterm] at hsum
    rw [← hsum, Finset.sum_congr rfl hothers, Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Nat.cast_sub (Nat.le_of_lt hcard)]
    simp [n]
  unfold totalVariation
  simp_rw [h, abs_mul, abs_of_pos hd, ← Finset.mul_sum]
  change (1 / 2) * (d * ∑ x : A, f x) = _
  rw [hsum]
  field_simp [hn.ne']
  ring

open Classical in
/-- One independent input per nonzero column attains the modulus at every
positive distance below the strict threshold, with both offsets zero. -/
theorem equality_criterion_sufficient (two : ∀ x : A, x + x = 0) (hcard : 1 < Fintype.card A)
    (a : A) (ha : a ≠ 0) (e δ : ℝ) (he : 0 < e) (hδ : 0 < δ)
    (hcut :
      let n : ℝ := Fintype.card A
      let beta := (n - 1) / n
      e * (1 + δ / (beta * e)) ^ (n / 2) < 1) :
    let n : ℝ := Fintype.card A
    let beta := (n - 1) / n
    let c : {x : A // x ≠ 0} → A := Subtype.val
    ∃ f g : {x : A // x ≠ 0} → ℝ,
      (∀ i, 0 < f i ∧ f i < 1) ∧ (∀ i, 0 < g i ∧ g i < 1) ∧
      let p := law c 0 f
      let q := law c 0 g
      (∀ ψ, e ≤ |moment p ψ| ∧ e ≤ |moment q ψ|) ∧ totalVariation p q = δ ∧
      |Real.log (groupBias c f a) - Real.log (groupBias c g a)| =
        2 * beta * Real.log (1 + δ / (beta * e)) := by
  intro n beta c
  let d := δ / beta
  let h := Real.log (1 + d / e)
  let b := Real.log e
  have hn₁ : 1 < n := by dsimp [n]; exact_mod_cast hcard
  have hn : 0 < n := by linarith
  have hbeta : 0 < beta := div_pos (sub_pos.mpr hn₁) hn
  have hd : 0 < d := div_pos hδ hbeta
  have hh : 0 < h := Real.log_pos (lt_add_of_pos_right _ (div_pos hd he))
  have hcut' : b + n / 2 * h < 0 := by
    have hr : 0 < 1 + δ / (beta * e) :=
      add_pos_of_pos_of_nonneg zero_lt_one (div_pos hδ (mul_pos hbeta he)).le
    simpa only [h, b, d, div_mul_eq_div_div] using (log_cutoff_iff he hr).mpr hcut
  have hbase : 2 * b / n + h < 0 := by
    apply (mul_lt_mul_iff_right₀ hn).mp
    rw [mul_zero, mul_add, mul_div_cancel₀ _ hn.ne']
    linarith
  have hneg : 2 * b / n < 0 := by linarith
  have hneg' : 2 * (b + h) / n < 0 := by
    apply (mul_lt_mul_iff_right₀ hn).mp
    rw [mul_zero, mul_div_cancel₀ _ hn.ne']
    have hn₂ : 2 ≤ n := by
      dsimp [n]
      exact_mod_cast (Nat.succ_le_of_lt hcard)
    have horder : 1 ≤ n / 2 := by linarith
    have hv := mul_le_mul_of_nonneg_right horder hh.le
    linarith
  let f (i : {x : A // x ≠ 0}) := Real.exp (2 * (b + h) / n + if i.val = a then -h else 0)
  let g (i : {x : A // x ≠ 0}) := Real.exp (2 * b / n + if i.val = a then h else 0)
  refine ⟨f, g, ?_, ?_, ?_⟩
  · intro i
    refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr ?_⟩
    dsimp [f]
    split <;> linarith
  · intro i
    refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr ?_⟩
    dsimp [g]
    split <;> linarith
  let p := law c 0 f
  let q := law c 0 g
  have he_exp : Real.exp b = e := Real.exp_log he
  have hbe : Real.exp (b + h) = e + d := by
    rw [Real.exp_add, he_exp, Real.exp_log (add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg hd.le he.le))]
    field_simp
  have hp_mass : ∑ x, p x = 1 := law_mass_one two f
  have hq_mass : ∑ x, q x = 1 := law_mass_one two g
  have hlo : e ≤ 1 := by
    have hb : b < 0 := by
      have hv := mul_pos (div_pos hn (show 0 < (2 : ℝ) by norm_num)) hh
      linarith
    rw [← he_exp]
    exact (Real.exp_lt_one_iff.mpr hb).le
  have hvalues (ψ : AddChar A ℂ) (hψ : ψ ≠ 0) :
      moment p ψ = (if sign ψ a = -1 then e else e + d) ∧
      moment q ψ = (if sign ψ a = -1 then e + d else e) := by
    have hp := moment_of_perturbed_factors two a (2 * (b + h) / n) (-h) ψ hψ
    have hq := moment_of_perturbed_factors two a (2 * b / n) h ψ hψ
    change moment p ψ = Real.exp (n / 2 * (2 * (b + h) / n) +
      if sign ψ a = -1 then -h else 0) at hp
    change moment q ψ = Real.exp (n / 2 * (2 * b / n) +
      if sign ψ a = -1 then h else 0) at hq
    rw [show n / 2 * (2 * (b + h) / n) = b + h by field_simp] at hp
    rw [show n / 2 * (2 * b / n) = b by field_simp] at hq
    by_cases hs : sign ψ a = -1
    · simp only [hs, ite_true] at hp hq ⊢
      rw [show b + h + -h = b by ring, he_exp] at hp
      exact ⟨hp, hq.trans hbe⟩
    · simp only [hs, ite_false, add_zero] at hp hq ⊢
      exact ⟨hp.trans hbe, hq.trans he_exp⟩
  change (∀ ψ, e ≤ |moment p ψ| ∧ e ≤ |moment q ψ|) ∧ totalVariation p q = δ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro ψ
    by_cases hψ : ψ = 0
    · subst ψ
      have hp0 : moment p (0 : AddChar A ℂ) = 1 := by simpa [moment, sign] using hp_mass
      have hq0 : moment q (0 : AddChar A ℂ) = 1 := by simpa [moment, sign] using hq_mass
      rw [hp0, hq0, abs_one]
      exact ⟨hlo, hlo⟩
    · rw [(hvalues ψ hψ).1, (hvalues ψ hψ).2]
      by_cases hs : sign ψ a = -1
      all_goals simp [hs, abs_of_pos he, abs_of_pos (add_pos he hd), hd.le]
  · have hdiff : ∀ ψ : AddChar A ℂ, ψ ≠ 0 → moment p ψ - moment q ψ = d * sign ψ a := by
      intro ψ hψ
      rw [(hvalues ψ hψ).1, (hvalues ψ hψ).2]
      rcases sign_cases two ψ a with hs | hs <;> norm_num [hs]
    have ht := tv_of_profile p q a d hd hcard
      (difference_from_profile two p q (hp_mass.trans hq_mass.symm) a d hdiff)
    change totalVariation p q = beta * d at ht
    rw [ht]
    exact mul_div_cancel₀ δ hbeta.ne'
  · rw [groupBias_subtype f a ha, groupBias_subtype g a ha]
    simp only [f, g, ite_true, Real.log_exp]
    have hdiff : 2 * (b + h) / n + -h - (2 * b / n + h) = -(2 * beta * h) := by
      dsimp [beta]
      field_simp
      ring
    rw [hdiff, abs_neg, abs_of_pos (by positivity : 0 < 2 * beta * h)]
    simp only [h, d, div_mul_eq_div_div]

end D5.S3.TotalVariation.ParityLogModulusEquality
