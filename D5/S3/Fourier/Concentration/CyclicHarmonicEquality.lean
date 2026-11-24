/- GID: D5/S3/Fourier/Concentration/CyclicHarmonicEquality
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CyclicHarmonicEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classify saturation of the first Fourier mode when the second vanishes. -/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Finset

namespace D5.S3.Fourier.Concentration.CyclicHarmonicEquality

private theorem first_moment_projection_variance
    {J : Type*} [Fintype J] (z : J → ℂ) (w : J → ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hw : ∑ j, w j = 1)
    (hsecond : ∑ j, (w j : ℂ) * z j ^ 2 = 0) :
    let m := ∑ j, (w j : ℂ) * z j
    let c := ‖m‖ ^ 2
    ∑ j, w j * ((star m * z j).re - c) ^ 2 = c / 2 - c ^ 2 := by
  let m : ℂ := ∑ j, (w j : ℂ) * z j
  let c : ℝ := ‖m‖ ^ 2
  let X (j : J) := star m * z j
  change ∑ j, w j * ((X j).re - c) ^ 2 = c / 2 - c ^ 2
  have hcx : (c : ℂ) = star m * m := by
    simpa [c, Complex.ofReal_pow] using (Complex.conj_mul' m).symm
  have hcomplex : ∑ j, (w j : ℂ) * X j = (c : ℂ) := by
    rw [hcx]
    simp_rw [X, mul_left_comm (↑(w _) : ℂ) (star m), ← mul_sum]
    rfl
  have hfirstRe : ∑ j, w j * (X j).re = c := by
    simpa [Complex.re_sum, Complex.mul_re] using congrArg Complex.re hcomplex
  have hsecondX : ∑ j, (w j : ℂ) * X j ^ 2 = 0 := by
    simp_rw [X, mul_pow, mul_left_comm (↑(w _) : ℂ) (star m ^ 2), ← mul_sum, hsecond, mul_zero]
  have hsecondRe : ∑ j, w j * (X j ^ 2).re = 0 := by
    simpa [Complex.re_sum, Complex.mul_re] using congrArg Complex.re hsecondX
  have hnorm (j : J) : Complex.normSq (X j) = c := by
    rw [Complex.normSq_eq_norm_sq]
    simp [X, hz, c]
  have hpoint (j : J) : (X j).re ^ 2 = (c + (X j ^ 2).re) / 2 := by
    have h := hnorm j
    rw [Complex.normSq_apply] at h
    have hp : (X j ^ 2).re =
        (X j).re * (X j).re - (X j).im * (X j).im := by
      rw [pow_two, Complex.mul_re]
    nlinarith only [h, hp]
  have hsecondReal : ∑ j, w j * (X j).re ^ 2 = c / 2 := by
    calc
      _ = ∑ j, (w j * c + w j * (X j ^ 2).re) / 2 := by
        exact sum_congr rfl fun j _ => by rw [hpoint]; ring
      _ = c / 2 := by
        simp_rw [div_eq_mul_inv, ← sum_mul, sum_add_distrib, ← sum_mul, hw, hsecondRe]
        ring
  calc
    _ = ∑ j, (w j * (X j).re ^ 2 - (2 * c) * (w j * (X j).re) + w j * c ^ 2) :=
      sum_congr rfl fun j _ => by ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hfirstRe, hsecondReal, hw]
      ring

private theorem first_moment_le_half_and_projection
    {J : Type*} [Fintype J] (z : J → ℂ) (w : J → ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hw : ∑ j, w j = 1) (hpos : ∀ j, 0 ≤ w j)
    (hsecond : ∑ j, (w j : ℂ) * z j ^ 2 = 0) :
    let m := ∑ j, (w j : ℂ) * z j
    ‖m‖ ^ 2 ≤ 1 / 2 ∧
      (‖m‖ ^ 2 = 1 / 2 → ∀ j, 0 < w j →
        (star m * z j).re = 1 / 2 ∧
          ((star m * z j).im = 1 / 2 ∨ (star m * z j).im = -(1 / 2))) := by
  let m := ∑ j, (w j : ℂ) * z j
  let c := ‖m‖ ^ 2
  let X (j : J) := star m * z j
  change c ≤ 1 / 2 ∧ (c = 1 / 2 → ∀ j, 0 < w j →
    (X j).re = 1 / 2 ∧ ((X j).im = 1 / 2 ∨ (X j).im = -(1 / 2)))
  have hvar := first_moment_projection_variance z w hz hw hsecond
  change ∑ j, w j * ((X j).re - c) ^ 2 = c / 2 - c ^ 2 at hvar
  have hterms (j : J) : 0 ≤ w j * ((X j).re - c) ^ 2 :=
    mul_nonneg (hpos j) (sq_nonneg _)
  constructor
  · have h : 0 ≤ ∑ j, w j * ((X j).re - c) ^ 2 := sum_nonneg fun j _ => hterms j
    rw [hvar] at h
    by_contra! hlt
    have hc : 0 < c := by linarith
    have hprod : c * (1 / 2 - c) < 0 := mul_neg_of_pos_of_neg hc (by linarith)
    nlinarith only [h, hprod]
  · intro heq j hj
    have hsum : ∑ j, w j * ((X j).re - c) ^ 2 = 0 := by
      rw [hvar, heq]
      norm_num
    have hterm := (sum_eq_zero_iff_of_nonneg (fun j _ => hterms j)).mp hsum j (mem_univ j)
    have hre : (X j).re = 1 / 2 := by
      have hs := (mul_eq_zero.mp hterm).resolve_left hj.ne'
      exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hs)).trans heq
    refine ⟨hre, ?_⟩
    have hn : Complex.normSq (X j) = c := by
      rw [Complex.normSq_eq_norm_sq]
      simp [X, hz, c]
    rw [Complex.normSq_apply, hre, heq] at hn
    have hfactor : ((X j).im - 1 / 2) * ((X j).im + 1 / 2) = 0 := by nlinarith only [hn]
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linarith only [h])

private theorem equality_two_weights
    {J : Type*} [Fintype J] [DecidableEq J] (z : J → ℂ) (w : J → ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hinj : Function.Injective z)
    (hw : ∑ j, w j = 1) (hpos : ∀ j, 0 ≤ w j)
    (hsecond : ∑ j, (w j : ℂ) * z j ^ 2 = 0)
    (heq : ‖∑ j, (w j : ℂ) * z j‖ ^ 2 = 1 / 2) :
    ∃ a b : J, a ≠ b ∧ z b = Complex.I * z a ∧
      w a = 1 / 2 ∧ w b = 1 / 2 ∧ ∀ j, j ≠ a → j ≠ b → w j = 0 := by
  let m := ∑ j, (w j : ℂ) * z j
  let X (j : J) := star m * z j
  have hm : m ≠ 0 := by
    intro hz
    change ‖m‖ ^ 2 = 1 / 2 at heq
    rw [hz] at heq
    norm_num at heq
  have hX : Function.Injective X := by
    intro j k h
    exact hinj (mul_left_cancel₀ (star_ne_zero.mpr hm) h)
  have hproj := (first_moment_le_half_and_projection z w hz hw hpos hsecond).2 heq
  change ∀ j, 0 < w j → (X j).re = 1 / 2 ∧
    ((X j).im = 1 / 2 ∨ (X j).im = -(1 / 2)) at hproj
  have hsumX : ∑ j, (w j : ℂ) * X j = ((1 / 2 : ℝ) : ℂ) := by
    change ‖m‖ ^ 2 = 1 / 2 at heq
    have hmul : star m * m = ((1 / 2 : ℝ) : ℂ) := by
      simpa [← Complex.ofReal_pow, heq] using Complex.conj_mul' m
    rw [← hmul]
    simp_rw [X, mul_left_comm (↑(w _) : ℂ) (star m), ← mul_sum]
    rfl
  have hsumIm : ∑ j, w j * (X j).im = 0 := by
    simpa [Complex.im_sum, Complex.mul_im] using congrArg Complex.im hsumX
  have hex (sgn : ℝ) (hs : sgn = 1 / 2 ∨ sgn = -(1 / 2)) :
      ∃ j, 0 < w j ∧ (X j).im = sgn := by
    by_contra! hn
    have hall (j : J) : w j * (X j).im = w j * -sgn := by
      rcases (hpos j).eq_or_lt with h | h
      · simp [← h]
      · have hcase := (hproj j h).2
        have him := hn j h
        rcases hs with hs | hs
        · rw [hs] at him ⊢
          rw [hcase.resolve_left him]
        · rw [hs] at him ⊢
          rw [hcase.resolve_right him, neg_neg]
    have hval : (∑ j, w j * (X j).im) = -sgn := by
      simp_rw [hall, ← sum_mul, hw, one_mul]
    rw [hsumIm] at hval
    rcases hs with hs | hs <;> linarith
  obtain ⟨a, ha, haIm⟩ := hex (-(1 / 2)) (Or.inr rfl)
  obtain ⟨b, hb, hbIm⟩ := hex (1 / 2) (Or.inl rfl)
  have hab : a ≠ b := by intro h; rw [h] at haIm; linarith
  have haRe := (hproj a ha).1
  have hbRe := (hproj b hb).1
  have hzRelation : X b = Complex.I * X a := by
    apply Complex.ext
    · simp [Complex.mul_re, haIm, hbRe]
    · simp [Complex.mul_im, haRe, hbIm]
  have hz' : z b = Complex.I * z a := by
    apply mul_left_cancel₀ (star_ne_zero.mpr hm)
    change X b = star m * (Complex.I * z a)
    rw [hzRelation]
    simp [X, mul_left_comm]
  have hzero (j : J) (hja : j ≠ a) (hjb : j ≠ b) : w j = 0 := by
    rcases (hpos j).eq_or_lt with h | h
    · exact h.symm
    · obtain ⟨hjRe, hjIm | hjIm⟩ := hproj j h
      · exact (hjb (hX (Complex.ext (hjRe.trans hbRe.symm) (hjIm.trans hbIm.symm)))).elim
      · exact (hja (hX (Complex.ext (hjRe.trans haRe.symm) (hjIm.trans haIm.symm)))).elim
  have hab' : a ∉ ({b} : Finset J) := by simpa using hab
  have hmass : w a + w b = 1 := by
    rw [← hw, ← sum_subset (subset_univ ({a, b} : Finset J))
      (fun j _ hj => hzero j (fun eq => hj (by simp [eq])) (fun eq => hj (by simp [eq]))),
      sum_insert hab', sum_singleton]
  have hbal : w a * (X a).im + w b * (X b).im = 0 := by
    rw [← hsumIm, ← sum_subset (subset_univ ({a, b} : Finset J))
      (fun j _ hj => mul_eq_zero.mpr (Or.inl
        (hzero j (fun eq => hj (by simp [eq])) (fun eq => hj (by simp [eq]))))),
      sum_insert hab', sum_singleton]
  rw [haIm, hbIm] at hbal
  exact ⟨a, b, hab, hz', by linarith, by linarith, hzero⟩

private theorem order_four_of_character_i {q : ℕ} [NeZero q] (d : ZMod q)
    (h : ZMod.stdAddChar d = Complex.I) : addOrderOf d = 4 := by
  let χ := (ZMod.stdAddChar (N := q))
  have h4 : 4 • d = 0 := by
    apply ZMod.injective_stdAddChar
    change χ (4 • d) = χ 0
    rw [AddChar.map_nsmul_eq_pow, h, Complex.I_pow_four, AddChar.map_zero_eq_one]
  have h2 : 2 • d ≠ 0 := by
    intro hz
    have hc := congrArg χ hz
    rw [AddChar.map_nsmul_eq_pow, h, Complex.I_sq, AddChar.map_zero_eq_one] at hc
    norm_num at hc
  have hdvd : addOrderOf d ∣ 4 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h4
  have hpow : addOrderOf d ∣ 2 ^ 2 := hdvd
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpow
  have hne : ¬ addOrderOf d ∣ 2 := fun h => h2 (addOrderOf_dvd_iff_nsmul_eq_zero.mp h)
  interval_cases k <;> simp_all

private theorem character_sq_of_order_four {q : ℕ} [NeZero q] (d : ZMod q)
    (h : addOrderOf d = 4) : ZMod.stdAddChar d ^ 2 = -1 := by
  let χ := (ZMod.stdAddChar (N := q))
  have hfour : 4 • d = 0 := by
    rw [← h]
    exact addOrderOf_nsmul_eq_zero d
  have htwo : 2 • d ≠ 0 := by
    intro h2
    have hdvd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2
    rw [h] at hdvd
    norm_num at hdvd
  have hfour' := congrArg χ hfour
  rw [AddChar.map_nsmul_eq_pow, AddChar.map_zero_eq_one] at hfour'
  have hs : (χ d ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hfour'
  rcases sq_eq_one_iff.mp hs with hs | hs
  · apply False.elim
    apply htwo
    apply ZMod.injective_stdAddChar
    change χ (2 • d) = χ 0
    rw [AddChar.map_nsmul_eq_pow, hs, AddChar.map_zero_eq_one]
  · exact hs

/-- The vanishing second Fourier mode bounds the first and forces an order-four
pair of equal masses at equality. -/
theorem zmod_first_mode_le_half_of_second_zero (q : ℕ) [NeZero q]
    (w : ZMod q → ℝ) (hw : ∑ j, w j = 1) (hpos : ∀ j, 0 ≤ w j)
    (hsecond : ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod q) = 0) :
    let d := ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod q)
    ‖d‖ ^ 2 ≤ 1 / 2 ∧
      (‖d‖ ^ 2 = 1 / 2 ↔ ∃ a b : ZMod q, a ≠ b ∧ addOrderOf (b - a) = 4 ∧
        w a = 1 / 2 ∧ w b = 1 / 2 ∧ ∀ j, j ≠ a → j ≠ b → w j = 0) := by
  let χ := (ZMod.stdAddChar (N := q))
  let z (j : ZMod q) := χ (-j)
  let m := ∑ j, (w j : ℂ) * z j
  have hz (j : ZMod q) : ‖z j‖ = 1 := χ.norm_apply _
  have hfirst : ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod q) = m := by
    rw [ZMod.dft_apply]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_one, smul_eq_mul, mul_comm]
  have hsecond' : ∑ j, (w j : ℂ) * z j ^ 2 = 0 := by
    rw [← hsecond, ZMod.dft_apply]
    refine sum_congr rfl fun j _ => ?_
    have harg : -(j * 2) = 2 • (-j) := by rw [mul_two, two_nsmul, neg_add_rev]
    change (w j : ℂ) * χ (-j) ^ 2 = χ (-(j * 2)) • (w j : ℂ)
    rw [harg, AddChar.map_nsmul_eq_pow, smul_eq_mul]
    exact mul_comm _ _
  dsimp only
  rw [hfirst]
  refine ⟨(first_moment_le_half_and_projection z w hz hw hpos hsecond').1, ?_⟩
  constructor
  · intro he
    have hn : Function.Injective z := fun _ _ h => neg_injective (ZMod.injective_stdAddChar h)
    obtain ⟨a, b, hab, hzrel, ha, hb, ho⟩ := equality_two_weights z w hz hn hw hpos hsecond' he
    have hchar : χ (a - b) = Complex.I := by
      have harg : -b = (a - b) + -a := by abel
      change χ (-b) = Complex.I * χ (-a) at hzrel
      rw [harg, AddChar.map_add_eq_mul] at hzrel
      have hne : χ (-a) ≠ 0 := by
        intro h
        have hnorm := hz a
        change ‖χ (-a)‖ = 1 at hnorm
        simp [h] at hnorm
      exact mul_right_cancel₀ hne hzrel
    exact ⟨b, a, hab.symm, order_four_of_character_i _ hchar, hb, ha, fun j x y => ho j y x⟩
  · rintro ⟨a, b, hab, horder, ha, hb, hzero⟩
    have hsub : addOrderOf (a - b) = 4 := by rw [← neg_sub, addOrderOf_neg, horder]
    let t := χ (a - b)
    have hsq : t ^ 2 = -1 := character_sq_of_order_four _ hsub
    have ht : t = Complex.I ∨ t = -Complex.I := by
      have hm : (t - Complex.I) * (t + Complex.I) = 0 := by
        calc
          _ = t ^ 2 - Complex.I ^ 2 := by ring
          _ = _ := by rw [hsq, Complex.I_sq, sub_self]
      exact (mul_eq_zero.mp hm).imp sub_eq_zero.mp (eq_neg_of_add_eq_zero_left)
    have harg : -b = (a - b) + -a := by abel
    have hrel : z b = t * z a := by
      change χ (-b) = χ (a - b) * χ (-a)
      rw [harg, AddChar.map_add_eq_mul]
    have hm : m = (1 / 2 : ℂ) * (1 + t) * z a := by
      have hab' : a ∉ ({b} : Finset (ZMod q)) := by simpa using hab
      have hoff (j : ZMod q) (_ : j ∈ univ) (hj : j ∉ ({a,b} : Finset (ZMod q))) :
          (w j : ℂ) * z j = 0 := by
        rw [hzero j (fun h => hj (by simp [h])) (fun h => hj (by simp [h])),
          Complex.ofReal_zero, zero_mul]
      unfold m
      rw [← sum_subset (subset_univ ({a,b} : Finset (ZMod q))) hoff, sum_insert hab',
        sum_singleton, ha, hb, hrel]
      push_cast
      ring
    have hz' : Complex.normSq (z a) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hz, one_pow]
    have hhalf : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by
      norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]
    rw [hm, Complex.sq_norm, Complex.normSq_mul, Complex.normSq_mul, hz', hhalf]
    rcases ht with ht | ht <;> rw [ht] <;> norm_num [Complex.normSq_apply]

/-- The bound for the first Fourier mode at zero second mode is attained
exactly when the modulus is divisible by four. -/
theorem zmod_exists_first_mode_half_of_second_zero (q : ℕ) [NeZero q] :
    (∃ w : ZMod q → ℝ, (∑ j, w j) = 1 ∧ (∀ j, 0 ≤ w j) ∧
      ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod q) = 0 ∧
      ‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod q)‖ ^ 2 = 1 / 2) ↔ 4 ∣ q := by
  constructor
  · rintro ⟨w, hw, hpos, hsecond, hfirst⟩
    obtain ⟨a, b, _, hab, _⟩ :=
      (zmod_first_mode_le_half_of_second_zero q w hw hpos hsecond).2.mp hfirst
    have hdvd : addOrderOf (b - a) ∣ Fintype.card (ZMod q) := addOrderOf_dvd_card
    simpa only [hab, ZMod.card] using hdvd
  · intro hq
    have hq0 : q ≠ 0 := NeZero.ne q
    let d : ZMod q := ((q / 4 : ℕ) : ZMod q)
    have hd : addOrderOf d = 4 := by
      change addOrderOf ((q / 4 : ℕ) : ZMod q) = 4
      rw [ZMod.addOrderOf_coe _ hq0, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hq),
        Nat.div_div_self hq hq0]
    have hd0 : d ≠ 0 := by
      intro hz
      simp [hz] at hd
    let w (j : ZMod q) : ℝ := if j = 0 ∨ j = d then 1 / 2 else 0
    have h0 : w 0 = 1 / 2 := by simp [w]
    have hwd : w d = 1 / 2 := by simp [w]
    have hoff (j : ZMod q) (h0 : j ≠ 0) (hd : j ≠ d) : w j = 0 := by simp [w, h0, hd]
    have hpair : (0 : ZMod q) ∉ ({d} : Finset (ZMod q)) := by simpa using Ne.symm hd0
    have hw : ∑ j, w j = 1 := by
      rw [← sum_subset (subset_univ ({0, d} : Finset (ZMod q)))
        (fun j _ h => hoff j (fun h0 => h (by simp [h0])) (fun hd => h (by simp [hd]))),
        sum_insert hpair, sum_singleton, h0, hwd]
      norm_num
    have hpos (j : ZMod q) : 0 ≤ w j := by unfold w; split <;> norm_num
    have hsecond : ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod q) = 0 := by
      rw [ZMod.dft_apply]
      have hz (j : ZMod q) (_ : j ∈ (univ : Finset (ZMod q)))
          (hj : j ∉ ({0, d} : Finset (ZMod q))) :
          ZMod.stdAddChar (-(j * 2)) • (w j : ℂ) = 0 := by
        rw [hoff j (fun h0 => hj (by simp [h0])) (fun hd => hj (by simp [hd]))]
        simp
      have harg : -(d * 2) = 2 • (-d) := by rw [mul_two, two_nsmul, neg_add_rev]
      have hs := character_sq_of_order_four (-d) (by rw [addOrderOf_neg, hd])
      rw [← sum_subset (subset_univ ({0, d} : Finset (ZMod q))) hz, sum_insert hpair,
        sum_singleton, zero_mul, neg_zero, AddChar.map_zero_eq_one, harg,
        AddChar.map_nsmul_eq_pow, hs, h0, hwd, one_smul, neg_smul, one_smul, add_neg_cancel]
    refine ⟨w, hw, hpos, hsecond, (zmod_first_mode_le_half_of_second_zero q w hw hpos hsecond).2.mpr ?_⟩
    exact ⟨0, d, Ne.symm hd0, by simpa using hd, h0, hwd, hoff⟩

end D5.S3.Fourier.Concentration.CyclicHarmonicEquality
