/- GID: D5/S3/Analytic/Interpolation/HermiteTwoPointRemainder
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/HermiteTwoPointRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-point Hermite interpolation has a cubic remainder with strict sign under positive third derivative. -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Set

noncomputable section

private theorem hermite_remainder_aux
    (L H x : ℝ) (f p q : ℝ → ℝ)
    (hLH : L < H) (hx : x ∈ Ioo L H)
    (hf : ContDiff ℝ 3 f) (hp : ContDiff ℝ 3 p) (hq : ContDiff ℝ 3 q)
    (hzero : ∀ t, iteratedDeriv 3 p t = 0)
    (hqL : q L = 0) (hqH : q H = 0) (hqX : q x ≠ 0)
    (hqderL : deriv q L = 0) (hqthird : ∀ t, iteratedDeriv 3 q t = 6)
    (hvalL : p L = f L) (hderL : deriv p L = deriv f L) (hvalH : p H = f H) :
    ∃ ξ ∈ Ioo L H,
      f x - p x = (iteratedDeriv 3 f ξ / 6) * q x := by
  let K : ℝ := (f x - p x) / q x
  let g : ℝ → ℝ := fun t => f t - p t - K * q t
  have hg : ContDiff ℝ 3 g := by
    dsimp [g]
    fun_prop
  have hgL : g L = 0 := by simp [g, K, hvalL, hqL]
  have hgH : g H = 0 := by simp [g, K, hvalH, hqH]
  have hgx : g x = 0 := by
    dsimp [g, K]
    field_simp [hqX]
    ring
  have hdergL : deriv g L = 0 := by
    have hderg : HasDerivAt g (deriv f L - deriv p L - K * deriv q L) L := by
      dsimp [g]
      convert ((hf.contDiffAt.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).hasDerivAt.sub
        (hp.contDiffAt.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).hasDerivAt).sub
        ((hq.contDiffAt.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).hasDerivAt.const_mul K) using 1 <;> rfl
    rw [hderg.deriv]
    simp [hderL, hqderL]
  obtain ⟨u, hu, hgu⟩ := exists_deriv_eq_zero (a := L) (b := x) hx.1 hg.continuous.continuousOn
      (show g L = g x from hgL.trans hgx.symm)
  obtain ⟨v, hv, hgv⟩ := exists_deriv_eq_zero (a := x) (b := H) hx.2 hg.continuous.continuousOn
      (show g x = g H from hgx.trans hgH.symm)
  have huv : u < v := lt_trans hu.2 hv.1
  have hderg_cont : Continuous (deriv g) := by
    simpa only [iteratedDeriv_one] using hg.continuous_iteratedDeriv 1 (by norm_num)
  obtain ⟨a, ha, haa⟩ := exists_deriv_eq_zero (a := L) (b := u) hu.1
      hderg_cont.continuousOn (show deriv g L = deriv g u from hdergL.trans hgu.symm)
  obtain ⟨b, hb, hbb⟩ := exists_deriv_eq_zero (a := u) (b := v) huv
      hderg_cont.continuousOn (show deriv g u = deriv g v from hgu.trans hgv.symm)
  have hab : a < b := lt_trans ha.2 hb.1
  have hderg2_cont : Continuous (deriv (deriv g)) := by
    simpa only [iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_zero] using
      hg.continuous_iteratedDeriv 2 (by norm_num)
  obtain ⟨ξ, hξ, hxi⟩ := exists_deriv_eq_zero (a := a) (b := b) hab
      hderg2_cont.continuousOn (show deriv (deriv g) a = deriv (deriv g) b from haa.trans hbb.symm)
  refine ⟨ξ, ⟨lt_trans ha.1 hξ.1, lt_trans hξ.2 (lt_trans hb.2 hv.2)⟩, ?_⟩
  have hthirdg : iteratedDeriv 3 g ξ = 0 := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using hxi
  have hgfun : g = (f - p) - K • q := by
    funext t
    simp [g, Pi.sub_apply, Pi.smul_apply]
  have hthirdg' : iteratedDeriv 3 g ξ =
      iteratedDeriv 3 f ξ - iteratedDeriv 3 p ξ - K * iteratedDeriv 3 q ξ := by
    rw [hgfun]
    calc
      iteratedDeriv 3 ((f - p) - K • q) ξ =
          iteratedDeriv 3 (f - p) ξ - iteratedDeriv 3 (K • q) ξ :=
        iteratedDeriv_sub ((hf.sub hp).contDiffAt) ((hq.const_smul K).contDiffAt)
      _ = iteratedDeriv 3 f ξ - iteratedDeriv 3 p ξ - K * iteratedDeriv 3 q ξ := by
        rw [iteratedDeriv_sub hf.contDiffAt hp.contDiffAt]
        rw [iteratedDeriv_const_smul hq.contDiffAt K]
        simp [smul_eq_mul]
  have hK : K = iteratedDeriv 3 f ξ / 6 := by
    rw [hthirdg'] at hthirdg
    rw [hzero, hqthird ξ] at hthirdg
    linarith
  have hK' : K = iteratedDeriv 3 f ξ / 6 := by simpa [K] using hK
  calc
    f x - p x = K * q x := by
      dsimp [K]
      exact (div_mul_cancel₀ (f x - p x) hqX).symm
    _ = (iteratedDeriv 3 f ξ / 6) * q x := by rw [hK']


/-- The two-point Hermite remainder and its sign for a positive third derivative. -/
theorem hermite_two_point_remainder
    (L H x : ℝ) (f p : ℝ → ℝ)
    (hx : x ∈ Ioo L H)
    (hf : ContDiff ℝ 3 f) (hp : ContDiff ℝ 3 p)
    (hzero : ∀ t, iteratedDeriv 3 p t = 0)
    (hvalL : p L = f L) (hderL : deriv p L = deriv f L) (hvalH : p H = f H)
    (hpos : ∀ t ∈ Ioo L H, 0 < iteratedDeriv 3 f t) :
    ∃ ξ ∈ Ioo L H,
      f x - p x = (iteratedDeriv 3 f ξ / 6) * (x - L)^2 * (x - H) ∧
        f x - p x < 0 := by
  let q : ℝ → ℝ := fun t => (t - L)^2 * (t - H)
  have hqL : q L = 0 := by simp [q]
  have hqH : q H = 0 := by simp [q]
  have hqX : q x ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hx.1.ne'))
      (sub_ne_zero.mpr (ne_of_lt hx.2))
  have hqderL : deriv q L = 0 := by
    have hq1 : deriv q = fun t => 2 * (t-L) * (t-H) + (t-L)^2 := by
      funext t
      have h := (((hasDerivAt_id t).sub (hasDerivAt_const t L)).pow 2).mul
        ((hasDerivAt_id t).sub (hasDerivAt_const t H))
      change deriv (fun t : ℝ => (t-L)^2*(t-H)) t = _
      simpa [sub_eq_add_neg] using h.deriv
    rw [hq1]
    simp [q]
  have hqthird : ∀ t, iteratedDeriv 3 q t = 6 := by
    have hq1 : deriv q = fun t => 2 * (t-L) * (t-H) + (t-L)^2 := by
      funext t
      have h := (((hasDerivAt_id t).sub (hasDerivAt_const t L)).pow 2).mul
        ((hasDerivAt_id t).sub (hasDerivAt_const t H))
      change deriv (fun t : ℝ => (t-L)^2*(t-H)) t = _
      simpa [sub_eq_add_neg] using h.deriv
    have hq2 : deriv (fun t : ℝ => 2 * (t-L) * (t-H) + (t-L)^2) = fun t => 6*t - 4*L - 2*H := by
      funext t
      have h1raw := (((hasDerivAt_id t).sub (hasDerivAt_const t L)).const_mul 2).mul
        ((hasDerivAt_id t).sub (hasDerivAt_const t H))
      have h1 : HasDerivAt (fun y : ℝ => 2 * (y-L) * (y-H))
          (2 * (t-H) + 2 * (t-L)) t := by
        convert h1raw using 1 <;> (try { rfl }) <;> (try { ext y; simp [sub_eq_add_neg, id_eq, Pi.sub_apply, Pi.pow_apply]; ring }) <;> simp [sub_eq_add_neg, id_eq, Pi.sub_apply, Pi.pow_apply] <;> ring
      have h2raw := (((hasDerivAt_id t).sub (hasDerivAt_const t L)).pow 2)
      have h2 : HasDerivAt (fun y : ℝ => (y-L)^2) (2 * (t-L)) t := by
        convert h2raw using 1 <;> (try { rfl }) <;> (try { ext y; simp [sub_eq_add_neg, id_eq, Pi.sub_apply, Pi.pow_apply]; ring }) <;> simp [sub_eq_add_neg, id_eq, Pi.sub_apply, Pi.pow_apply] <;> ring
      have hsum := h1.add h2
      change deriv (fun t : ℝ => 2 * (t-L) * (t-H) + (t-L)^2) t = _
      convert hsum.deriv using 1 <;> (try { rfl }) <;> (try { ext y; simp only [Pi.add_apply]; ring }) <;> ring
      /- have h1 := (((hasDerivAt_id t).sub (hasDerivAt_const t L)).const_mul 2).mul
        ((hasDerivAt_id t).sub (hasDerivAt_const t H))
      -/
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [show deriv q = (fun t => 2 * (t-L) * (t-H) + (t-L)^2) from hq1]
    rw [hq2]
    intro t
    have h := (hasDerivAt_id t).const_mul 6
    simpa using h.deriv


  obtain ⟨ξ, hξ, heq⟩ := hermite_remainder_aux L H x f p q
      (lt_trans hx.1 hx.2) hx hf hp (by dsimp [q]; fun_prop) hzero hqL hqH hqX hqderL hqthird
      hvalL hderL hvalH
  have hqneg : q x < 0 := by
    dsimp [q]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (sub_ne_zero.mpr hx.1.ne'))
      (sub_neg.mpr hx.2)
  have hcoef : 0 < iteratedDeriv 3 f ξ / 6 := div_pos (hpos ξ hξ) (by norm_num)
  refine ⟨ξ, hξ, ?_, ?_⟩
  · simpa [q, mul_assoc] using heq
  · rw [heq]
    exact mul_neg_of_pos_of_neg hcoef hqneg
