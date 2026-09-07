/- GID: D5/S3/Zeros/PochhammerDeformation/LinearFactor
   generality: G
   mirror-B: D5/B/S3/Zeros/PochhammerDeformation/LinearFactor
   mirror-E: none(waiver:general-theorems-no-computational-artifact)
   anchors: []
   utility: none
   digest: Linear factors preserve the Pochhammer unit root interval. -/

import D5.S3.Zeros.PochhammerDeformation.QuadraticInterval

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.PochhammerDeformation.LinearFactor

open Polynomial QuadraticInterval

/-- V7.0 on each falling Pochhammer basis element. -/
theorem lOp_linear_factor_on_falling (a t : ℝ) (ha : 0 < a) (k : ℕ) :
    lOp a ((C a⁻¹ * X + C t) * descPochhammer ℝ k) =
      (X + C t) * lOp a (descPochhammer ℝ k) +
        C a⁻¹ * X * (1 + X) * (lOp a (descPochhammer ℝ k)).derivative := by
  have hb (j : ℕ) : lOp a (descPochhammer ℝ j) =
      (ascPochhammer ℝ j).eval a • X ^ j := by
    have h := congrArg (fun p : ℝ[X] => (ascPochhammer ℝ j).eval a • p)
      (lOp_definition a ha j)
    simpa only [← smul_eq_C_mul, ← map_smul, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (ascPochhammer_pos j a ha)), one_smul] using h
  have he : (C a⁻¹ * X + C t) * descPochhammer ℝ k =
      a⁻¹ • descPochhammer ℝ (k + 1) + (a⁻¹ * k + t) • descPochhammer ℝ k := by
    rw [descPochhammer_succ_right]
    simp only [smul_eq_C_mul, map_add, map_mul, C_eq_natCast]
    ring
  rw [he, map_add, map_smul, map_smul, hb, hb, ascPochhammer_succ_eval]
  simp only [smul_eq_C_mul, map_mul, map_add, C_eq_natCast]
  have hc : C a⁻¹ * C a = (1 : ℝ[X]) := by
    rw [← map_mul, inv_mul_cancel₀ ha.ne', map_one]
  cases k with
  | zero =>
    simp only [ascPochhammer_zero, eval_one, map_one, Nat.cast_zero, pow_zero,
      zero_add, add_zero, mul_one, one_mul, mul_zero, derivative_one, pow_one, add_left_inj]
    rw [← mul_assoc, hc, one_mul]
  | succ k =>
    rw [derivative_C_mul, derivative_X_pow_succ]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one, C_eq_natCast, pow_succ]
    linear_combination (C ((ascPochhammer ℝ (k + 1)).eval a) * X ^ k * X ^ 2) * hc

/-- V7.0, extended from the falling Pochhammer basis by linearity. -/
theorem lOp_linear_factor (a t : ℝ) (ha : 0 < a) (P : ℝ[X]) :
    lOp a ((C a⁻¹ * X + C t) * P) =
      (X + C t) * lOp a P + C a⁻¹ * X * (1 + X) * (lOp a P).derivative := by
  let S : Polynomial.Sequence ℝ :=
    { elems' := descPochhammer ℝ
      degree_eq' := fun k => by
        rw [degree_eq_natDegree (monic_descPochhammer ℝ k).ne_zero,
          descPochhammer_natDegree] }
  have hspan := S.span (fun k => by
    change IsUnit (descPochhammer ℝ k).leadingCoeff
    rw [(monic_descPochhammer ℝ k).leadingCoeff]
    exact isUnit_one)
  have hmem : P ∈ Submodule.span ℝ (Set.range S) := by rw [hspan]; trivial
  induction hmem using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k, rfl⟩ := hp
    exact lOp_linear_factor_on_falling a t ha k
  | zero => simp
  | add p q _ _ hp hq => simp only [mul_add, map_add, hp, hq]; ring
  | smul r p _ hp =>
    simp only [mul_smul_comm, map_smul, hp, smul_add]

private theorem reciprocal_balance_location (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (s : Multiset ℂ)
    (hs : ∀ r ∈ s, r.im = 0 ∧ r.re ∈ Set.Icc (-1) 0) (z : ℂ)
    (hbalance : (a * t) • z⁻¹ + (a * (1 - t)) • (z + 1)⁻¹ +
      (s.map (fun r => (z - r)⁻¹)).sum = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1) 0 := by
  have hsep (f : ℂ →ₗ[ℝ] ℝ)
      (hr : ∀ r ∈ s, 0 ≤ f ((z - r)⁻¹))
      (h0 : 0 < f z⁻¹) (h1 : 0 < f (z + 1)⁻¹) : False := by
    have hsum : 0 ≤ f (s.map (fun r => (z - r)⁻¹)).sum := by
      rw [map_multiset_sum, Multiset.map_map]
      apply Multiset.sum_nonneg
      intro x hx
      obtain ⟨r, hr', rfl⟩ := Multiset.mem_map.mp hx
      exact hr r hr'
    have hpair : 0 < t * f z⁻¹ + (1 - t) * f (z + 1)⁻¹ := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]
        simpa using h1
      · exact add_pos_of_pos_of_nonneg (mul_pos h h0)
          (mul_nonneg (sub_nonneg.mpr ht.2) h1.le)
    have heq := congrArg f hbalance
    simp only [map_add, map_smul, map_zero, smul_eq_mul] at heq
    nlinarith [mul_pos ha hpair]
  have him : z.im = 0 := by
    by_contra hz
    let f : ℂ →ₗ[ℝ] ℝ := (-z.im) • Complex.imLm
    have hpos (r : ℂ) (hr : r.im = 0) : 0 < f ((z - r)⁻¹) := by
      have hne : z - r ≠ 0 := by
        intro h
        apply hz
        simpa only [Complex.sub_im, hr, sub_zero, Complex.zero_im]
          using congrArg Complex.im h
      change 0 < -z.im * ((z - r)⁻¹).im
      rw [Complex.inv_im, Complex.sub_im, hr, sub_zero]
      have he : -z.im * (-z.im / Complex.normSq (z - r)) =
          z.im ^ 2 / Complex.normSq (z - r) := by ring
      rw [he]
      exact div_pos (sq_pos_of_ne_zero hz) (Complex.normSq_pos.mpr hne)
    exact hsep f (fun r hr => (hpos r (hs r hr).1).le)
      (by simpa using hpos 0 (by simp))
      (by simpa using hpos (-1) (by simp))
  refine ⟨him, ?_, ?_⟩
  · by_contra h
    have hz : z.re < -1 := lt_of_not_ge h
    have hpos (r : ℂ) (hr : -1 ≤ r.re) : 0 < (-Complex.reLm) ((z - r)⁻¹) := by
      have hn : (z - r).re < 0 := by simp only [Complex.sub_re]; linarith
      have hne : z - r ≠ 0 := by
        intro he
        simp only [he, Complex.zero_re, lt_self_iff_false] at hn
      change 0 < -((z - r)⁻¹).re
      rw [Complex.inv_re, ← neg_div]
      exact div_pos (neg_pos.mpr hn) (Complex.normSq_pos.mpr hne)
    exact hsep (-Complex.reLm) (fun r hr => (hpos r (hs r hr).2.1).le)
      (by simpa using hpos 0 (by norm_num))
      (by simpa using hpos (-1) (by norm_num))
  · by_contra h
    have hz : 0 < z.re := lt_of_not_ge h
    have hpos (r : ℂ) (hr : r.re ≤ 0) : 0 < Complex.reLm ((z - r)⁻¹) := by
      have hn : 0 < (z - r).re := by simp only [Complex.sub_re]; linarith
      change 0 < ((z - r)⁻¹).re
      rw [Complex.inv_re]
      exact div_pos hn (Complex.normSq_pos.mpr (Complex.ne_zero_of_re_pos hn))
    exact hsep Complex.reLm (fun r hr => (hpos r (hs r hr).2.2).le)
      (by simpa using hpos 0 (by norm_num))
      (by simpa using hpos (-1) (by norm_num))

/-- The differential expression in V7.0 preserves the entire closed root interval. -/
theorem differential_preserves_unit_interval (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (Q : ℝ[X]) (hQ : RealRootsInUnitInterval Q) :
    RealRootsInUnitInterval
      ((X + C t) * Q + C a⁻¹ * X * (1 + X) * Q.derivative) := by
  let q := Q.map (algebraMap ℝ ℂ)
  have hm : (((X + C t) * Q + C a⁻¹ * X * (1 + X) * Q.derivative).map
      (algebraMap ℝ ℂ)) =
        (X + C (t : ℂ)) * q + C (a : ℂ)⁻¹ * X * (1 + X) * q.derivative := by
    simp [q, ← derivative_map]
  intro z hz
  rw [hm] at hz
  by_cases hq : q = 0
  · simp [hq] at hz
  by_cases hzq : q.eval z = 0
  · exact hQ z ((mem_roots hq).mpr hzq)
  by_cases hz0 : z = 0
  · subst z
    norm_num
  by_cases hz1 : z = -1
  · subst z
    norm_num
  have hz1' : z + 1 ≠ 0 := by
    intro h
    apply hz1
    linear_combination h
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have heval : (z + (t : ℂ)) * q.eval z +
      (a : ℂ)⁻¹ * z * (1 + z) * q.derivative.eval z = 0 := by
    simpa only [IsRoot, eval_add, eval_mul, eval_C, eval_X, eval_one]
      using isRoot_of_mem_roots hz
  have hlog := (IsAlgClosed.splits q).eval_derivative_div_eval_of_ne_zero hzq
  simp only [one_div] at hlog
  apply reciprocal_balance_location a t ha ht q.roots hQ z
  rw [← hlog]
  change (↑(a * t) : ℂ) * z⁻¹ + (↑(a * (1 - t)) : ℂ) * (z + 1)⁻¹ +
    q.derivative.eval z / q.eval z = 0
  have he : (↑(a * t) : ℂ) * z⁻¹ + (↑(a * (1 - t)) : ℂ) * (z + 1)⁻¹ +
      q.derivative.eval z / q.eval z =
      (a : ℂ) / (z * (z + 1) * q.eval z) *
        ((z + (t : ℂ)) * q.eval z +
          (a : ℂ)⁻¹ * z * (1 + z) * q.derivative.eval z) := by
    push_cast
    field_simp [ha', hz0, hz1', hzq]
    ring
  rw [he, heval, mul_zero]

/-- Open Problem 1.9 for the normalized factor X/a+t, for every positive a. -/
theorem linear_factor_preserves_unit_interval (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (P : ℝ[X])
    (hP : RealRootsInUnitInterval (lOp a P)) :
    RealRootsInUnitInterval (lOp a ((C a⁻¹ * X + C t) * P)) := by
  rw [lOp_linear_factor a t ha P]
  exact differential_preserves_unit_interval a t ha ht (lOp a P) hP

#print axioms lOp_linear_factor_on_falling
#print axioms lOp_linear_factor
#print axioms differential_preserves_unit_interval
#print axioms linear_factor_preserves_unit_interval

end D5.S3.Zeros.PochhammerDeformation.LinearFactor
