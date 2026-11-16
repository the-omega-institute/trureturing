/- GID: D5/S3/StatisticalMechanics/InversePowerLineConductance
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/InversePowerLineConductance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Harmonic gap conductances for inverse-power equilibria. -/

/-
admission_basis: escape-witness
question_answered: https://github.com/the-omega-institute/trureturing/issues/27202
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27401
force_difference_nonneg:
  proof_shape: bind-only; escape_witness: none.
  consumers: adjacent_force_loss.
adjacent_force_loss:
  proof_shape: content; escape_witness: adjacent_force_loss.
  consumers: equilibrium_gap_ratio.
crude_ratio:
  proof_shape: bind-only; escape_witness: none.
  consumers: equilibrium_gap_ratio.
equilibrium_gap_ratio:
  proof_shape: content; escape_witness: adjacent_force_loss.
  consumers: equilibrium_gap_reverse, InversePowerLineEquilibria.equilibrium_is_progression.
equilibrium_gap_reverse:
  proof_shape: content; escape_witness: adjacent_force_loss.
  consumers: InversePowerLineEquilibria.equilibrium_is_progression.
negative_dslope_formula:
  proof_shape: bind-only; escape_witness: none.
  consumers: secant_pos, secant_mean_value, secant_bound, conductance_formula.
secant_mul:
  proof_shape: bind-only; escape_witness: none.
  consumers: conductance_force_difference.
secant_symm:
  proof_shape: bind-only; escape_witness: none.
  consumers: secant_bound.
secant_pos:
  proof_shape: bind-only; escape_witness: none.
  consumers: conductance_positive.
secant_mean_value:
  proof_shape: bind-only; escape_witness: none.
  consumers: secant_bound.
secant_bound:
  proof_shape: bind-only; escape_witness: none.
  consumers: conductance_distance_bound.
reciprocal_transform:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.equilibrium_is_progression.
conductance:
  proof_shape: bind-only; escape_witness: none.
  consumers: conductance_formula, conductance_symmetric, conductance_positive,
    conductance_force_difference, gaps_harmonic_difference, conductance_distance_bound,
    conductance_rows, gaps_harmonic, InversePowerLineEquilibria.equilibrium_is_progression.
conductance_formula:
  proof_shape: bind-only; escape_witness: none.
  consumers: conductance_positive, conductance_force_difference, conductance_distance_bound,
    conductance_rows.
conductance_symmetric:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.equilibrium_is_progression.
conductance_positive:
  proof_shape: bind-only; escape_witness: none.
  consumers: conductance_rows, InversePowerLineEquilibria.equilibrium_is_progression.
conductance_force_difference:
  proof_shape: bind-only; escape_witness: none.
  consumers: gaps_harmonic_difference.
gaps_harmonic_difference:
  proof_shape: bind-only; escape_witness: none.
  consumers: gaps_harmonic.
shifted_distance_comparison:
  proof_shape: bind-only; escape_witness: none.
  consumers: conductance_distance_bound.
conductance_distance_bound:
  proof_shape: bind-only; escape_witness: none.
  consumers: conductance_rows, InversePowerLineEquilibria.equilibrium_is_progression.
local_distance_lower:
  proof_shape: bind-only; escape_witness: none.
  consumers: conductance_rows.
conductance_rows:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.equilibrium_is_progression.
gaps_harmonic:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.equilibrium_is_progression.
-/

import D5.S3.StatisticalMechanics.InversePowerLineBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Gap comparison and harmonic conductances
-/

namespace D5.S3.StatisticalMechanics.InversePowerLineConductance

open D5.S3.StatisticalMechanics.InversePowerLineBasics

private theorem force_difference_nonneg {s : ℝ} (hs : 0 < s) {a : ℤ → ℝ}
    (ha : StrictMono a) (n j : ℤ) (hjn : j ≠ n) (hjn1 : j ≠ n + 1) :
    0 ≤ indexedForce s a (n + 1) j - indexedForce s a n j := by
  rcases lt_or_gt_of_ne hjn with hj | hj
  · have h1 : a j < a n := ha hj
    have h2 : a j < a (n + 1) := ha (by omega)
    have hn : a n < a (n + 1) := ha (by omega)
    simp only [indexedForce, Real.sign_of_neg (sub_neg.mpr h1),
      Real.sign_of_neg (sub_neg.mpr h2), neg_one_mul,
      abs_of_neg (sub_neg.mpr h1), abs_of_neg (sub_neg.mpr h2)]
    have h := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < -(a j - a n))
      (by linarith : -(a j - a n) ≤ -(a j - a (n + 1))) (by linarith : -s ≤ 0)
    linarith
  · have h1 : a n < a j := ha hj
    have h2 : a (n + 1) < a j := ha (by omega)
    have hn : a n < a (n + 1) := ha (by omega)
    simp only [indexedForce, Real.sign_of_pos (sub_pos.mpr h1),
      Real.sign_of_pos (sub_pos.mpr h2), one_mul,
      abs_of_pos (sub_pos.mpr h1), abs_of_pos (sub_pos.mpr h2)]
    exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos (sub_pos.mpr h2)
      (by linarith) (by linarith))

private theorem adjacent_force_loss {s : ℝ} (hs : 0 < s) {a : ℤ → ℝ}
    (ha : StrictMono a) (hf : ∀ n, HasSum (indexedForce s a n) 0) (n : ℤ) :
    (a n - a (n - 1)) ^ (-s) ≤
      2 * (a (n + 1) - a n) ^ (-s) + (a (n + 1) - a (n - 1)) ^ (-s) := by
  classical
  let v := (a (n + 1) - a n) ^ (-s)
  let T : ℤ → ℝ := fun j =>
    indexedForce s a (n + 1) j - indexedForce s a n j +
      (if j = n then v else 0) + (if j = n + 1 then v else 0)
  have hsingle (k : ℤ) : HasSum (fun j : ℤ => if j = k then v else 0) v := by
    simpa only [eq_comm] using hasSum_ite_eq k v
  have hT : HasSum T (2 * v) := by
    have H := (((hf (n + 1)).sub (hf n)).add (hsingle n)).add (hsingle (n + 1))
    convert H using 1 <;> ring
  have hpos : a n < a (n + 1) := ha (by omega)
  have hTn : T n = 0 := by
    simp [T, indexedForce, v, Real.sign_of_neg (sub_neg.mpr hpos),
      abs_of_neg (sub_neg.mpr hpos), show -(a n - a (n + 1)) = a (n + 1) - a n by ring]
  have hTn1 : T (n + 1) = 0 := by
    simp [T, indexedForce, v, Real.sign_of_pos (sub_pos.mpr hpos),
      abs_of_pos (sub_pos.mpr hpos)]
  have hTnonneg (j : ℤ) : 0 ≤ T j := by
    by_cases hj : j = n
    · simpa [hj, hTn]
    by_cases hj1 : j = n + 1
    · simpa [hj1, hTn1]
    simpa only [T, if_neg hj, if_neg hj1, add_zero] using force_difference_nonneg hs ha n j hj hj1
  have hle := hT.summable.le_tsum (n - 1) (fun j _ => hTnonneg j)
  rw [hT.tsum_eq] at hle
  have hm : a (n - 1) < a n := ha (by omega)
  have hm1 : a (n - 1) < a (n + 1) := ha (by omega)
  simp only [T, indexedForce, if_neg (show n - 1 ≠ n by omega),
    if_neg (show n - 1 ≠ n + 1 by omega), add_zero,
    Real.sign_of_neg (sub_neg.mpr hm), Real.sign_of_neg (sub_neg.mpr hm1),
    neg_one_mul, abs_of_neg (sub_neg.mpr hm), abs_of_neg (sub_neg.mpr hm1)] at hle
  simp only [neg_sub] at hle
  dsimp [v] at hle
  linarith

private theorem crude_ratio {s u v : ℝ} (hs : 2 < s) (hu : 0 < u) (hv : 0 < v)
    (h : u ^ (-s) ≤ 2 * v ^ (-s) + (u + v) ^ (-s)) : v ≤ 2 * u := by
  by_contra hh
  have hlarge : 2 * u < v := lt_of_not_ge hh
  have hp : 0 < u ^ (-s) := Real.rpow_pos_of_pos hu _
  have hmono : (u + v) ^ (-s) ≤ v ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hv (by linarith) (by linarith)
  have hvb : v ^ (-s) ≤ (2 * u) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hlarge.le (by linarith)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hu.le] at hvb
  have htwo : (2:ℝ) ^ (-s) < (1:ℝ) / 4 := by
    have hpow := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
      (by linarith : -s < (-2:ℝ))
    norm_num at hpow ⊢
    exact hpow
  nlinarith

theorem equilibrium_gap_ratio {s : ℝ} (hs : 2 < s) {a : ℤ → ℝ}
    (ha : StrictMono a) (hf : ∀ n, HasSum (indexedForce s a n) 0) :
    ∀ n : ℤ, a (n + 1) - a n ≤ 2 * (a n - a (n - 1)) := by
  intro n
  apply crude_ratio hs (sub_pos.mpr (ha (by omega))) (sub_pos.mpr (ha (by omega)))
  have h := adjacent_force_loss (by linarith : 0 < s) ha hf n
  convert h using 1 <;> congr 1 <;> ring

theorem equilibrium_gap_reverse {s : ℝ} (hs : 2 < s) {a : ℤ → ℝ}
    (ha : StrictMono a) (hf : ∀ n, HasSum (indexedForce s a n) 0) :
    ∀ n : ℤ, a n - a (n - 1) ≤ 2 * (a (n + 1) - a n) := by
  let b : ℤ → ℝ := fun j => -a (-j)
  have hb : StrictMono b := by
    intro j k hjk
    exact neg_lt_neg (ha (neg_lt_neg hjk))
  have hbf : ∀ n, HasSum (indexedForce s b n) 0 := by
    intro n
    have H := ((Equiv.neg ℤ).hasSum_iff.mpr (hf (-n))).neg
    convert H using 1
    · ext j
      simp only [indexedForce, b, Equiv.neg_apply, show -a (-j) - -a (-n) = -(a (-j) - a (-n)) by ring,
        Real.sign_neg, abs_neg, neg_mul, Function.comp_apply]
    · simp
  intro n
  have H := equilibrium_gap_ratio hs hb hbf (-n)
  dsimp [b] at H
  rw [show -(-n + 1) = n - 1 by ring, neg_neg,
    show -(-n - 1) = n + 1 by ring] at H
  linarith

private theorem negative_dslope_formula (s D E : ℝ) :
    -dslope (fun t : ℝ => t ^ (-s)) D E =
      if D = E then s * D ^ (-s - 1) else (D ^ (-s) - E ^ (-s)) / (E - D) := by
  by_cases h : D = E
  · subst E
    simp [Real.deriv_rpow_const]
  · rw [ite_eq_right h, dslope_of_ne _ (Ne.symm h), slope_def_field]
    ring


private theorem secant_mul (s D E : ℝ) :
    (-dslope (fun t : ℝ => t ^ (-s)) D E) * (E - D) = D ^ (-s) - E ^ (-s) := by
  have h := sub_smul_dslope (fun t : ℝ => t ^ (-s)) D E
  simp only [smul_eq_mul] at h
  nlinarith [h]


private theorem secant_symm (s D E : ℝ) : (-dslope (fun t : ℝ => t ^ (-s)) D E) = (-dslope (fun t : ℝ => t ^ (-s)) E D) := by
  by_cases h : D = E
  · subst E; rfl
  · rw [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ h, slope_comm]

private theorem secant_pos {s D E : ℝ} (hs : 0 < s) (hD : 0 < D) (hE : 0 < E) :
    0 < (-dslope (fun t : ℝ => t ^ (-s)) D E) := by
  by_cases h : D = E
  · simp only [negative_dslope_formula, ite_eq_left h]
    exact mul_pos hs (Real.rpow_pos_of_pos hD _)
  · simp only [negative_dslope_formula, ite_eq_right h]
    rcases lt_or_gt_of_ne h with h | h
    · exact div_pos (sub_pos.mpr (Real.rpow_lt_rpow_of_neg hD h (by linarith))) (sub_pos.mpr h)
    · exact div_pos_of_neg_of_neg
        (sub_neg.mpr (Real.rpow_lt_rpow_of_neg hE h (by linarith))) (sub_neg.mpr h)

private theorem secant_mean_value {s D E : ℝ} (hD : 0 < D) (hDE : D < E) :
    ∃ ξ ∈ Set.Ioo D E, (-dslope (fun t : ℝ => t ^ (-s)) D E) = s * ξ ^ (-s - 1) := by
  have hderiv (x : ℝ) (hx : x ∈ Set.Ioo D E) :
      HasDerivAt (fun t : ℝ => t ^ (-s)) ((-s) * x ^ (-s - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hD.trans hx.1)))
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-s)) (Set.Icc D E) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x (-s) (Or.inl (ne_of_gt (hD.trans_le hx.1)))).continuousWithinAt
  obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-s))
    (fun t : ℝ => (-s) * t ^ (-s - 1)) hDE hcont hderiv
  refine ⟨ξ, hξ, ?_⟩
  simp only [negative_dslope_formula, ite_eq_right hDE.ne]
  have hn : E - D ≠ 0 := sub_ne_zero.mpr hDE.ne'
  field_simp [hn] at heq ⊢
  linarith

private theorem secant_bound {s D E : ℝ} (hs : 0 < s) (hD : 0 < D) (hE : 0 < E) :
    (-dslope (fun t : ℝ => t ^ (-s)) D E) ≤ s * (min D E) ^ (-s - 1) := by
  rcases lt_trichotomy D E with h | h | h
  · obtain ⟨ξ, hξ, heq⟩ := secant_mean_value hD h
    rw [min_eq_left h.le, heq]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hD hξ.1.le (by linarith)) hs.le
  · subst E
    rw [negative_dslope_formula]
    simp
  · rw [secant_symm, min_comm]
    obtain ⟨ξ, hξ, heq⟩ := secant_mean_value hE h
    rw [min_eq_left h.le, heq]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hE hξ.1.le (by linarith)) hs.le

theorem reciprocal_transform {V : Type*} (c : V → V → ℝ) (g : V → ℝ)
    (hg : ∀ x, 0 < g x) (hrow : ∀ x, Summable (c x))
    (hweighted : ∀ x, Summable (fun y => c x y * g y))
    (hharm : ∀ x, (∑' y, c x y * g y) = (∑' y, c x y) * g x) :
    (∀ x, Summable (fun y => c x y * g x * g y)) ∧
    (∀ x, Summable (fun y => (c x y * g x * g y) * (g y)⁻¹)) ∧
    ∀ x, (∑' y, (c x y * g x * g y) * (g y)⁻¹) =
      (∑' y, c x y * g x * g y) * (g x)⁻¹ := by
  have hpoint (x y : V) : (c x y * g x * g y) * (g y)⁻¹ = c x y * g x := by
    field_simp [(hg y).ne']
  have hsum (x : V) : Summable (fun y => c x y * g x * g y) := by
    convert (hweighted x).mul_left (g x) using 1
    ext y; ring
  refine ⟨hsum, ?_, ?_⟩
  · intro x
    simp_rw [hpoint]
    exact (hrow x).mul_right (g x)
  · intro x
    simp_rw [hpoint]
    rw [tsum_mul_right]
    have heq : (∑' y, c x y * g x * g y) = g x * (∑' y, c x y * g y) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro y; ring
    rw [heq, hharm]
    field_simp [(hg x).ne']

noncomputable def conductance (s : ℝ) (a : ℤ → ℝ) (n j : ℤ) : ℝ :=
  if n = j then 0 else
    if |a j - a n| = |a (j + 1) - a (n + 1)| then s * |a j - a n| ^ (-s - 1)
    else (|a j - a n| ^ (-s) - |a (j + 1) - a (n + 1)| ^ (-s)) /
      (|a (j + 1) - a (n + 1)| - |a j - a n|)

private theorem conductance_formula (s : ℝ) (a : ℤ → ℝ) (n j : ℤ) :
    conductance s a n j = if n = j then 0 else
      -dslope (fun t : ℝ => t ^ (-s)) |a j - a n| |a (j + 1) - a (n + 1)| := by
  simp only [conductance, negative_dslope_formula]


theorem conductance_symmetric (s : ℝ) (a : ℤ → ℝ) (n j : ℤ) :
    conductance s a n j = conductance s a j n := by
  simp only [conductance, eq_comm, abs_sub_comm (a j) (a n),
    abs_sub_comm (a (j + 1)) (a (n + 1))]

theorem conductance_positive {s : ℝ} (hs : 0 < s) {a : ℤ → ℝ}
    (ha : StrictMono a) (n j : ℤ) (hnj : n ≠ j) : 0 < conductance s a n j := by
  rw [conductance_formula, if_neg hnj]
  apply secant_pos hs
  · exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hnj (ha.injective h).symm))
  · exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hnj (by have H := ha.injective h; omega)))

private theorem conductance_force_difference (s : ℝ) {a : ℤ → ℝ} (ha : StrictMono a) (n j : ℤ) :
    conductance s a n j * (fwdDiff 1 a j - fwdDiff 1 a n) =
      indexedForce s a n j - indexedForce s a (n + 1) (j + 1) := by
  by_cases hnj : n = j
  · subst j; simp [conductance, indexedForce, fwdDiff]
  have H := secant_mul s |a j - a n| |a (j + 1) - a (n + 1)|
  rw [conductance_formula, if_neg hnj]
  rcases lt_or_gt_of_ne hnj with h | h
  · have h1 := ha h
    have h2 := ha (show n + 1 < j + 1 by omega)
    simp only [abs_of_pos (sub_pos.mpr h1), abs_of_pos (sub_pos.mpr h2)] at H
    simp only [indexedForce, Real.sign_of_pos (sub_pos.mpr h1), Real.sign_of_pos (sub_pos.mpr h2),
      abs_of_pos (sub_pos.mpr h1), abs_of_pos (sub_pos.mpr h2), one_mul, fwdDiff]
    convert H using 1 <;> congr 1 <;> ring
  · have h1 := ha h
    have h2 := ha (show j + 1 < n + 1 by omega)
    simp only [abs_of_neg (sub_neg.mpr h1), abs_of_neg (sub_neg.mpr h2)] at H
    simp only [indexedForce, Real.sign_of_neg (sub_neg.mpr h1), Real.sign_of_neg (sub_neg.mpr h2),
      abs_of_neg (sub_neg.mpr h1), abs_of_neg (sub_neg.mpr h2), neg_one_mul, fwdDiff]
    nlinarith [H]

private theorem gaps_harmonic_difference {s : ℝ} {a : ℤ → ℝ} (ha : StrictMono a)
    (hf : ∀ n, HasSum (indexedForce s a n) 0) :
    ∀ n, HasSum (fun j => conductance s a n j * (fwdDiff 1 a j - fwdDiff 1 a n)) 0 := by
  intro n
  have H := hf (n + 1)
  have Hshift : HasSum (fun j : ℤ => indexedForce s a (n + 1) (j + 1)) 0 :=
    ((Equiv.addRight (1 : ℤ)).hasSum_iff
      (f := indexedForce s a (n + 1)) (a := (0 : ℝ))).mpr H
  have Hdiff := (hf n).sub Hshift
  rw [sub_self] at Hdiff
  exact Hdiff.congr_fun (fun j => conductance_force_difference s ha n j)

private theorem shifted_distance_comparison {a : ℤ → ℝ} (ha : StrictMono a)
    (hreverse : ∀ n, fwdDiff 1 a n ≤ 2 * fwdDiff 1 a (n + 1)) (n j : ℤ) :
    |a j - a n| ≤ 3 * |a (j + 1) - a (n + 1)| := by
  have hright (n j : ℤ) (hnj : n < j) :
      a j - a n ≤ 3 * (a (j + 1) - a (n + 1)) := by
    have hratio := hreverse n
    have hpos : 0 < fwdDiff 1 a (n + 1) := sub_pos.mpr (ha (by omega))
    dsimp [fwdDiff] at hratio hpos
    by_cases hj : j = n + 1
    · subst j; linarith
    · have hjn : n + 2 ≤ j := by omega
      have hmono := ha.monotone hjn
      have hmono2 := ha.monotone (show j ≤ j + 1 by omega)
      rw [show n + 1 + 1 = n + 2 by omega] at hratio hpos
      linarith
  rcases lt_trichotomy n j with h | h | h
  · simpa only [abs_of_pos (sub_pos.mpr (ha h)),
      abs_of_pos (sub_pos.mpr (ha (show n + 1 < j + 1 by omega)))] using hright n j h
  · subst j; simp
  · simpa only [abs_of_neg (sub_neg.mpr (ha h)),
      abs_of_neg (sub_neg.mpr (ha (show j + 1 < n + 1 by omega))), neg_sub] using hright j n h

theorem conductance_distance_bound {s : ℝ} (hs : 0 < s) {a : ℤ → ℝ}
    (ha : StrictMono a) (hreverse : ∀ n, fwdDiff 1 a n ≤ 2 * fwdDiff 1 a (n + 1))
    (n j : ℤ) (hnj : n ≠ j) :
    conductance s a n j ≤ (s / (3:ℝ) ^ (-s - 1)) * |a j - a n| ^ (-s - 1) := by
  let D := |a j - a n|
  let E := |a (j + 1) - a (n + 1)|
  have hD : 0 < D := abs_pos.mpr (sub_ne_zero.mpr (fun h => hnj (ha.injective h).symm))
  have hE : 0 < E := abs_pos.mpr (sub_ne_zero.mpr (fun h => hnj (by have H := ha.injective h; omega)))
  have hcomp : D ≤ 3 * E := shifted_distance_comparison ha hreverse n j
  have hmin : D / 3 ≤ min D E := le_min (by linarith) (by linarith)
  have H := (secant_bound hs hD hE).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < D / 3) hmin (by linarith : -s - 1 ≤ 0)) hs.le)
  rw [Real.div_rpow hD.le (by norm_num : (0:ℝ) ≤ 3)] at H
  rw [conductance_formula, if_neg hnj]
  convert H using 1 <;> dsimp [D, E] <;> ring

private theorem local_distance_lower {a : ℤ → ℝ} (ha : StrictMono a) (n j : ℤ) (hnj : n ≠ j) :
    min (fwdDiff 1 a n) (fwdDiff 1 a (n - 1)) ≤ |a j - a n| := by
  rcases lt_or_gt_of_ne hnj with h | h
  · rw [abs_of_pos (sub_pos.mpr (ha h))]
    have H := ha.monotone (show n + 1 ≤ j by omega)
    exact (min_le_left _ _).trans (by dsimp [fwdDiff]; linarith)
  · rw [abs_of_neg (sub_neg.mpr (ha h))]
    have H := ha.monotone (show j ≤ n - 1 by omega)
    apply (min_le_right _ _).trans
    dsimp [fwdDiff]
    rw [show n - 1 + 1 = n by omega]
    linarith

theorem conductance_rows {s : ℝ} (hs : 0 < s) {a : ℤ → ℝ}
    (ha : StrictMono a) (hreverse : ∀ n, fwdDiff 1 a n ≤ 2 * fwdDiff 1 a (n + 1))
    (htotal : ∀ n, Summable (fun j : ℤ => |a j - a n| ^ (-s))) :
    ∀ n, Summable (conductance s a n) := by
  intro n
  let δ := min (fwdDiff 1 a n) (fwdDiff 1 a (n - 1))
  let K := s / (3:ℝ) ^ (-s - 1)
  have hgap (k : ℤ) : 0 < fwdDiff 1 a k := sub_pos.mpr (ha (by omega))
  have hδ : 0 < δ := lt_min (hgap n) (hgap (n - 1))
  have hK : 0 ≤ K := div_nonneg hs.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hcpos (j : ℤ) : 0 ≤ conductance s a n j := by
    by_cases hnj : n = j
    · simp [conductance, hnj]
    · exact (conductance_positive hs ha n j hnj).le
  apply Summable.of_nonneg_of_le hcpos ?_ ((htotal n).mul_left (K / δ))
  intro j
  by_cases hnj : n = j
  · rw [conductance_formula, if_pos hnj]
    exact mul_nonneg (div_nonneg hK hδ.le) (Real.rpow_nonneg (abs_nonneg _) _)
  ·
    have hD : 0 < |a j - a n| := abs_pos.mpr (sub_ne_zero.mpr (fun h => hnj (ha.injective h).symm))
    have hδD : δ ≤ |a j - a n| := local_distance_lower ha n j hnj
    calc
      conductance s a n j ≤ K * |a j - a n| ^ (-s - 1) := conductance_distance_bound hs ha hreverse n j hnj
      _ = K * (|a j - a n| ^ (-s) / |a j - a n|) := by rw [Real.rpow_sub_one hD.ne']
      _ ≤ K * (|a j - a n| ^ (-s) / δ) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left
          (Real.rpow_nonneg (abs_nonneg _) _) hδ hδD) hK
      _ = _ := by exact Eq.symm (mul_comm_div K δ (|a j - a n| ^ (-s)))

theorem gaps_harmonic {s : ℝ} {a : ℤ → ℝ} (ha : StrictMono a)
    (hf : ∀ n, HasSum (indexedForce s a n) 0)
    (hrow : ∀ n, Summable (conductance s a n)) :
    (∀ n, Summable (fun j => conductance s a n j * fwdDiff 1 a j)) ∧
    ∀ n, (∑' j, conductance s a n j * fwdDiff 1 a j) =
      (∑' j, conductance s a n j) * fwdDiff 1 a n := by
  have H := gaps_harmonic_difference ha hf
  have hweighted (n : ℤ) : HasSum (fun j => conductance s a n j * fwdDiff 1 a j)
      ((∑' j, conductance s a n j) * fwdDiff 1 a n) := by
    convert (H n).add ((hrow n).hasSum.mul_right (fwdDiff 1 a n)) using 1
    · ext j; ring
    · ring
  exact ⟨fun n => (hweighted n).summable, fun n => (hweighted n).tsum_eq⟩

end D5.S3.StatisticalMechanics.InversePowerLineConductance
