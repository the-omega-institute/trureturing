/- GID: D5/S3/Analytic/ConvexBarrier/DikinOneDimensional
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/DikinOneDimensional
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
One-dimensional calculus behind the Dikin inclusion, used in (2.2) of
Zhang--Fu--Dai, arXiv:2611.06404v1, and their Lemma 3.2. This is standard
self-concordant analysis, not a new mathematical bound.

No integral comparison is a premise: the reciprocal-Hessian estimate and
the two subsequent integrations are proved by the mean-value inequality.
The final supplier in `PrimalDikin` constructs all four functions here from
the actual Frechet derivatives of `Basic.IsLHSCB`.

SOURCE ONLY. No Lean elaboration or kernel execution has been performed.
-/

open Set

namespace D5.S3.Analytic.ConvexBarrier

/-- The mean-value inequality in the scalar form needed below. -/
theorem abs_increment_le {f d : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hC : ∀ t ∈ Icc a b, |d t| ≤ C) :
    |f b - f a| ≤ C * (b-a) := by
  simpa only [Real.norm_eq_abs] using
    (norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hd t ht).hasDerivWithinAt)
      (fun t ht => by
        simpa only [Real.norm_eq_abs] using hC t (Ico_subset_Icc_self ht))
      b (right_mem_Icc.mpr hab))

noncomputable def reciprocalHessian (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Real.sqrt (q t))⁻¹

noncomputable def reciprocalSlope (q c : ℝ → ℝ) (t : ℝ) : ℝ :=
  -c t / (2 * q t * Real.sqrt (q t))

/-- Differentiate the reciprocal square root of the *actual* second
derivative. The sign agrees with `(q^(-1/2))' = -q'/(2*q^(3/2))`. -/
theorem reciprocalHessian_hasDerivAt {q c : ℝ → ℝ} {t : ℝ}
    (hd : HasDerivAt q (c t) t) (hq : 0 < q t) :
    HasDerivAt (reciprocalHessian q) (reciprocalSlope q c t) t := by
  have hs : 0 < Real.sqrt (q t) := Real.sqrt_pos.mpr hq
  have hs2 : (Real.sqrt (q t))^2 = q t := Real.sq_sqrt hq.le
  have heq : reciprocalSlope q c t =
      -(c t / (2 * Real.sqrt (q t))) / (Real.sqrt (q t))^2 := by
    dsimp [reciprocalSlope]
    rw [hs2]
    field_simp [hq.ne', hs.ne']
    <;> ring
  rw [heq]
  exact (hd.sqrt hq.ne').inv hs.ne'

/-- Standard diagonal SC gives a derivative bound, rather than postulating
a Lipschitz or line-integral inequality. -/
theorem reciprocalSlope_abs_le_one {q c : ℝ → ℝ} {t : ℝ}
    (hq : 0 < q t)
    (hsc : |c t| ≤ 2 * q t * Real.sqrt (q t)) :
    |reciprocalSlope q c t| ≤ 1 := by
  have hd : 0 < 2 * q t * Real.sqrt (q t) := by positivity
  rw [reciprocalSlope, abs_div, abs_neg, abs_of_pos hd]
  exact (div_le_one hd).mpr hsc

/-- Reciprocal-Hessian integration on any closed interval in the actual
line domain. This also supplies the lower-Hessian comparison used in
standard conjugate-barrier boundary proofs; no conjugate is asserted here. -/
theorem reciprocalHessian_lipschitz {q c : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt q (c t) t)
    (hq : ∀ t ∈ Icc a b, 0 < q t)
    (hsc : ∀ t ∈ Icc a b,
      |c t| ≤ 2 * q t * Real.sqrt (q t)) :
    |reciprocalHessian q b - reciprocalHessian q a| ≤ b-a := by
  simpa only [one_mul] using abs_increment_le (C := 1) hab
    (fun t ht => reciprocalHessian_hasDerivAt (hd t ht) (hq t ht))
    (fun t ht => reciprocalSlope_abs_le_one (hq t ht) (hsc t ht))

/-- An explicit uniform upper bound before any finite endpoint strictly
inside the initial Dikin radius. The functions are respectively the value,
first, second, and third derivatives along one line. Their only premises
are genuine derivative equalities, Hessian positivity, and diagonal SC.

The proof integrates three times: first `1/sqrt(q)`, then `g`, then `f`.
Consequently finite-boundary divergence cannot occur at this endpoint.
-/
theorem selfConcordant_finite_segment_upper
    {f g q c : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : ∀ t ∈ Ico 0 T, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Ico 0 T, HasDerivAt g (q t) t)
    (hq : ∀ t ∈ Ico 0 T, HasDerivAt q (c t) t)
    (hpos : ∀ t ∈ Ico 0 T, 0 < q t)
    (hsc : ∀ t ∈ Ico 0 T,
      |c t| ≤ 2 * q t * Real.sqrt (q t))
    (hradius : T < (Real.sqrt (q 0))⁻¹) :
    ∀ t ∈ Ico 0 T,
      f t ≤ f 0 + (|g 0| +
        ((Real.sqrt (q 0))⁻¹ - T)⁻¹ ^ 2 * T) * T := by
  let m : ℝ := (Real.sqrt (q 0))⁻¹ - T
  let M : ℝ := m⁻¹ ^ 2
  let C : ℝ := |g 0| + M*T
  have hm : 0 < m := sub_pos.mpr hradius
  have hM : 0 ≤ M := sq_nonneg _
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (mul_nonneg hM hT.le)
  have hqbound : ∀ t ∈ Ico 0 T, q t ≤ M := by
    intro t ht
    have hsub : Icc 0 t ⊆ Ico 0 T := by
      intro u hu
      exact ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩
    have hr := reciprocalHessian_lipschitz ht.1
      (fun u hu => hq u (hsub hu))
      (fun u hu => hpos u (hsub hu))
      (fun u hu => hsc u (hsub hu))
    have hrmin : m ≤ (Real.sqrt (q t))⁻¹ := by
      have hh := (abs_le.mp hr).1
      dsimp [reciprocalHessian] at hh
      have hh' : (Real.sqrt (q 0))⁻¹ - t ≤ (Real.sqrt (q t))⁻¹ := by
        linarith
      dsimp [m]
      linarith [hh', ht.2]
    have hs : 0 < Real.sqrt (q t) := Real.sqrt_pos.mpr (hpos t ht)
    have hmul : m * Real.sqrt (q t) ≤ 1 := by
      rw [inv_eq_one_div] at hrmin
      exact (le_div_iff₀ hs).mp hrmin
    have hsbound : Real.sqrt (q t) ≤ m⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hm).mpr
      nlinarith
    calc
      q t = (Real.sqrt (q t))^2 := (Real.sq_sqrt (hpos t ht).le).symm
      _ ≤ m⁻¹ ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self hs.le hsbound
      _ = M := rfl
  have hgbound : ∀ t ∈ Ico 0 T, |g t| ≤ C := by
    intro t ht
    have hsub : Icc 0 t ⊆ Ico 0 T := by
      intro u hu
      exact ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩
    have hgdiff := abs_increment_le ht.1
      (fun u hu => hg u (hsub hu))
      (fun u hu => by
        rw [abs_of_pos (hpos u (hsub hu))]
        exact hqbound u (hsub hu))
    have htri : |g t| ≤ |g t - g 0| + |g 0| := by
      calc
        |g t| = |(g t - g 0) + g 0| := by rw [sub_add_cancel]
        _ ≤ |g t - g 0| + |g 0| := abs_add_le _ _
    have hprod : M*t ≤ M*T := mul_le_mul_of_nonneg_left ht.2.le hM
    dsimp [C]
    linarith
  intro t ht
  have hsub : Icc 0 t ⊆ Ico 0 T := by
    intro u hu
    exact ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩
  have hfdiff := abs_increment_le ht.1
    (fun u hu => hf u (hsub hu))
    (fun u hu => hgbound u (hsub hu))
  have hprod : C*t ≤ C*T := mul_le_mul_of_nonneg_left ht.2.le hC
  have habs := le_abs_self (f t-f 0)
  change f t ≤ f 0 + C*T
  linarith

end D5.S3.Analytic.ConvexBarrier
