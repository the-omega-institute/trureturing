/- GID: D5/S3/Analytic/ConvexBarrier/ScalarAlgebra
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/ScalarAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Algebraic parts of Zhang--Fu--Dai, arXiv:2611.06404v1, Lemmas 3.2--3.4.
The mixed-cubic argument below replaces their Bernstein citation by three
explicit evaluations.  These lemmas do NOT supply Dikin containment,
conjugacy, or the analytic radial derivative identities.
Source only: not elaborated or kernel checked.
Intended canonical subject: D5/S3/Analytic/ConvexBarrier.
-/

namespace D5.S3.Analytic.ConvexBarrier

/-- Algebra after differentiating the actual homogeneous extension.  The
chain rule supplying the left sides is a separate analytic obligation. -/
theorem radial_hessian_identity (a d b : ℝ) :
    a^2 + b - 2*a*d = (a-d)^2 + (b-d^2) := by ring

theorem radial_cubic_identity (a d b t : ℝ) :
    -2*a^3 + t - 6*a*b + 6*a^2*d =
      -2*(a-d)^3 - 6*(a-d)*(b-d^2) + (t-6*b*d+4*d^3) := by ring

noncomputable def primalQuadratic (ν A Q t : ℝ) : ℝ :=
  ν * (1 - 2 * A * t + (A ^ 2 + Q) * t ^ 2)

noncomputable def dualQuadratic (ν A Q t : ℝ) : ℝ :=
  ((A ^ 2 + Q) * t ^ 2 - 2 * ν * Q * t + ν ^ 2 * Q) / (ν * Q)

/-- The two actual quadratic minima in Lemma 3.2.  The hypotheses are
explicit ellipsoid-exclusion inequalities, not asserted facts about barriers. -/
theorem dikin_quadratic_consequences {ν A Q : ℝ}
    (hν : 0 < ν) (hA : 0 < A) (hQ : 0 < Q)
    (hp : ∀ t : ℝ, 0 < t → 1 ≤ primalQuadratic ν A Q t)
    (hd : ∀ t : ℝ, 0 < t → 1 ≤ dualQuadratic ν A Q t) :
    A ^ 2 ≤ (ν - 1) * Q ∧ Q ≤ (ν - 1) * A ^ 2 ∧ 2 ≤ ν := by
  have hS : 0 < A ^ 2 + Q := by positivity
  have ep : primalQuadratic ν A Q (A / (A ^ 2 + Q)) = ν * Q / (A ^ 2 + Q) := by
    unfold primalQuadratic
    field_simp [hS.ne']
    <;> ring
  have ed : dualQuadratic ν A Q (ν * Q / (A ^ 2 + Q)) =
      ν * A ^ 2 / (A ^ 2 + Q) := by
    unfold dualQuadratic
    field_simp [hS.ne', hν.ne', hQ.ne']
    <;> ring
  have h1 := hp (A / (A ^ 2 + Q)) (div_pos hA hS)
  have h2 := hd (ν * Q / (A ^ 2 + Q)) (div_pos (mul_pos hν hQ) hS)
  rw [ep, le_div_iff₀ hS] at h1
  rw [ed, le_div_iff₀ hS] at h2
  have hp' : A ^ 2 ≤ (ν - 1) * Q := by nlinarith
  have hd' : Q ≤ (ν - 1) * A ^ 2 := by nlinarith
  have hρ : 0 < ν - 1 := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hQ.le
    nlinarith [sq_pos_of_pos hA]
  have hprod := mul_le_mul_of_nonneg_left hd' hρ.le
  have hsq' : 1 * A ^ 2 ≤ (ν - 1) ^ 2 * A ^ 2 := by
    nlinarith [hp', hprod]
  have hsq : 1 ≤ (ν - 1) ^ 2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hA)).mp
    simpa [mul_comm] using hsq'
  have hρ1 : 1 ≤ ν-1 := le_of_sq_le_sq (by simpa using hsq) hρ.le
  exact ⟨hp', hd', by linarith⟩

/-- Taking square roots gives both normalized chord inequalities, with
`Q = q*delta^2`, `A = 1-a*delta`, and `s = sqrt(nu-1)`. -/
theorem normalized_chord_bounds {A Q s : ℝ} (hA : 0 < A) (hQ : 0 < Q)
    (hs : 0 < s) (hp : A ^ 2 ≤ s ^ 2 * Q) (hd : Q ≤ s ^ 2 * A ^ 2) :
    1 / s ≤ A / Real.sqrt Q ∧ A / Real.sqrt Q ≤ s := by
  have ht : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have ht2 := Real.sq_sqrt hQ.le
  have ha : A ≤ s * Real.sqrt Q := by
    apply le_of_sq_le_sq _ (mul_pos hs ht).le
    nlinarith [hp, congrArg (fun t : ℝ => s^2*t) ht2]
  have hb : Real.sqrt Q ≤ s * A := by
    apply le_of_sq_le_sq _ (mul_pos hs hA).le
    nlinarith [hd]
  constructor
  · apply (le_div_iff₀ ht).2
    have hdiv : Real.sqrt Q / s ≤ A := (div_le_iff₀ hs).2 (by nlinarith [hb])
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  · exact (div_le_iff₀ ht).2 (by nlinarith [ha])

/-- Sharp normalized projective cubic bound.  Squared SC is tested at the
two radial directions `u = ±1/s`, so no Hildebrand theorem is assumed.
To apply this to a barrier one must still prove its radial chain-rule formula
and normalize `q>0`; that analytic bridge is not present in this file. -/
theorem sharp_projective_cubic {s τ : ℝ} (hs : 1 ≤ s)
    (hsc : ∀ u : ℝ, (-2 * u ^ 3 - 6 * u + τ) ^ 2 ≤
      4 * (s ^ 2 + 1) * (u ^ 2 + 1) ^ 3) :
    |τ| ≤ 2 * (s ^ 2 - 1) / s := by
  have hs0 : 0 < s := by linarith
  have hn : s ≠ 0 := hs0.ne'
  have hm : (τ * s ^ 3 + 2 + 6 * s ^ 2) ^ 2 ≤ (2 * (s ^ 2 + 1) ^ 2) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (hsc (-1 / s)) (sq_nonneg (s ^ 3))
    convert h using 1 <;> field_simp [hn] <;> ring
  have hp : (-τ * s ^ 3 + 2 + 6 * s ^ 2) ^ 2 ≤ (2 * (s ^ 2 + 1) ^ 2) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (hsc (1 / s)) (sq_nonneg (s ^ 3))
    convert h using 1 <;> field_simp [hn] <;> ring
  have hm' := le_of_sq_le_sq hm (by positivity)
  have hp' := le_of_sq_le_sq hp (by positivity)
  have hupper : τ * s ≤ 2 * (s ^ 2 - 1) := by
    have : (τ * s - 2 * (s ^ 2 - 1)) * s ^ 2 ≤ 0 := by nlinarith [hm']
    linarith [nonpos_of_mul_nonpos_left this (sq_pos_of_pos hs0)]
  have hlower : -τ * s ≤ 2 * (s ^ 2 - 1) := by
    have : (-τ * s - 2 * (s ^ 2 - 1)) * s ^ 2 ≤ 0 := by nlinarith [hp']
    linarith [nonpos_of_mul_nonpos_left this (sq_pos_of_pos hs0)]
  apply abs_le.2
  constructor
  · have := (le_div_iff₀ hs0).2 hlower
    linarith
  · exact (le_div_iff₀ hs0).2 hupper

def binaryCubic (a b d e u v : ℝ) : ℝ :=
  a * u ^ 3 + 3 * b * u ^ 2 * v + 3 * d * u * v ^ 2 + e * v ^ 3

/-- A symmetric binary cubic's mixed coefficient is bounded by its diagonal
norm on the Euclidean circle.  This is Lemma 3.4 in orthonormal coordinates.
The proof is finite algebra and uses no Bernstein or polarization supplier. -/
theorem mixed_binary_cubic_bound {a b d e M : ℝ}
    (h : ∀ u v : ℝ, |binaryCubic a b d e u v| ≤
      M * (u ^ 2 + v ^ 2) * Real.sqrt (u ^ 2 + v ^ 2)) : |d| ≤ M := by
  have h0 : |a| ≤ M := by simpa [binaryCubic] using h 1 0
  have ht : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr : (1 : ℝ) ^ 2 + (Real.sqrt 3) ^ 2 = 4 := by nlinarith
  have hr' : (1 : ℝ) ^ 2 + (-Real.sqrt 3) ^ 2 = 4 := by nlinarith
  have hp := h 1 (Real.sqrt 3)
  have hm := h 1 (-Real.sqrt 3)
  rw [hr] at hp
  rw [hr'] at hm
  norm_num at hp hm
  have hp' := abs_le.1 hp
  have hm' := abs_le.1 hm
  have h0' := abs_le.1 h0
  have heq : binaryCubic a b d e 1 (Real.sqrt 3) +
      binaryCubic a b d e 1 (-Real.sqrt 3) = 2 * (a + 9 * d) := by
    unfold binaryCubic
    linear_combination (6*d)*ht
  exact abs_le.2 ⟨by nlinarith [hp'.1, hm'.1, h0'.2],
    by nlinarith [hp'.2, hm'.2, h0'.1]⟩

/-- The actual mixed trilinear estimate in any real vector space, on any
orthonormal pair for a bilinear form.  Positivity elsewhere is unnecessary.
This supplies the full tensor form of Lemma 3.4 without a Bernstein premise. -/
theorem mixed_trilinear_bound {E : Type*} [AddCommGroup E] [Module ℝ E]
    (G : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (sym12 : ∀ x y z, T x y z = T y x z)
    (sym23 : ∀ x y z, T x y z = T x z y)
    (e1 e2 : E) (h11 : G e1 e1 = 1) (h22 : G e2 e2 = 1)
    (h12 : G e1 e2 = 0) (h21 : G e2 e1 = 0) (M : ℝ)
    (h : ∀ x, |T x x x| ≤ M * G x x * Real.sqrt (G x x)) :
    |T e1 e2 e2| ≤ M := by
  have h121 : T e1 e2 e1 = T e1 e1 e2 := sym23 e1 e2 e1
  have h211 : T e2 e1 e1 = T e1 e1 e2 := (sym12 e2 e1 e1).trans h121
  have h212 : T e2 e1 e2 = T e1 e2 e2 := sym12 e2 e1 e2
  have h221 : T e2 e2 e1 = T e1 e2 e2 := (sym23 e2 e2 e1).trans h212
  apply mixed_binary_cubic_bound (a := T e1 e1 e1) (b := T e1 e1 e2)
    (e := T e2 e2 e2)
  intro u v
  have hc : T (u • e1 + v • e2) (u • e1 + v • e2) (u • e1 + v • e2) =
      binaryCubic (T e1 e1 e1) (T e1 e1 e2) (T e1 e2 e2) (T e2 e2 e2) u v := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, h121, h211, h212, h221, binaryCubic]
    ring
  have hg : G (u • e1 + v • e2) (u • e1 + v • e2) = u^2+v^2 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, h11, h22, h12, h21]
    ring
  have hh := h (u • e1 + v • e2)
  rw [hc, hg] at hh
  exact hh

/-- The vertical primal/dual chord consequence is strictly positive. -/
theorem vertical_kappa_lower {s k w z : ℝ} (hs : 0 < s) (hk : 0 < k)
    (hm : 1 / s ≤ (w + z) * Real.sqrt k)
    (hp : 1 / s ≤ (w - z) * Real.sqrt k) : 1 / s ^ 2 ≤ k * w ^ 2 := by
  have ht := Real.sq_sqrt hk.le
  have hm0 : 0 ≤ (w + z) * Real.sqrt k := le_trans (by positivity) hm
  have hmul := mul_le_mul hm hp (by positivity : 0 ≤ 1 / s) hm0
  have heq : ((w + z) * Real.sqrt k) * ((w - z) * Real.sqrt k) =
      k * (w ^ 2 - z ^ 2) := by linear_combination (w^2-z^2)*ht
  rw [heq] at hmul
  have hz : 0 ≤ k * z ^ 2 := mul_nonneg hk.le (sq_nonneg z)
  have hrecip : (1 / s) * (1 / s) = 1 / s ^ 2 := by
    field_simp [hs.ne'] <;> ring
  rw [hrecip] at hmul
  nlinarith

end D5.S3.Analytic.ConvexBarrier
