/- GID: D5/S3/Analytic/Laplace/EulerFirstMomentLocal
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/EulerFirstMomentLocal
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: The first-moment Euler equation gives local holomorphic continuation across a nonzero real cut. -/

import D5.S3.Analytic.Laplace.EulerLocalContinuation

/-!
# Local continuation of the first-moment transform

For the forward-window Robin criterion, `F` is the tail Laplace transform of the
signed theta signal. The first-moment transform is `L = -deriv F`. Differentiating
`z * deriv (deriv F) z + 2 * deriv F z = Φ z` gives the equation below with
`P = -deriv Φ`, as in `ForwardWindowLaplace.neg_deriv_euler_of_first_moment`.
-/

noncomputable section
open Complex Set Metric

namespace D5.S3.Analytic.Laplace.EulerFirstMomentLocal

open EulerLocalContinuation (rightHalfDisk)

private theorem isOpen_rightHalfDisk (c r : ℝ) : IsOpen (rightHalfDisk c r) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)

private theorem isPreconnected_rightHalfDisk (c r : ℝ) : IsPreconnected (rightHalfDisk c r) :=
  ((convex_ball (c : ℂ) r).inter (convex_halfSpace_re_gt c)).isPreconnected

/-- The first-moment Euler equation extends its solution across a nonzero real cut. -/
theorem exists_extension_of_ne_zero {c r : ℝ} (hc : c ≠ 0) (hr : 0 < r)
    {P L : ℂ → ℂ} (hP : DifferentiableOn ℂ P (ball (c : ℂ) r))
    (hL : DifferentiableOn ℂ L (rightHalfDisk c r))
    (hode : ∀ z ∈ rightHalfDisk c r,
      z * deriv (deriv L) z + 3 * deriv L z = P z) :
    ∃ δ : ℝ, 0 < δ ∧ δ < r ∧ ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (ball (c : ℂ) δ) ∧ EqOn H L (rightHalfDisk c δ) := by
  have hweighted : DifferentiableOn ℂ (fun z => z ^ 2 * P z) (ball (c : ℂ) r) :=
    (differentiableOn_pow 2).mul hP
  obtain ⟨Q, hQ⟩ := hweighted.isExactOn_ball
  have ho := isOpen_rightHalfDisk c r
  let D : ℂ → ℂ := fun z => z ^ 3 * deriv L z - Q z
  have hD : ∀ z ∈ rightHalfDisk c r, HasDerivAt D 0 z := by
    intro z hz
    have hdL := (hL.deriv ho).hasDerivAt (ho.mem_nhds hz)
    have hpow : HasDerivAt (fun w : ℂ => w ^ 3) (3 * z ^ 2) z := by
      simpa only [Nat.cast_ofNat, Nat.reduceSub] using hasDerivAt_pow 3 z
    have hzero : 3 * z ^ 2 * deriv L z + z ^ 3 * deriv (deriv L) z - z ^ 2 * P z = 0 := by
      linear_combination (z ^ 2) * (hode z hz)
    exact ((hpow.mul hdL).sub (hQ z hz.1)).congr_deriv hzero
  obtain ⟨A, hA⟩ := ho.exists_is_const_of_deriv_eq_zero (isPreconnected_rightHalfDisk c r)
    (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hD z hz).deriv)

  let δ := min (r / 2) (‖(c : ℂ)‖ / 2)
  have hn : 0 < ‖(c : ℂ)‖ := norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr hc)
  have hδ : 0 < δ := lt_min (half_pos hr) (half_pos hn)
  have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
  have hsub : ball (c : ℂ) δ ⊆ ball (c : ℂ) r := ball_subset_ball hδr.le
  have hhalfsub : rightHalfDisk c δ ⊆ rightHalfDisk c r :=
    fun _ hz => ⟨hsub hz.1, hz.2⟩
  have hnz : ∀ z ∈ ball (c : ℂ) δ, z ≠ 0 := by
    intro z hz he
    subst z
    have hz' : ‖(c : ℂ)‖ < δ := by simpa [mem_ball, dist_eq_norm] using hz
    have hbound : δ ≤ ‖(c : ℂ)‖ / 2 := min_le_right _ _
    linarith

  let W : ℂ → ℂ := fun z => (Q z + A) / z ^ 3
  have hWd : DifferentiableOn ℂ W (ball (c : ℂ) δ) := by
    have hQd : DifferentiableOn ℂ Q (ball (c : ℂ) δ) :=
      fun z hz => (hQ z (hsub hz)).differentiableAt.differentiableWithinAt
    exact (hQd.add (differentiableOn_const A)).div (differentiableOn_pow 3)
      (fun z hz => pow_ne_zero 3 (hnz z hz))
  obtain ⟨G, hG⟩ := hWd.isExactOn_ball
  have hGd : DifferentiableOn ℂ G (ball (c : ℂ) δ) :=
    fun z hz => (hG z hz).differentiableAt.differentiableWithinAt
  have hderiv : EqOn (deriv L) (deriv G) (rightHalfDisk c δ) := by
    intro z hz
    rw [(hG z hz.1).deriv]
    change deriv L z = (Q z + A) / z ^ 3
    symm
    apply (div_eq_iff (pow_ne_zero 3 (hnz z hz.1))).mpr
    have ha : z ^ 3 * deriv L z - Q z = A := hA z (hhalfsub hz)
    linear_combination -ha
  obtain ⟨B, hB⟩ := (isOpen_rightHalfDisk c δ).exists_eq_add_of_deriv_eq
    (isPreconnected_rightHalfDisk c δ) (hL.mono hhalfsub) (hGd.mono fun _ hz => hz.1) hderiv
  exact ⟨δ, hδ, hδr, fun z => G z + B, hGd.add (differentiableOn_const B), hB.symm⟩

end D5.S3.Analytic.Laplace.EulerFirstMomentLocal
