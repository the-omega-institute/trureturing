/- GID: D5/S1/Dynamics/Symbolic/KhetanThreePointRoot
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Unit-circle rigidity for a three-term Fourier mask. -/

import Mathlib

/-! A three-point mask can vanish on the unit circle only at the cubic
roots.  This is the algebraic step used by the Fourier proof of the
one-dimensional three-point tiling lemma. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanThreePointRoot

theorem unit_circle_three_term_root
    {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hzero : 1 + u + v = 0) :
    u ^ 2 + u + 1 = 0 ∧ v ^ 2 + v + 1 = 0 := by
  have huv : v = -1 - u := by linear_combination hzero
  have hnormv : ‖1 + u‖ ^ 2 = (1 : ℝ) := by
    rw [show 1 + u = -v by linear_combination huv]
    rw [norm_neg, hv]
    norm_num
  have hmul_u : u * star u = (1 : ℂ) := by
    have hnorm_u : ‖u‖ ^ 2 = (1 : ℝ) := by rw [hu]; norm_num
    calc
      u * star u = (Complex.normSq u : ℂ) := by
        simpa using (Complex.mul_conj u)
      _ = (‖u‖ : ℂ) ^ 2 := by
        norm_cast
        exact Complex.normSq_eq_norm_sq u
      _ = 1 := by rw [hu]; norm_num
  have hmul_one_u : (1 + u) * star (1 + u) = (1 : ℂ) := by
    have hnorm : ‖(1 + u)‖ ^ 2 = (1 : ℝ) := hnormv
    calc
      (1 + u) * star (1 + u) = (Complex.normSq (1 + u) : ℂ) := by
        simpa using (Complex.mul_conj (1 + u))
      _ = (‖(1 + u)‖ : ℂ) ^ 2 := by
        norm_cast
        exact Complex.normSq_eq_norm_sq (1 + u)
      _ = 1 := by
        have habs : ‖1 + u‖ = (1 : ℝ) := by
          nlinarith [hnorm, norm_nonneg (1 + u)]
        rw [habs]
        norm_num
  have hconj : star u = -1 - u := by
    have hstar : star (1 + u) = 1 + star u := by simp
    rw [hstar] at hmul_one_u
    have hexpand : (1 + u) * (1 + star u) =
        1 + star u + u + u * star u := by ring
    rw [hexpand, hmul_u] at hmul_one_u
    linear_combination hmul_one_u
  have huquad : u ^ 2 + u + 1 = 0 := by
    have hmul := congrArg (fun z : ℂ => u * z) hconj
    rw [hmul_u] at hmul
    linear_combination hmul
  have hvquad : v ^ 2 + v + 1 = 0 := by
    rw [huv]
    linear_combination huquad
  exact ⟨huquad, hvquad⟩

theorem unit_circle_three_term_root_cubed
    {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hzero : 1 + u + v = 0) :
    u ^ 3 = 1 ∧ v ^ 3 = 1 := by
  rcases unit_circle_three_term_root hu hv hzero with ⟨huq, hvq⟩
  constructor
  · linear_combination (u - 1) * huq
  · linear_combination (v - 1) * hvq

end D5.S1.Dynamics.Symbolic.KhetanThreePointRoot
