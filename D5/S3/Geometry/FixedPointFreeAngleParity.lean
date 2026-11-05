/- GID: D5/S3/Geometry/FixedPointFreeAngleParity
   generality: G
   mirror-B: D5/B/S3/Geometry/FixedPointFreeAngleParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed-point-free involution forces an interval-bounded angle sum away from two pi. -/

/- Escape audit unfinished for the public theorem:
   https://github.com/the-omega-institute/trureturing/issues/24594.
   No declared_validated registration is claimed. -/

import D5.S3.PrimeForms.Crossing.GlideCrossingParity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S3.Geometry.FixedPointFreeAngleParity

open scoped BigOperators

private theorem sum_lt_card_mul {Crossing : Type*} [Fintype Crossing]
    (w : Crossing → ℝ) (c : ℝ) (hc : ∀ x, w x < c) (hne : Nonempty Crossing) :
    (∑ x, w x) < (Fintype.card Crossing : ℝ) * c := by
  let s : Finset Crossing := Finset.univ
  have hs : s.Nonempty := by
    simpa [s] using hne
  have hsum : s.sum w < s.sum (fun _ => c) := by
    apply Finset.sum_lt_sum_of_nonempty hs
    intro x hx
    exact hc x
  simpa [s, Finset.sum_const, nsmul_eq_mul] using hsum

private theorem card_mul_lt_sum {Crossing : Type*} [Fintype Crossing]
    (w : Crossing → ℝ) (c : ℝ) (hc : ∀ x, c < w x) (hne : Nonempty Crossing) :
    (Fintype.card Crossing : ℝ) * c < ∑ x, w x := by
  let s : Finset Crossing := Finset.univ
  have hs : s.Nonempty := by
    simpa [s] using hne
  have hsum : s.sum (fun _ => c) < s.sum w := by
    apply Finset.sum_lt_sum_of_nonempty hs
    intro x hx
    exact hc x
  simpa [s, Finset.sum_const, nsmul_eq_mul] using hsum

/-- A finite even family of angles in `(π/3, π/2)` cannot sum to `2π`.

The proof separates the even cardinalities `0`, `2`, `4`, and at least `6`.
The strict interval bounds rule out the first three upper-bound cases and the
last lower-bound case. -/
private theorem even_interval_sum_ne_two_pi {Crossing : Type*} [Fintype Crossing]
    (w : Crossing → ℝ) (hEven : Even (Fintype.card Crossing))
    (hLower : ∀ x, Real.pi / 3 < w x)
    (hUpper : ∀ x, w x < Real.pi / 2) :
    (∑ x, w x) ≠ 2 * Real.pi := by
  classical
  obtain ⟨k, hk⟩ := hEven
  by_cases hk0 : k = 0
  · subst k
    have hcard : Fintype.card Crossing = 0 := by simpa using hk
    haveI : IsEmpty Crossing := Fintype.card_eq_zero_iff.mp hcard
    simp
  by_cases hk1 : k = 1
  · subst k
    have hcard : Fintype.card Crossing = 2 := by simpa using hk
    haveI : Nonempty Crossing := Fintype.card_pos_iff.mp (by omega)
    have hlt := sum_lt_card_mul w (Real.pi / 2) hUpper inferInstance
    rw [hcard] at hlt
    intro hsum
    norm_num at hlt
    nlinarith [Real.pi_pos]
  by_cases hk2 : k = 2
  · subst k
    have hcard : Fintype.card Crossing = 4 := by simpa using hk
    haveI : Nonempty Crossing := Fintype.card_pos_iff.mp (by omega)
    have hlt := sum_lt_card_mul w (Real.pi / 2) hUpper inferInstance
    rw [hcard] at hlt
    intro hsum
    norm_num at hlt
    nlinarith [Real.pi_pos]
  have hk3 : 3 ≤ k := by omega
  have hcard : 6 ≤ Fintype.card Crossing := by omega
  haveI : Nonempty Crossing := Fintype.card_pos_iff.mp (by omega)
  have hgt := card_mul_lt_sum w (Real.pi / 3) hLower inferInstance
  rw [show (Fintype.card Crossing : ℝ) * (Real.pi / 3) =
      (Fintype.card Crossing : ℝ) * Real.pi / 3 by ring] at hgt
  intro hsum
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcardR : (6 : ℝ) ≤ Fintype.card Crossing := by exact_mod_cast hcard
  have hbound : 2 * Real.pi ≤ (Fintype.card Crossing : ℝ) * Real.pi / 3 := by
    nlinarith [hcardR, Real.pi_pos]
  nlinarith [hbound]

/- A finite fixed-point-free involution is the parity source used by the
   low-face transport argument. -/
theorem fixed_point_free_involution_interval_sum_ne_two_pi
    {Crossing : Type*} [Fintype Crossing]
    (glide : Crossing → Crossing) (hInvolutive : Function.Involutive glide)
    (hFixedPointFree : ∀ crossing, glide crossing ≠ crossing)
    (angle : Crossing → ℝ)
    (hLower : ∀ x, Real.pi / 3 < angle x)
    (hUpper : ∀ x, angle x < Real.pi / 2) :
    (∑ x, angle x) ≠ 2 * Real.pi := by
  apply even_interval_sum_ne_two_pi angle
    (D5.S3.PrimeForms.Crossing.GlideCrossingParity.glide_crossing_count_even
      glide hInvolutive hFixedPointFree)
    hLower hUpper

#print axioms fixed_point_free_involution_interval_sum_ne_two_pi

end D5.S3.Geometry.FixedPointFreeAngleParity
