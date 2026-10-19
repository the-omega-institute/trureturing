/- GID: D5/S3/Geometry/Hyperideal/EvenAngleSumObstruction
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/EvenAngleSumObstruction
   mirror-E: none(waiver:finite-even-angle-obstruction)
   anchors: []
   utility: none
   digest: An even number of middle angles cannot sum to two pi when every angle lies strictly between pi over three and pi over two. -/

import Mathlib.Tactic

/-! The analytic parity obstruction used by the low-face transport argument. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.EvenAngleSumObstruction

variable {T : Type*} [Fintype T]

/-- A finite even-cardinality family of strict middle angles cannot close at `2 * pi`. -/
theorem even_middle_angle_sum_ne_two_pi (angle : T → ℝ)
    (heven : Even (Fintype.card T))
    (hrange : ∀ t, Real.pi / 3 < angle t ∧ angle t < Real.pi / 2) :
    (∑ t, angle t) ≠ 2 * Real.pi := by
  classical
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      letI := hempty
      simp [Real.pi_pos.ne']
  | inr hnonempty =>
      letI := hnonempty
      rcases heven with ⟨k, hk⟩
      have hcard_pos : 0 < Fintype.card T := Fintype.card_pos_iff.mpr hnonempty
      have hsum_upper : (∑ t : T, angle t) < (Fintype.card T : ℝ) * (Real.pi / 2) := by
        simpa [Finset.sum_const, nsmul_eq_mul] using
          (Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset T))
            (f := fun t : T => angle t) (g := fun _ : T => Real.pi / 2)
            Finset.univ_nonempty (fun t ht => (hrange t).2))
      have hsum_lower : (Fintype.card T : ℝ) * (Real.pi / 3) < ∑ t : T, angle t := by
        simpa [Finset.sum_const, nsmul_eq_mul] using
          (Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset T))
            (f := fun _ : T => Real.pi / 3) (g := fun t : T => angle t)
            Finset.univ_nonempty (fun t ht => (hrange t).1))
      by_cases hk_small : k ≤ 2
      · have hcard_le : Fintype.card T ≤ 4 := by omega
        have hcard_le_real : (Fintype.card T : ℝ) ≤ 4 := by exact_mod_cast hcard_le
        intro hsum
        nlinarith [Real.pi_pos]
      · have hk_large : 3 ≤ k := by omega
        have hcard_ge : 6 ≤ Fintype.card T := by omega
        have hcard_ge_real : (6 : ℝ) ≤ (Fintype.card T : ℝ) := by exact_mod_cast hcard_ge
        intro hsum
        nlinarith [Real.pi_pos]

#print axioms even_middle_angle_sum_ne_two_pi

end D5.S3.Geometry.Hyperideal.EvenAngleSumObstruction
