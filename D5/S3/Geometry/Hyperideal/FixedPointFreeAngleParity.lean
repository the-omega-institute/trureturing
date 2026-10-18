/- GID: D5/S3/Geometry/Hyperideal/FixedPointFreeAngleParity
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FixedPointFreeAngleParity
   mirror-E: none(waiver:finite-low-face-angle-parity)
   anchors: []
   utility: none
   digest: Fixed-point-free face pairing makes zero-or-middle angle sums miss two pi. -/

import D5.S3.Geometry.Hyperideal.EvenAngleSumObstruction
import D5.S3.PrimeForms.Crossing.GlideCrossingParity

/-! The support-parity obstruction for flat and middle angle appearances. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.FixedPointFreeAngleParity

variable {T : Type*} [Fintype T]

/--
If a fixed-point-free involution preserves a family whose entries are either zero
or strict middle angles, the nonzero part cannot sum to `2 * pi`.

The zero entries model flat appearances.  The involution is allowed to pair
zero entries with zero entries and middle entries with middle entries; this is
the support-preserving content needed for the low-face transport argument.
-/
theorem zero_or_middle_angle_sum_ne_two_pi
    (angle : T → ℝ)
    (partner : T → T)
    (hinvolutive : Function.Involutive partner)
    (hfixedPointFree : ∀ t, partner t ≠ t)
    (hpreserves : ∀ t, angle (partner t) = angle t)
    (hshape : ∀ t, angle t = 0 ∨
      (Real.pi / 3 < angle t ∧ angle t < Real.pi / 2)) :
    (∑ t, angle t) ≠ 2 * Real.pi := by
  classical
  let U := {t : T // angle t ≠ 0}
  let partnerU : U → U := fun t =>
    ⟨partner t.1, by
      intro hzero
      apply t.2
      rw [← hpreserves t.1]
      exact hzero⟩
  have hU_involutive : Function.Involutive partnerU := by
    intro t
    apply Subtype.ext
    dsimp [partnerU]
    exact hinvolutive t.1
  have hU_fixedPointFree : ∀ t : U, partnerU t ≠ t := by
    intro t hfixed
    apply hfixedPointFree t.1
    have hval : (partnerU t).1 = t.1 := congrArg Subtype.val hfixed
    simpa [partnerU] using hval
  have hU_even : Even (Fintype.card U) :=
    D5.S3.PrimeForms.Crossing.GlideCrossingParity.glide_crossing_count_even
      partnerU hU_involutive hU_fixedPointFree
  have hU_range : ∀ t : U,
      Real.pi / 3 < angle t.1 ∧ angle t.1 < Real.pi / 2 := by
    intro t
    rcases hshape t.1 with hzero | hmiddle
    · exact False.elim (t.2 hzero)
    · exact hmiddle
  have hU_sum_ne : (∑ t : U, angle t.1) ≠ 2 * Real.pi :=
    D5.S3.Geometry.Hyperideal.EvenAngleSumObstruction.even_middle_angle_sum_ne_two_pi
      (fun t : U => angle t.1) hU_even hU_range
  have hsum_subtype : (∑ t : U, angle t.1) = ∑ t : T, angle t := by
    have hdecomp := Fintype.sum_subtype_add_sum_subtype
      (p := fun t : T => angle t ≠ 0) (f := fun t : T => angle t)
    have hzero : (∑ t : {t : T // ¬ angle t ≠ 0}, angle t.1) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      exact not_not.mp t.2
    calc
      (∑ t : U, angle t.1) = (∑ t : U, angle t.1) + 0 := by simp
      _ = (∑ t : U, angle t.1) +
          (∑ t : {t : T // ¬ angle t ≠ 0}, angle t.1) := by rw [hzero]
      _ = ∑ t : T, angle t := by simpa [U] using hdecomp
  intro hsum
  apply hU_sum_ne
  rw [hsum_subtype]
  exact hsum

#print axioms zero_or_middle_angle_sum_ne_two_pi

end D5.S3.Geometry.Hyperideal.FixedPointFreeAngleParity
