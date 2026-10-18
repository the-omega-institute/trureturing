/- GID: D5/S3/Geometry/Hyperideal/IridescentEdgeCycleParity
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/IridescentEdgeCycleParity
   mirror-E: none(waiver:rainbow-endpoint-transport)
   anchors: []
   utility: none
   digest: A finite normal-edge cycle with a transported pair of distinct non-target colors has even length. -/

import D5.S3.PrimeForms.Crossing.GlideCrossingParity
import Mathlib

/-! The endpoint-color swap is the parity-bearing part of the normal-edge
circle argument. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.IridescentEdgeCycleParity

/-! The local geometric input is the ordered pair of the two colors seen from
the chosen endpoint of a target edge.  A passage through a rainbow tetrahedron
swaps that pair.  The structure below isolates exactly this transport law from
the face-pairing bookkeeping. -/

structure RainbowCycle (I : Type*) [Fintype I] where
  next : Equiv.Perm I
  firstColor : I → Fin 3
  secondColor : I → Fin 3
  distinct : ∀ i, firstColor i ≠ secondColor i
  transported : ∀ i,
    firstColor (next i) = secondColor i ∧
      secondColor (next i) = firstColor i

private def orientation {I : Type*} [Fintype I] (c : RainbowCycle I) : I → Bool :=
  fun i => decide (c.firstColor i < c.secondColor i)

private theorem pair_order_flip (a b : Fin 3) (h : a ≠ b) :
    decide (b < a) = !(decide (a < b)) := by
  fin_cases a <;> fin_cases b <;> simp_all

private theorem orientation_next {I : Type*} [Fintype I]
    (c : RainbowCycle I) (i : I) :
    orientation c (c.next i) = !(orientation c i) := by
  obtain ⟨hlr, hrl⟩ := c.transported i
  have hne := c.distinct i
  simpa [orientation, hlr, hrl] using
    pair_order_flip (c.firstColor i) (c.secondColor i) hne

private theorem orientation_symm {I : Type*} [Fintype I]
    (c : RainbowCycle I) (i : I) :
    orientation c (c.next.symm i) = !(orientation c i) := by
  have h := orientation_next c (c.next.symm i)
  simpa using h.symm

/-- Swapping the two distinct endpoint colors at every successor forces an
even number of occurrences in the finite cycle. -/
theorem even_card_of_rainbow_cycle {I : Type*} [Fintype I]
    (c : RainbowCycle I) : Even (Fintype.card I) := by
  let glide : I → I := fun i =>
    if orientation c i then c.next.symm i else c.next i
  have hglide : Function.Involutive glide := by
    intro i
    by_cases h : orientation c i
    · have hs : orientation c (c.next.symm i) = false := by
        rw [orientation_symm c i, h]
        decide
      simp [glide, h, hs, c.next.apply_symm_apply]
    · have hn : orientation c (c.next i) = true := by
        have h' : orientation c i = false := Bool.eq_false_iff.mpr h
        rw [orientation_next c i, h']
        decide
      simp [glide, h, hn, c.next.symm_apply_apply]
  have hfixed : ∀ i, glide i ≠ i := by
    intro i hfix
    by_cases h : orientation c i
    · have hs := orientation_symm c i
      have hfix' : c.next.symm i = i := by simpa [glide, h] using hfix
      rw [hfix'] at hs
      simp [h] at hs
    · have hn := orientation_next c i
      have hfix' : c.next i = i := by simpa [glide, h] using hfix
      rw [hfix'] at hn
      simp [h] at hn
  exact D5.S3.PrimeForms.Crossing.GlideCrossingParity.glide_crossing_count_even
    glide hglide hfixed

#print axioms even_card_of_rainbow_cycle

end D5.S3.Geometry.Hyperideal.IridescentEdgeCycleParity
