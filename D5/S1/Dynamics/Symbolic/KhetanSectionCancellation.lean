/- GID: D5/S1/Dynamics/Symbolic/KhetanSectionCancellation
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: The 3-by-3 section-cancellation incidence pattern is impossible. -/

import Mathlib

/-! A finite obstruction used in the six-cell section-cancellation argument.

In the only non-product incidence pattern, three two-point sections use the
pairs `01`, `02`, and `12`.  A unit-modulus character cannot cancel on all
three sections: the first two equations identify the two latter phases, while
the third forces the common phase to vanish.  This isolates the exact
contradiction needed before the geometric classification of six points. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanSectionCancellation

noncomputable def sectionSum (phase : Fin 3 → ℂ) (S : Finset (Fin 3)) : ℂ :=
  S.sum phase

theorem no_triangle_section_cancellation
    (phase : Fin 3 → ℂ)
    (hunit : ∀ i, ‖phase i‖ = 1)
    (h01 : sectionSum phase {0, 1} = 0)
    (h02 : sectionSum phase {0, 2} = 0)
    (h12 : sectionSum phase {1, 2} = 0) :
    False := by
  have h01' : phase 0 + phase 1 = 0 := by
    simpa [sectionSum] using h01
  have h02' : phase 0 + phase 2 = 0 := by
    simpa [sectionSum] using h02
  have h12' : phase 1 + phase 2 = 0 := by
    simpa [sectionSum] using h12
  have htwo : 2 * phase 0 = 0 := by
    linear_combination h01' + h02' - h12'
  have hzero : phase 0 = 0 := by
    calc
      phase 0 = (1 / 2 : ℂ) * (2 * phase 0) := by ring
      _ = 0 := by rw [htwo, mul_zero]
  have hnonzero : phase 0 ≠ 0 := by
    intro hz
    have := hunit (0 : Fin 3)
    rw [hz] at this
    norm_num at this
  exact hnonzero hzero

/-! The finite incidence part of the same obstruction.  In a `3 × 3`
configuration with two occupied points in every row and column, each row is
the complement of one missing column, and the missing-column map is a
permutation.  This is the exact normal form to which the character equations
above apply.  The statement is finite and is discharged by kernel-checked
enumeration, rather than by assuming a geometric picture. -/

set_option maxRecDepth 100000 in
theorem regular_three_by_three_incidence
    (A : Fin 3 → Finset (Fin 3))
    (hrow : ∀ i, (A i).card = 2)
    (hcol : ∀ j, (Finset.univ.filter fun i => j ∈ A i).card = 2) :
    ∃ missing : Fin 3 → Fin 3,
      (∀ i, A i = Finset.univ.erase (missing i)) ∧
        Function.Bijective missing := by
  decide +revert

end D5.S1.Dynamics.Symbolic.KhetanSectionCancellation
