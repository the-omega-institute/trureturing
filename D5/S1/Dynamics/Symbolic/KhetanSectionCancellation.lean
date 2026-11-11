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
set_option maxHeartbeats 0 in
-- The finite incidence table is exhaustively reduced over all `Fin 3` rows.
theorem regular_three_by_three_incidence
    (A : Fin 3 → Finset (Fin 3))
    (hrow : ∀ i, (A i).card = 2)
    (hcol : ∀ j, (Finset.univ.filter fun i => j ∈ A i).card = 2) :
    ∃ missing : Fin 3 → Fin 3,
      (∀ i, A i = Finset.univ.erase (missing i)) ∧
        Function.Bijective missing := by
  decide +revert

/-! A six-point incidence table with no singleton occupied section has only
the three expected shapes: a `2 × 3` product, a `3 × 2` product, or the
regular `3 × 3` two-point pattern.  This is the finite geometric reduction
used before the character contradiction. -/

def columnCount (A : Fin 3 → Finset (Fin 3)) (j : Fin 3) : Nat :=
  (Finset.univ.filter fun i => j ∈ A i).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The six-point dichotomy is a kernel-checked finite enumeration of all tables.
theorem six_point_incidence_dichotomy
    (A : Fin 3 → Finset (Fin 3))
    (htotal : Finset.univ.sum (fun i : Fin 3 => (A i).card) = 6)
    (hrow : ∀ i, (A i).Nonempty → 2 ≤ (A i).card)
    (hcol : ∀ j, (Finset.univ.filter fun i => j ∈ A i).Nonempty →
      2 ≤ columnCount A j) :
    (∃ rows : Finset (Fin 3), rows.card = 2 ∧
        (∀ i, i ∈ rows → A i = Finset.univ)) ∨
      (∃ cols : Finset (Fin 3), cols.card = 2 ∧
        (∀ i, A i = cols)) ∨
      ((∀ i, (A i).card = 2) ∧ (∀ j, columnCount A j = 2)) := by
  decide +revert

theorem no_regular_three_by_three_section_cancellation
    (A : Fin 3 → Finset (Fin 3))
    (hrow : ∀ i, (A i).card = 2)
    (hcol : ∀ j, columnCount A j = 2)
    (phase : Fin 3 → ℂ)
    (hunit : ∀ j, ‖phase j‖ = 1)
    (hcancel : ∀ i, sectionSum phase (A i) = 0) :
    False := by
  obtain ⟨missing, hshape, hbij⟩ := regular_three_by_three_incidence A hrow hcol
  let total : ℂ := (Finset.univ : Finset (Fin 3)).sum phase
  have hphase_missing : ∀ i, phase (missing i) = total := by
    intro i
    have hc : sectionSum phase (Finset.univ.erase (missing i)) = 0 := by
      rw [← hshape i]
      exact hcancel i
    have hs := Finset.sum_erase_add (Finset.univ : Finset (Fin 3)) phase
      (Finset.mem_univ (missing i))
    dsimp [sectionSum, total] at hc ⊢
    linear_combination hs - hc
  have hphase_all : ∀ j, phase j = total := by
    intro j
    obtain ⟨i, rfl⟩ := hbij.2 j
    exact hphase_missing i
  have htotal_eq : total = 3 * total := by
    dsimp [total]
    calc
      (Finset.univ : Finset (Fin 3)).sum phase =
          (Finset.univ : Finset (Fin 3)).sum (fun _ => total) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hphase_all j
      _ = 3 * total := by simp
  have htotal_zero : total = 0 := by
    have htwo : (2 : ℂ) * total = 0 := by
      calc
        (2 : ℂ) * total = 3 * total - total := by ring
        _ = 0 := by rw [← htotal_eq]; ring
    rcases mul_eq_zero.mp htwo with htwo | hzero
    · norm_num at htwo
    · exact hzero
  have hz : phase 0 = 0 := by
    rw [hphase_all 0, htotal_zero]
  have := hunit (0 : Fin 3)
  rw [hz] at this
  norm_num at this

end D5.S1.Dynamics.Symbolic.KhetanSectionCancellation
