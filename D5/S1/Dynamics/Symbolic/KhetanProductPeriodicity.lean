/- GID: D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Exact-cover product fibres feed the six-cell residue dichotomy. -/

import Mathlib
import D5.S1.Dynamics.Symbolic.KhetanSixCellResidue

/-! This is the product branch of the six-cell route.  The genuinely
one-dimensional input is left explicit as `three_point_tiling_residue`; the
bridge proved here derives the Boolean adjacent-column hypotheses from the
two-column exact-cover equation and then reuses the existing residue
dichotomy. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanProductPeriodicity

open scoped BigOperators

noncomputable def anchorBit (T : ℤ → ℤ → Prop) (x y : ℤ) : ℕ := by
  classical
  exact if T x y then 1 else 0

noncomputable def oneDWindowCount (S : ℤ → Prop) (b c y : ℤ) : ℕ := by
  classical
  exact Finset.sum ({0, b, c} : Finset ℤ) (fun z => if S (y - z) then 1 else 0)

noncomputable def productWindowCount (T : ℤ → ℤ → Prop) (b c x y : ℤ) : ℕ := by
  classical
  exact Finset.sum ({0, b, c} : Finset ℤ) (fun z =>
    anchorBit T (x - 1) (y - z) + anchorBit T x (y - z))

/-! Exact-cover product fibres force one of the two global periods, provided
the one-dimensional three-point residue theorem is supplied.  The latter is
kept as a hypothesis because it is the classical prime-three tiling input,
not the new six-cell bridge. -/
theorem product_three_exact_cover_periodic
    (T : ℤ → ℤ → Prop) (b c : ℤ)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hbc : b ≠ c)
    (hgcd : Int.gcd b c = 1)
    (three_point_tiling_residue :
      ∀ (S : ℤ → Prop),
        b ≠ 0 → c ≠ 0 → b ≠ c → Int.gcd b c = 1 →
        (∀ y, oneDWindowCount S b c y = 1) →
        ∃ r : ℤ, ∀ y, S y ↔ y % 3 = r % 3)
    (hcover : ∀ x y, productWindowCount T b c x y = 1) :
    (∀ x y, T (x + 2) y ↔ T x y) ∨
      (∀ x y, T x (y + 3) ↔ T x y) := by
  let C : ℤ → ℤ → Prop := fun x y => T (x - 1) y ∨ T x y
  have hdisj : ∀ x y, ¬ (T (x - 1) y ∧ T x y) := by
    intro x y hboth
    have hbound :
        anchorBit T (x - 1) y + anchorBit T x y ≤
          productWindowCount T b c x y := by
      simpa [productWindowCount] using (Finset.single_le_sum
        (s := ({0, b, c} : Finset ℤ))
        (a := (0 : ℤ))
        (f := fun z =>
          anchorBit T (x - 1) (y - z) + anchorBit T x (y - z))
        (fun _ _ => Nat.zero_le _) (by simp))
    have htwo : 2 ≤ productWindowCount T b c x y := by
      have hbits : anchorBit T (x - 1) y = 1 ∧ anchorBit T x y = 1 := by
        simp [anchorBit, hboth.1, hboth.2]
      calc
        2 = anchorBit T (x - 1) y + anchorBit T x y := by
          simp [hbits.1, hbits.2]
        _ ≤ productWindowCount T b c x y := hbound
    rw [hcover x y] at htwo
    omega
  have hsum_eq : ∀ x y,
      oneDWindowCount (C x) b c y = productWindowCount T b c x y := by
    intro x y
    unfold oneDWindowCount productWindowCount
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hl : T (x - 1) (y - z)
    · have hr : ¬ T x (y - z) := by
        intro hr
        exact hdisj x (y - z) ⟨hl, hr⟩
      simp [C, anchorBit, hl, hr]
    · by_cases hr : T x (y - z)
      · simp [C, anchorBit, hl, hr]
      · simp [C, anchorBit, hl, hr]
  have hCcover : ∀ x y, oneDWindowCount (C x) b c y = 1 := by
    intro x y
    rw [hsum_eq x y]
    exact hcover x y
  choose r hres using fun x =>
    three_point_tiling_residue (C x) hb0 hc0 hbc hgcd (hCcover x)
  have hpart : ∀ x y,
      Xor (T (x - 1) y) (T x y) ↔ y % 3 = r x % 3 := by
    intro x y
    rw [← hres x y]
    constructor
    · intro hx
      rcases hx with ⟨hl, _⟩ | ⟨hright, _⟩
      · exact Or.inl hl
      · exact Or.inr hright
    · intro hc'
      rcases hc' with hl | hright
      · exact Or.inl ⟨hl, fun h => hdisj x y ⟨hl, h⟩⟩
      · exact Or.inr ⟨hright, fun h => hdisj x y ⟨h, hright⟩⟩
  exact D5.S1.Dynamics.Symbolic.KhetanSixCellResidue.three_residue_column_dichotomy
    T r hpart hdisj

end D5.S1.Dynamics.Symbolic.KhetanProductPeriodicity
