/- GID: D5/S1/Words/Mechanical/MechanicalBalance
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalBalance
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Lower mechanical words telescope and every pair of equal windows is balanced by one. -/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace D5.S1.Words.Mechanical

/-- The `n`th lower mechanical letter with slope `alpha` and intercept `rho`. -/
noncomputable def lowerMechanicalLetter (alpha rho : Real) (n : Nat) : Int :=
  ⌊rho + ((n + 1 : Nat) : Real) * alpha⌋ - ⌊rho + (n : Real) * alpha⌋

/-- The Boolean readout of a lower mechanical letter. -/
noncomputable def lowerMechanicalWord (alpha rho : Real) (n : Nat) : Bool :=
  decide (lowerMechanicalLetter alpha rho n = 1)

/-- The number of true letters in the half-open lower-mechanical window `[i, i + n)`. -/
noncomputable def lowerMechanicalWindowTrueCount
    (alpha rho : Real) (i n : Nat) : Nat :=
  ((Finset.range n).filter fun k => lowerMechanicalWord alpha rho (i + k) = true).card

@[simp] theorem lowerMechanicalWord_eq_true_iff (alpha rho : Real) (n : Nat) :
    lowerMechanicalWord alpha rho n = true ↔ lowerMechanicalLetter alpha rho n = 1 := by
  simp [lowerMechanicalWord]

/-- At a slope in `[0, 1)`, every lower mechanical letter is zero or one. -/
theorem lowerMechanicalLetter_eq_zero_or_one {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (n : Nat) :
    lowerMechanicalLetter alpha rho n = 0 ∨ lowerMechanicalLetter alpha rho n = 1 := by
  have hfloor : ⌊alpha⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨halpha0, halpha1⟩
  let x : Real := rho + (n : Real) * alpha
  have hlower := Int.le_floor_add x alpha
  have hupper := Int.le_floor_add_floor x alpha
  rw [hfloor, add_zero] at hlower hupper
  have hletter : lowerMechanicalLetter alpha rho n = ⌊x + alpha⌋ - ⌊x⌋ := by
    apply congrArg₂ (· - ·)
    · apply congrArg Int.floor
      dsimp [x]
      push_cast
      ring
    · rfl
  rw [hletter]
  omega

private theorem lowerMechanicalWord_indicator_eq_letter {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (n : Nat) :
    (if lowerMechanicalWord alpha rho n = true then (1 : Int) else 0) =
      lowerMechanicalLetter alpha rho n := by
  rcases lowerMechanicalLetter_eq_zero_or_one halpha0 halpha1 n with hzero | hone
  · rw [hzero, if_neg]
    exact fun hword => by
      rw [lowerMechanicalWord_eq_true_iff, hzero] at hword
      omega
  · rw [if_pos (lowerMechanicalWord_eq_true_iff alpha rho n |>.mpr hone), hone]

/-- A lower-mechanical window count telescopes to its two endpoint floors. -/
theorem lowerMechanicalWindowTrueCount_eq_floor {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (i n : Nat) :
    (lowerMechanicalWindowTrueCount alpha rho i n : Int) =
      ⌊rho + ((i + n : Nat) : Real) * alpha⌋ - ⌊rho + (i : Real) * alpha⌋ := by
  classical
  rw [lowerMechanicalWindowTrueCount, Finset.natCast_card_filter]
  simp_rw [lowerMechanicalWord_indicator_eq_letter halpha0 halpha1]
  let f : Nat → Int := fun k => ⌊rho + ((i + k : Nat) : Real) * alpha⌋
  calc
    ∑ k ∈ Finset.range n, lowerMechanicalLetter alpha rho (i + k) =
        ∑ k ∈ Finset.range n, (f (k + 1) - f k) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [lowerMechanicalLetter, f]
      congr 2
    _ = f n - f 0 := Finset.sum_range_sub f n
    _ = ⌊rho + ((i + n : Nat) : Real) * alpha⌋ - ⌊rho + (i : Real) * alpha⌋ := by
      simp [f]

/-- Any two equal-length windows of a lower mechanical word differ in true count by at most one. -/
theorem lowerMechanicalWord_balanced_one {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (i j n : Nat) :
    |(lowerMechanicalWindowTrueCount alpha rho i n : Int) -
      (lowerMechanicalWindowTrueCount alpha rho j n : Int)| ≤ 1 := by
  rw [lowerMechanicalWindowTrueCount_eq_floor halpha0 halpha1,
    lowerMechanicalWindowTrueCount_eq_floor halpha0 halpha1]
  let xi : Real := rho + (i : Real) * alpha
  let xj : Real := rho + (j : Real) * alpha
  let t : Real := (n : Real) * alpha
  have hi : rho + ((i + n : Nat) : Real) * alpha = xi + t := by
    dsimp [xi, t]
    push_cast
    ring
  have hj : rho + ((j + n : Nat) : Real) * alpha = xj + t := by
    dsimp [xj, t]
    push_cast
    ring
  have hi_lower := Int.le_floor_add xi t
  have hi_upper := Int.le_floor_add_floor xi t
  have hj_lower := Int.le_floor_add xj t
  have hj_upper := Int.le_floor_add_floor xj t
  rw [hi, hj]
  change |(⌊xi + t⌋ - ⌊xi⌋) - (⌊xj + t⌋ - ⌊xj⌋)| ≤ 1
  rw [abs_le]
  constructor <;> omega

private theorem rational_window_count_zero_example :
    lowerMechanicalWindowTrueCount (2 / 5 : Real) (1 / 7) 0 7 = 2 := by
  have hcount := lowerMechanicalWindowTrueCount_eq_floor
    (alpha := (2 / 5 : Real)) (rho := (1 / 7 : Real)) (by norm_num) (by norm_num) 0 7
  norm_num at hcount
  exact_mod_cast hcount

private theorem rational_window_count_two_example :
    lowerMechanicalWindowTrueCount (2 / 5 : Real) (1 / 7) 2 7 = 3 := by
  have hcount := lowerMechanicalWindowTrueCount_eq_floor
    (alpha := (2 / 5 : Real)) (rho := (1 / 7 : Real)) (by norm_num) (by norm_num) 2 7
  norm_num at hcount
  exact_mod_cast hcount

#print axioms lowerMechanicalLetter_eq_zero_or_one
#print axioms lowerMechanicalWindowTrueCount_eq_floor
#print axioms lowerMechanicalWord_balanced_one

end D5.S1.Words.Mechanical
