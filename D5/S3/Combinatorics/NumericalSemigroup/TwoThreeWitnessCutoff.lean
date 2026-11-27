/- GID: D5/S3/Combinatorics/NumericalSemigroup/TwoThreeWitnessCutoff
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NumericalSemigroup/TwoThreeWitnessCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive and primitive witnesses of the row (2, 3) have best cutoff eight. -/

import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.Combinatorics.NumericalSemigroup.TwoThreeWitnessCutoff

open scoped Int

private def degree (x : ℤ × ℤ) : ℤ := 2 * x.1 + 3 * x.2

private def coordinateDet (x y : ℤ × ℤ) : ℤ := x.1 * y.2 - x.2 * y.1

private def combination (p u : ℤ × ℤ) (a c : ℤ) : ℤ × ℤ :=
  (a * p.1 + c * u.1, a * p.2 + c * u.2)

def viable (p u : ℤ × ℤ) (t : ℤ) : Prop :=
  ∃ a c : ℤ, let x := combination p u a c
    0 ≤ x.1 ∧ 0 ≤ x.2 ∧ degree x = t

private theorem compatible_det {p u x y : ℤ × ℤ}
    (hx : ∃ a c, combination p u a c = x)
    (hy : ∃ a c, combination p u a c = y) :
    |coordinateDet p u| ∣ coordinateDet x y := by
  obtain ⟨a,c,rfl⟩ := hx
  obtain ⟨b,d,rfl⟩ := hy
  apply (abs_dvd _ _).mpr
  refine ⟨a * d - c * b, ?_⟩
  simp only [coordinateDet, combination]
  ring

set_option maxHeartbeats 1000000 in
private theorem obstruction_below_eight (p u : ℤ × ℤ)
    (hp₁ : 0 < p.1) (hp₂ : 0 < p.2) (hu : degree u = 1) :
    ¬ (∀ t : ℤ, 7 ≤ t → viable p u t) := by
  intro all
  let d := |coordinateDet p u|
  unfold degree at hu
  have opposite : (u.1 < 0 ∧ 0 < u.2) ∨ (0 < u.1 ∧ u.2 < 0) := by omega
  have dBound : |u.1| + |u.2| ≤ d := by
    rcases opposite with ⟨hu₁,hu₂⟩ | ⟨hu₁,hu₂⟩
    · have sign : 0 ≤ coordinateDet p u := by
        unfold coordinateDet
        exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hp₂.le hu₁.le).trans
          (mul_nonneg hp₁.le hu₂.le))
      rw [abs_of_neg hu₁, abs_of_pos hu₂, show d = coordinateDet p u from abs_of_nonneg sign]
      unfold coordinateDet
      have h1 := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ p.1 by omega) hu₂.le
      have h2 := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ p.2 by omega) (show 0 ≤ -u.1 by omega)
      linarith
    · have sign : coordinateDet p u ≤ 0 := by
        unfold coordinateDet
        exact sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos hp₁.le hu₂.le).trans
          (mul_nonneg hp₂.le hu₁.le))
      rw [abs_of_pos hu₁, abs_of_neg hu₂, show d = -coordinateDet p u from abs_of_nonpos sign]
      unfold coordinateDet
      have h1 := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ p.1 by omega) (show 0 ≤ -u.2 by omega)
      have h2 := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ p.2 by omega) hu₁.le
      linarith
  have two : 2 ≤ d := by
    rcases opposite with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [abs_of_neg h1, abs_of_pos h2] at dBound
      omega
    · rw [abs_of_pos h1, abs_of_neg h2] at dBound
      omega
  have get (t : ℤ) (ht : 7 ≤ t) : ∃ x : ℤ × ℤ, 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ degree x = t ∧
      ∃ a c, combination p u a c = x := by
    obtain ⟨a,c,h⟩ := all t ht
    exact ⟨combination p u a c, h.1,h.2.1,h.2.2, a,c,rfl⟩
  obtain ⟨⟨x₇,y₇⟩,hx₇,hy₇,eq₇,mem₇⟩ := get 7 (by decide)
  have unique : x₇ = 2 ∧ y₇ = 1 := by simp only [degree] at eq₇; omega
  obtain ⟨rfl,rfl⟩ := unique
  have divDet (t : ℤ) (ht : 7 ≤ t) : ∃ x y : ℤ, 0 ≤ x ∧ 0 ≤ y ∧ 2*x+3*y=t ∧
      d ∣ 2*y-x := by
    obtain ⟨⟨x,y⟩,hx,hy,eq,mem⟩ := get t ht
    exact ⟨x,y,hx,hy,eq,by simpa [d, coordinateDet] using compatible_det mem₇ mem⟩
  have notOne : ¬ d ∣ 1 := by
    intro trivial
    have := Int.le_of_dvd (by decide : (0 : ℤ) < 1) trivial
    omega
  have exactTwo : d = 2 := by
    obtain ⟨x₈,y₈,hx₈,hy₈,eq₈,div₈⟩ := divDet 8 (by decide)
    have forms : (x₈=4 ∧ y₈=0) ∨ (x₈=1 ∧ y₈=2) := by omega
    rcases forms with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have neg4 : d ∣ (-4 : ℤ) := by exact div₈
      obtain ⟨x₉,y₉,hx₉,hy₉,eq₉,div₉⟩ := divDet 9 (by decide)
      have forms : (x₉=3 ∧ y₉=1) ∨ (x₉=0 ∧ y₉=3) := by omega
      rcases forms with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact False.elim (notOne (dvd_neg.mp (show d ∣ (-1 : ℤ) from div₉)))
      · have div2 : d ∣ (2 : ℤ) := (dvd_add neg4 div₉)
        have := Int.le_of_dvd (by decide : (0 : ℤ) < 2) div2
        omega
    · have div3 : d ∣ (3 : ℤ) := div₈
      obtain ⟨x₁₀,y₁₀,hx₁₀,hy₁₀,eq₁₀,div₁₀⟩ := divDet 10 (by decide)
      have forms : (x₁₀=5 ∧ y₁₀=0) ∨ (x₁₀=2 ∧ y₁₀=2) := by omega
      rcases forms with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact False.elim (notOne (dvd_add (dvd_add div3 div3) div₁₀))
      · exact False.elim (notOne (dvd_sub div3 div₁₀))
  have uShape : u.1 = -1 ∧ u.2 = 1 := by
    rcases opposite with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [abs_of_neg h1, abs_of_pos h2, exactTwo] at dBound
      omega
    · rw [abs_of_pos h1, abs_of_neg h2, exactTwo] at dBound
      omega
  have uInSpan : ∃ a c, combination p u a c = u := ⟨0,1,by simp [combination]⟩
  have incompatible := compatible_det mem₇ uInSpan
  change d ∣ 2 * u.2 - 1 * u.1 at incompatible
  rw [exactTwo, uShape.1, uShape.2] at incompatible
  exact (by decide : ¬ (2 : ℤ) ∣ 2 * 1 - 1 * (-1)) incompatible

private theorem realizes_from_eight : ∀ t : ℤ, 8 ≤ t → viable (1,1) (-1,1) t := by
  intro t h
  let q := (t-8) / 4
  let r := (t-8) % 4
  have hq : 0 ≤ q := Int.ediv_nonneg (by omega) (by decide)
  have hr : 0 ≤ r := Int.emod_nonneg _ (by decide)
  have hr₄ : r < 4 := Int.emod_lt_of_pos _ (by decide)
  have decompose : r + 4*q = t-8 := Int.emod_add_mul_ediv _ _
  refine ⟨2+q, r-(2+q), ?_⟩
  simp only [combination, degree]
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Among spans of a strictly positive vector and a degree-one integer vector,
eight is the first possible cutoff for nonnegative solutions of the row (2, 3). -/
theorem best_two_witness_cutoff :
    IsLeast {C : ℤ | ∃ p u : ℤ × ℤ, 0 < p.1 ∧ 0 < p.2 ∧ degree u = 1 ∧
      ∀ t : ℤ, C ≤ t → viable p u t} 8 := by
  constructor
  · exact ⟨(1,1), (-1,1), by decide, by decide, by decide, realizes_from_eight⟩
  · rintro C ⟨p,u,hp₁,hp₂,hu,tail⟩
    by_contra! early
    exact obstruction_below_eight p u hp₁ hp₂ hu
      (fun t ht => tail t (by omega))

end D5.S3.Combinatorics.NumericalSemigroup.TwoThreeWitnessCutoff
