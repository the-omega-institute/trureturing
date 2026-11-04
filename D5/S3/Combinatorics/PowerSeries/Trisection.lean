/- GID: D5/S3/Combinatorics/PowerSeries/Trisection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/Trisection
   mirror-E: none(waiver:formal-power-series-trisection)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Expand]
   utility: none
   digest: Exact all-degree residue extraction for three formal power series components. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

/-! Exact coefficient extraction separates all three residue classes at every natural index over any commutative ring. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PowerSeries.Trisection

theorem coeff_shift_expand_three {R : Type*} [CommRing R]
    (p : PowerSeries R) (m : ℕ) (r s : Fin 3) :
    PowerSeries.coeff (3 * m + r.val)
      (PowerSeries.X ^ s.val * PowerSeries.expand 3 (by decide) p) =
      if r = s then PowerSeries.coeff m p else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hrs : r = s
  · subst s
    rw [if_pos (by omega), if_pos rfl,
      show 3 * m + r.val - r.val = 3 * m by omega, PowerSeries.coeff_expand_mul]
  · rw [if_neg hrs]
    split_ifs with hle
    · exact PowerSeries.coeff_expand_of_not_dvd 3 (by decide) p (by
        have hr := r.isLt
        have hs := s.isLt
        have hne : r.val ≠ s.val := fun he => hrs (Fin.ext he)
        omega)
    · rfl

/-- A formal dissection determines each progression at every natural degree. -/
theorem coeff_three_components {R : Type*} [CommRing R]
    (p a b c : PowerSeries R)
    (hp : p = PowerSeries.expand 3 (by decide) a +
      PowerSeries.X * PowerSeries.expand 3 (by decide) b +
      PowerSeries.X ^ 2 * PowerSeries.expand 3 (by decide) c) (m : ℕ) :
    PowerSeries.coeff (3 * m) p = PowerSeries.coeff m a ∧
    PowerSeries.coeff (3 * m + 1) p = PowerSeries.coeff m b ∧
    PowerSeries.coeff (3 * m + 2) p = PowerSeries.coeff m c := by
  have h0 := coeff_shift_expand_three a m
  have h1 := coeff_shift_expand_three b m
  have h2 := coeff_shift_expand_three c m
  rw [hp]
  constructor
  · rw [map_add, map_add]
    simpa using
      congrArg₂ (fun x y : R => x + y)
        (congrArg₂ (fun x y : R => x + y) (h0 0 0) (h1 0 1)) (h2 0 2)
  constructor
  · rw [map_add, map_add]
    simpa using congrArg₂ (fun x y : R => x + y)
      (congrArg₂ (fun x y : R => x + y) (h0 1 0) (h1 1 1)) (h2 1 2)
  · rw [map_add, map_add]
    simpa using congrArg₂ (fun x y : R => x + y)
      (congrArg₂ (fun x y : R => x + y) (h0 2 0) (h1 2 1)) (h2 2 2)

end D5.S3.Combinatorics.PowerSeries.Trisection
