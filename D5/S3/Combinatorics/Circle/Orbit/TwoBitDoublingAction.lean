/- GID: D5/S3/Combinatorics/Circle/Orbit/TwoBitDoublingAction
   generality: I
   mirror-B: none(waiver:consumed-symbolic-support)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Circle.Orbit.NarrowDoublingOrbit]
   utility: none
   digest: Physical doubling phases and the genuine period of two-bit seeds. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.Orbit.NarrowDoublingOrbit

/-! Candidate only: not elaborated or kernel checked.
Arithmetic for the prescribed two-bit seed, including nonunits.
Canonical residue/actual-period semantics and private return conversion are
reused from NarrowDoublingOrbit at c434a5ff8c88a7d8f71d75fe0ea077e5d904b36e.
No physical realization theorem is imported or asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.TwoBitDoublingAction

open NarrowDoublingOrbit
open D5.S3.Combinatorics.Circle.NarrowDoublingOrbit (periodic_iff_modEq residue_return residue_zero)

private theorem mersenne_congr (r : ℕ) :
    Nat.ModEq (2 ^ r - 1) (2 ^ r) 1 := by
  have hp : 0 < (2 : ℕ) ^ r := by positivity
  have he : 2 ^ r = (2 ^ r - 1) + 1 := by omega
  change 2 ^ r % (2 ^ r - 1) = 1 % (2 ^ r - 1)
  rw [he, Nat.add_mod]
  simp

private theorem wrap (r t : ℕ) (ht : r ≤ t) :
    Nat.ModEq (2 ^ r - 1) (2 ^ t) (2 ^ (t - r)) := by
  have he : (2 : ℕ) ^ t = 2 ^ r * 2 ^ (t - r) := by
    rw [← pow_add]
    congr 1
    omega
  rw [he]
  simpa using (mersenne_congr r).mul_right (2 ^ (t - r))

private theorem sum_bound (r u v : ℕ) (hr : 4 ≤ r)
    (hu : u ≤ r - 1) (hv : v ≤ r - 2) :
    2 ^ u + 2 ^ v < 2 ^ r - 1 := by
  have h₁ := Nat.pow_le_pow_right (by omega : 0 < 2) hu
  have h₂ := Nat.pow_le_pow_right (by omega : 0 < 2) hv
  have h₃ : (2 : ℕ) ^ 1 ≤ 2 ^ (r - 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have e₁ : (2 : ℕ) ^ (r - 1) = 2 * 2 ^ (r - 2) := by
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]; omega
  have e₂ : (2 : ℕ) ^ r = 4 * 2 ^ (r - 2) := by
    rw [show r = (r - 2) + 2 by omega, pow_add]; norm_num <;> ring
  norm_num at h₃
  omega

private theorem seed_bound (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    2 ^ (a + b - 1) + 2 ^ (b - 1) < 2 ^ (a + b) - 1 :=
  sum_bound (a + b) (a + b - 1) (b - 1) (by omega) (by omega) (by omega)

private theorem first_phase (a b h : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hh : 0 < h) (hhA : h ≤ a) :
    residue (2 ^ (a + b) - 1) (2 ^ (a + b - 1) + 2 ^ (b - 1)) h =
      2 ^ (h - 1) + 2 ^ (h + b - 1) := by
  have hc : Nat.ModEq (2 ^ (a + b) - 1)
      (2 ^ h * (2 ^ (a + b - 1) + 2 ^ (b - 1)))
      (2 ^ (h - 1) + 2 ^ (h + b - 1)) := by
    rw [Nat.mul_add, ← pow_add, ← pow_add]
    have hw := wrap (a + b) (h + (a + b - 1)) (by omega)
    rw [show h + (a + b - 1) - (a + b) = h - 1 by omega] at hw
    simpa only [show h + (b - 1) = h + b - 1 by omega] using
      hw.add (Nat.ModEq.rfl : Nat.ModEq (2 ^ (a + b) - 1)
        (2 ^ (h + b - 1)) (2 ^ (h + b - 1)))
  change _ % _ = _ at hc
  unfold residue
  rw [hc, Nat.mod_eq_of_lt]
  simpa only [Nat.add_comm] using
    sum_bound (a + b) (h + b - 1) (h - 1) (by omega) (by omega) (by omega)

/-- The phase at zero is the prescribed seed in the original residue domain. -/
theorem phase_zero (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    residue (2 ^ (a + b) - 1) (2 ^ (a + b - 1) + 2 ^ (b - 1)) 0 =
      2 ^ (a + b - 1) + 2 ^ (b - 1) :=
  residue_zero (seed_bound a b ha hb)

/-- The first low block; the offset used by BelowHalfBoundary is h-1. -/
theorem phase_before (a b h : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hh : 0 < h) (hhA : h < a) :
    residue (2 ^ (a + b) - 1) (2 ^ (a + b - 1) + 2 ^ (b - 1)) h =
      2 ^ (h - 1) * (2 ^ b + 1) := by
  rw [first_phase a b h ha hb hh (by omega), Nat.mul_add, Nat.mul_one, ← pow_add]
  rw [show h - 1 + b = h + b - 1 by omega, Nat.add_comm]

/-- The other high phase, without an ordering hypothesis on a,b. -/
theorem phase_at (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    residue (2 ^ (a + b) - 1) (2 ^ (a + b - 1) + 2 ^ (b - 1)) a =
      2 ^ (a + b - 1) + 2 ^ (a - 1) := by
  rw [first_phase a b a ha hb (by omega) le_rfl, Nat.add_comm]

/-- The second low block; the offset is h-a-1 with natural subtraction. -/
theorem phase_after (a b h : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hAh : a < h) (hhr : h < a + b) :
    residue (2 ^ (a + b) - 1) (2 ^ (a + b - 1) + 2 ^ (b - 1)) h =
      2 ^ (h - a - 1) * (2 ^ a + 1) := by
  have hc : Nat.ModEq (2 ^ (a + b) - 1)
      (2 ^ h * (2 ^ (a + b - 1) + 2 ^ (b - 1)))
      (2 ^ (h - 1) + 2 ^ (h - a - 1)) := by
    rw [Nat.mul_add, ← pow_add, ← pow_add]
    have h₁ := wrap (a + b) (h + (a + b - 1)) (by omega)
    have h₂ := wrap (a + b) (h + (b - 1)) (by omega)
    simpa only [show h + (a + b - 1) - (a + b) = h - 1 by omega,
      show h + (b - 1) - (a + b) = h - a - 1 by omega] using h₁.add h₂
  change _ % _ = _ at hc
  unfold residue
  rw [hc, Nat.mod_eq_of_lt
    (sum_bound (a + b) (h - 1) (h - a - 1) (by omega) (by omega) (by omega))]
  rw [Nat.mul_add, Nat.mul_one, ← pow_add,
    show h - a - 1 + a = h - 1 by omega]

private theorem sum_low (r u v : ℕ) (hr : 4 ≤ r)
    (hu : u < r - 2) (hv : v ≤ r - 2) :
    2 ^ u + 2 ^ v < 2 ^ (r - 1) := by
  have h₁ := Nat.pow_lt_pow_right (by omega : 1 < 2) hu
  have h₂ := Nat.pow_le_pow_right (by omega : 0 < 2) hv
  rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
  omega

private theorem low_phase (a b h : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hh : 0 < h) (hhr : h < a + b) (hne : h ≠ a) :
    residue (2 ^ (a + b) - 1) (2 ^ (a + b - 1) + 2 ^ (b - 1)) h <
      2 ^ (a + b - 1) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [first_phase a b h ha hb hh (by omega)]
    exact sum_low (a + b) (h - 1) (h + b - 1) (by omega) (by omega) (by omega)
  · rw [phase_after a b h ha hb hgt hhr, Nat.mul_add, Nat.mul_one, ← pow_add,
      show h - a - 1 + a = h - 1 by omega, Nat.add_comm]
    exact sum_low (a + b) (h - a - 1) (h - 1) (by omega) (by omega) (by omega)

/-- The actual least doubling period, including a=b and nonunit seeds.
The return at a+b supplies an upper bound; all earlier positive returns are
excluded by the low phases except a, which returns precisely when a=b. -/
theorem actual_period (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    period (2 ^ (a + b) - 1) (2 ^ (a + b - 1) + 2 ^ (b - 1)) =
      if a = b then a else a + b := by
  let M := 2 ^ (a + b) - 1
  let Q := 2 ^ (a + b - 1) + 2 ^ (b - 1)
  have hQ : Q < M := seed_bound a b ha hb
  have hr : Function.IsPeriodicPt (fun z : ZMod M => 2 * z) (a + b) (Q : ZMod M) :=
    (periodic_iff_modEq M Q (a + b)).mpr
      (by simpa using (mersenne_congr (a + b)).mul_right Q)
  have hp : 0 < period M Q := hr.minimalPeriod_pos (by omega)
  have hpr : period M Q ≤ a + b := hr.minimalPeriod_le (by omega)
  have hret : residue M Q (period M Q) = Q := residue_return hQ
  have early (h : ℕ) (hh : 0 < h) (hhr : h < a + b)
      (he : residue M Q h = Q) : h = a ∧ a = b := by
    have hha : h = a := by
      by_contra hne
      have hlo := low_phase a b h ha hb hh hhr hne
      change residue M Q h < 2 ^ (a + b - 1) at hlo
      rw [he] at hlo
      dsimp [Q] at hlo
      have hp : 0 < (2 : ℕ) ^ (b - 1) := Nat.pow_pos (by omega)
      omega
    subst h
    have he' : 2 ^ (a + b - 1) + 2 ^ (a - 1) =
        2 ^ (a + b - 1) + 2 ^ (b - 1) := by
      simpa only [M, Q, phase_at a b ha hb] using he
    have hexp := Nat.pow_right_injective (by omega : 2 ≤ (2 : ℕ))
      (Nat.add_left_cancel he')
    exact ⟨rfl, by omega⟩
  by_cases hab : a = b
  · rw [if_pos hab]
    have hQa : residue M Q a = Q := by
      simpa only [M, Q, hab] using phase_at a b ha hb
    have hra : Function.IsPeriodicPt (fun z : ZMod M => 2 * z) a (Q : ZMod M) := by
      apply (periodic_iff_modEq M Q a).mpr
      change residue M Q a = Q % M
      rw [hQa, Nat.mod_eq_of_lt hQ]
    have hpa : period M Q ≤ a := hra.minimalPeriod_le (by omega)
    exact (early (period M Q) hp (by omega) hret).1
  · rw [if_neg hab]
    change period M Q = a + b
    by_contra hne
    exact hab (early (period M Q) hp (by omega) hret).2

end D5.S3.Combinatorics.Circle.TwoBitDoublingAction
