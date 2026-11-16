/- GID: D5/S3/Combinatorics/Circle/Orbit/TwoBitPhysicalClassification
   generality: I
   mirror-B: none(waiver:consumed-symbolic-support)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift.BelowHalfBoundary]
   utility: none
   digest: Exact physical two-bit joint-order classification from the modular criterion. -/
import D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift.BelowHalfBoundary
import D5.S3.Combinatorics.Circle.Orbit.TwoBitDoublingAction
import D5.S3.Arith.Congruence.PowerPlusOneDivisibility
import D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift.HighPhaseTwoNegativeClassification
import D5.S3.Combinatorics.Circle.TwoNegativeNondecreasingJointLift.ReversedHighPhaseTwoNegativeClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.TwoBitPhysicalClassification

open NarrowDoublingOrbit
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.BelowHalfBoundary
open D5.S3.Combinatorics.Circle.TwoBitDoublingAction
open PowerPlusOneDivisibility
open D5.S3.Combinatorics.Circle.HighPhaseTwoNegativeClassification
open D5.S3.Combinatorics.Circle.ReversedHighPhaseTwoNegativeClassification

private theorem succ_mod_eq_iff (a b : ℕ) (ha : 2 ≤ a) :
    (b + 1) % (2 * a) = a ↔ b % (2 * a) = a - 1 := by
  have hm : 0 < 2 * a := by omega
  have hltA : a < 2 * a := by omega
  have hmod : (b + 1) % (2 * a) = (b % (2 * a) + 1) % (2 * a) := by
    have hone : 1 % (2 * a) = 1 := Nat.mod_eq_of_lt (by omega)
    calc
      (b + 1) % (2 * a) = (b % (2 * a) + 1 % (2 * a)) % (2 * a) :=
        Nat.add_mod b 1 (2 * a)
      _ = (b % (2 * a) + 1) % (2 * a) := by rw [hone]
  constructor
  · intro h
    have hx : b % (2 * a) < 2 * a := Nat.mod_lt b hm
    rw [hmod] at h
    by_cases hsmall : b % (2 * a) + 1 < 2 * a
    · rw [Nat.mod_eq_of_lt hsmall] at h
      omega
    · have heq : b % (2 * a) + 1 = 2 * a := by omega
      rw [heq, Nat.mod_self] at h
      omega
  · intro h
    rw [hmod, h]
    have hone : 1 ≤ a := by omega
    rw [Nat.sub_add_cancel hone, Nat.mod_eq_of_lt hltA]

/-- Full physical iff for the unchanged two-bit orbit, including both endpoints
and all four phase regions.  The same concrete `sigma` and literal `cut` are
retained by every prerequisite certificate consumed below. -/
theorem actualSource_full_cyclic_two_bit_physical_joint_iff (a b h : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) (hh : h < a + b) :
    (∃ sigma : List (Fin (a + b)), ∃ cut : ℕ, cut ≤ a + b ∧
      OriginalOrder (a + b)
        (NarrowDoublingOrbit.residue (2 ^ (a + b) - 1)
          (2 ^ (a + b - 1) + 2 ^ (b - 1)) h) sigma ∧
      OriginalOrder (a + b + 1)
        (2 * (NarrowDoublingOrbit.residue (2 ^ (a + b) - 1)
          (2 ^ (a + b - 1) + 2 ^ (b - 1)) h))
        (earWord (a + b) sigma cut)) ↔
      ((h ≠ 0 ∨ b % (2 * a) = a - 1 ∨ b % (2 * a) = a) ∧
        (h ≠ a ∨ a = b ∨ b = a + 1 ∨ 2 * a < b)) := by
  have hb : 2 ≤ b := ha.trans hab
  by_cases hzero : h = 0
  · subst h
    have hq := phase_zero a b ha hb
    rw [hq]
    have hforward :=
      actualSource_high_phase_two_negative_joint_iff a b ha hab
    have hane : 0 ≠ a := by omega
    have hd_b :=
      dvd_pow_add_one_iff_mod_two_mul 2 a b (by omega) (by omega)
    have hd_b1 :=
      dvd_pow_add_one_iff_mod_two_mul 2 a (b + 1) (by omega) (by omega)
    constructor
    · intro hphys
      have hdiv := hforward.mp hphys
      rcases hdiv with hdiv | hdiv
      · have hm := hd_b.mp hdiv
        exact ⟨Or.inr (Or.inr hm), Or.inl hane⟩
      · have hm := hd_b1.mp hdiv
        have hs := (succ_mod_eq_iff a b ha).mp hm
        exact ⟨Or.inr (Or.inl hs), Or.inl hane⟩
    · intro hrhs
      rcases hrhs.1 with hne | hm | hm
      · exact (hne rfl).elim
      · exact hforward.mpr
          (Or.inr (hd_b1.mpr ((succ_mod_eq_iff a b ha).mpr hm)))
      · exact hforward.mpr (Or.inl (hd_b.mpr hm))
  · by_cases h_at : h = a
    · subst h
      have hqa := phase_at a b ha hb
      rw [hqa]
      by_cases hab_eq : a = b
      · subst b
        have hforward :=
          actualSource_high_phase_two_negative_joint_iff a a ha le_rfl
        have hane : a ≠ 0 := by omega
        constructor
        · intro _
          exact ⟨Or.inl hane, Or.inr (Or.inl rfl)⟩
        · intro _
          exact hforward.mpr (Or.inl (dvd_refl (2 ^ a + 1)))
      · have hba : a < b := by omega
        have hreverse :=
          actualSource_reversed_high_phase_two_negative_joint_iff b a ha hba
        have hreverse' :
            (∃ sigma : List (Fin (a + b)), ∃ cut : ℕ, cut ≤ a + b ∧
              OriginalOrder (a + b)
                (2 ^ (a + b - 1) + 2 ^ (a - 1)) sigma ∧
              OriginalOrder (a + b + 1)
                (2 * (2 ^ (a + b - 1) + 2 ^ (a - 1)))
                (earWord (a + b) sigma cut)) ↔
              (b = a + 1 ∨ 2 * a < b) := by
          rw [Nat.add_comm b a] at hreverse
          exact hreverse
        have hane : a ≠ 0 := by omega
        simpa [hane, hab_eq] using hreverse'
    · rcases lt_or_gt_of_ne h_at with hlt | hgt
      · have hpos : 0 < h := by omega
        have hj : h - 1 ≤ a - 2 := by omega
        have hlow :=
          actualSource_below_half_two_bit_uniform_cut b a hb ha
        rcases hlow with ⟨sigma, cut, hcut, hall⟩
        have hlowj := hall (h - 1) (by omega : h - 1 ≤ a - 2)
        dsimp at hlowj
        have hq := phase_before a b h ha hb hpos (by omega)
        rw [hq]
        constructor
        · intro _
          exact ⟨Or.inl (by omega), Or.inl h_at⟩
        · intro _
          have hlowcertBA :
              ∃ tau : List (Fin (b + a)), ∃ c : ℕ, c ≤ b + a ∧
                OriginalOrder (b + a) (2 ^ (h - 1) * (2 ^ b + 1)) tau ∧
                OriginalOrder (b + a + 1) (2 * (2 ^ (h - 1) * (2 ^ b + 1)))
                  (earWord (b + a) tau c) := by
            exact ⟨sigma.map
                ((finRotate (b + a) : Equiv.Perm (Fin (b + a))) ^
                  (a - 2 - (h - 1))),
              cut, hcut, hlowj.1, hlowj.2⟩
          rw [Nat.add_comm b a] at hlowcertBA
          exact hlowcertBA
      · have hpos : 0 < h := by omega
        have hj : h - a - 1 ≤ b - 2 := by omega
        have hlow :=
          actualSource_below_half_two_bit_uniform_cut a b ha hb
        rcases hlow with ⟨sigma, cut, hcut, hall⟩
        have hlowj := hall (h - a - 1) hj
        dsimp at hlowj
        have hq := phase_after a b h ha hb hgt hh
        rw [hq]
        constructor
        · intro _
          exact ⟨Or.inl (by omega), Or.inl h_at⟩
        · intro _
          refine ⟨sigma.map
              ((finRotate (a + b) : Equiv.Perm (Fin (a + b))) ^ (b - 2 - (h - a - 1))),
            cut, hcut, ?_, ?_⟩
          · simpa using hlowj.1
          · simpa using hlowj.2

end D5.S3.Combinatorics.Circle.TwoBitPhysicalClassification
