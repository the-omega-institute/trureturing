/- GID: D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/AlternatingBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Alternating sections of degree at least five have even non-2-group order. -/

import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false

namespace NikolovSegal

theorem sixty_dvd_card_alternating {k : ℕ} (hk : 5 ≤ k) :
    60 ∣ Nat.card (alternatingGroup (Fin k)) := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h := Nat.factorial_dvd_factorial hk
  have hc := two_mul_nat_card_alternatingGroup (α := Fin k)
  simp only [Nat.card_perm, Nat.card_fin] at hc
  have hd : 2 * 60 ∣ 2 * Nat.card (alternatingGroup (Fin k)) := by
    rw [hc]
    norm_num at h ⊢
    exact h
  exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp hd

theorem two_dvd_card_alternating {k : ℕ} (hk : 5 ≤ k) :
    2 ∣ Nat.card (alternatingGroup (Fin k)) :=
  (by norm_num : 2 ∣ 60).trans (sixty_dvd_card_alternating hk)

theorem alternating_not_twoGroup {k : ℕ} (hk : 5 ≤ k) :
    ¬IsPGroup 2 (alternatingGroup (Fin k)) := by
  intro hp
  obtain ⟨n, hcard⟩ := hp.exists_card_eq
  have h : 3 ∣ Nat.card (alternatingGroup (Fin k)) :=
    (by norm_num : 3 ∣ 60).trans (sixty_dvd_card_alternating hk)
  rw [hcard] at h
  have h := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  norm_num at h

end NikolovSegal
