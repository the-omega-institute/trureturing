/- GID: D5/S3/Arith/Covering/PrimeFactorPureClass
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/PrimeFactorPureClass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sum-minimal odd covers contain every prime divisor as a pure prime modulus. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

open scoped BigOperators

variable {L : ℕ}

/- A prime divisor of a class modulus must already occur as a pure class in a
sum-minimal distinct cover: otherwise replacing the class by the larger
congruence class modulo that prime lowers the modulus sum. -/
theorem prime_dvd_modulus_is_present
    (F : OddDistinctCoveringSystem L)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (i : Fin L) (p : ℕ) (hp : Nat.Prime p) (hpi : p ∣ F.modulus i) :
    ∃ j : Fin L, F.modulus j = p := by
  classical
  by_contra hnone
  push_neg at hnone
  have hle : p ≤ F.modulus i :=
    Nat.le_of_dvd (Nat.zero_lt_of_lt (F.modulus_one_lt i)) hpi
  have hlt : p < F.modulus i := by
    exact lt_of_le_of_ne hle (fun heq ↦ hnone i heq.symm)
  let newMod : Fin L → ℕ := fun k ↦ if k = i then p else F.modulus k
  have hnewCover : ∀ x : ℕ, ∃ k : Fin L,
      x ≡ F.residue k [MOD newMod k] := by
    intro x
    obtain ⟨k, hk⟩ := F.covers x
    by_cases hki : k = i
    · subst k
      refine ⟨i, ?_⟩
      simpa only [newMod, if_pos rfl] using hk.of_dvd hpi
    · refine ⟨k, ?_⟩
      simpa only [newMod, if_neg hki] using hk
  have hnewOneLt : ∀ k, 1 < newMod k := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa only [newMod, if_pos rfl] using hp.one_lt
    · simpa only [newMod, if_neg hki] using F.modulus_one_lt k
  have hnewOdd : ∀ k, Odd (newMod k) := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa only [newMod, if_pos rfl] using
        (F.modulus_odd i).of_dvd_nat (by simpa only [newMod, if_pos rfl] using hpi)
    · simpa only [newMod, if_neg hki] using F.modulus_odd k
  have hnewInjective : Function.Injective newMod := by
    intro k l hkl
    by_cases hk : k = i
    · subst k
      by_cases hl : l = i
      · exact hl.symm
      · exfalso
        apply hnone l
        have hpEq : p = F.modulus l := by
          simpa only [newMod, if_pos rfl, if_neg hl] using hkl
        exact hpEq.symm
    · by_cases hl : l = i
      · exfalso
        subst l
        apply hnone k
        have hpEq : F.modulus k = p := by
          simpa only [newMod, if_neg hk, if_pos rfl] using hkl
        exact hpEq
      · apply F.modulus_injective
        simpa only [newMod, if_neg hk, if_neg hl] using hkl
  let H : OddDistinctCoveringSystem L :=
    { residue := F.residue
      modulus := newMod
      covers := hnewCover
      modulus_one_lt := hnewOneLt
      modulus_odd := hnewOdd
      modulus_injective := hnewInjective }
  have hnewLe : ∀ k, newMod k ≤ F.modulus k := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa only [newMod, if_pos rfl] using hlt.le
    · simpa only [newMod, if_neg hki] using (le_refl (F.modulus k))
  have hnewStrict : newMod i < F.modulus i := by
    simpa only [newMod, if_pos rfl] using hlt
  have hsumlt : (∑ k, newMod k) < ∑ k, F.modulus k := by
    apply Finset.sum_lt_sum
    · intro k _
      exact hnewLe k
    · exact ⟨i, Finset.mem_univ i, hnewStrict⟩
  exact (Nat.not_lt_of_ge (hsumMin H)) hsumlt

/- Every nonempty sum-minimal odd cover therefore contains a pure prime class. -/
theorem exists_pure_prime_class
    (F : OddDistinctCoveringSystem L)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i) :
    ∃ j : Fin L, Nat.Prime (F.modulus j) := by
  obtain ⟨i, _⟩ := F.covers 0
  obtain ⟨p, hp, hpi⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt (F.modulus_one_lt i))
  obtain ⟨j, hj⟩ := prime_dvd_modulus_is_present F hsumMin i p hp hpi
  exact ⟨j, hj ▸ hp⟩

end Erdos7.OddDistinctCoveringSystem
