/- GID: D5/S1/Recurrence/Parity/SquareCubeSubstitutionThreeIndexModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/SquareCubeSubstitutionThreeIndexModThree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Lucas congruences and residue descent settle Hanna's modulo-three conjecture. -/

/-
admission_basis: open-problem-resolution (#21674; Proved)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22693.
proof_shape: choose_three: bind-only; consumers: descent
  Direct frozen dependencies: none
proof_shape: claim: not-applicable(definition); consumers: result
  Direct frozen dependencies: D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.a
sha256:30758a2a16cda10f92851fd7f668989d00bad0fefd543fd5a8351f8663c4c094
proof_shape: descent: content; consumers: result
  Direct frozen dependencies: D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.a
sha256:30758a2a16cda10f92851fd7f668989d00bad0fefd543fd5a8351f8663c4c094;
D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.coeff_recurrence
sha256:54842d82098f37bef365ba16b134edddfa4cfb5591cf17b96dc2b8bdbd60a836
proof_shape: result: content; consumers: settling conclusion
  Direct frozen dependencies: D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.a
sha256:30758a2a16cda10f92851fd7f668989d00bad0fefd543fd5a8351f8663c4c094;
D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.coeff_recurrence
sha256:54842d82098f37bef365ba16b134edddfa4cfb5591cf17b96dc2b8bdbd60a836
The claim uses the existing integer recurrence, including its seed a(2)=1.
-/

import Mathlib.Data.Nat.Choose.Lucas
import D5.S1.Recurrence.Parity.SquareCubeSubstitutionOddIndexParity

namespace D5.S1.Recurrence.Parity.SquareCubeSubstitutionThreeIndexModThree

open D5.S1.Recurrence.Parity.SquareCubeSubstitutionOddIndexParity

def claim : Prop :=
  ∀ (n : ℕ), 1 < n → (3 : ℤ) ∣ a (3 * n - 1)

end D5.S1.Recurrence.Parity.SquareCubeSubstitutionThreeIndexModThree

namespace D5.S1.Recurrence.Parity.SquareCubeSubstitutionThreeIndexModThree

open D5.S1.Recurrence.Parity.SquareCubeSubstitutionOddIndexParity

private theorem choose_three (k j : ℕ) (hk : k % 3 ≠ 2)
    (hj : (j + 2 * k) % 3 = 1) : (3 : ℤ) ∣ (k.choose j : ℤ) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (p := 3) (n := k) (k := j)
  have hjk : k % 3 < j % 3 := by omega
  rw [Nat.choose_eq_zero_of_lt hjk, Nat.cast_zero, zero_mul] at h
  exact Int.modEq_zero_iff_dvd.mp h

private theorem descent (m : ℕ) (hm : 5 ≤ m) (hmod : m % 3 = 2) :
    (3 : ℤ) ∣ a m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [coeff_recurrence m (by omega)]
    apply Finset.dvd_sum
    intro k hk
    have hbound := Finset.mem_range.mp hk
    by_cases hlarge : m + 2 < 2 * k
    · rw [Nat.sub_eq_zero_of_le (by omega), Nat.choose_zero_right, Nat.cast_one, mul_one]
      have : m + 2 < 2 * k := hlarge
      omega
    have hj : (m + 2 - 2 * k + 2 * k) % 3 = 1 := by omega
    by_cases hk2 : k % 3 = 2
    · by_cases hk5 : 5 ≤ k
      · exact dvd_mul_of_dvd_left (ih k (by omega) hk5 hk2) _
      · have he : k = 2 := by omega
        subst k
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
        exact dvd_zero _
    · exact dvd_mul_of_dvd_right (choose_three k _ hk2 hj) _

theorem result : D5.S1.Recurrence.Parity.SquareCubeSubstitutionThreeIndexModThree.claim := by
  intro n hn
  exact descent _ (by omega) (by omega)

end D5.S1.Recurrence.Parity.SquareCubeSubstitutionThreeIndexModThree
