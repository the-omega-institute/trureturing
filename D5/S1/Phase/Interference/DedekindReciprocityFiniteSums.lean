/- GID: D5/S1/Phase/Interference/DedekindReciprocityFiniteSums
   generality: I
   mirror-B: D5/B/S1/Phase/Interference/DedekindReciprocityFiniteSums
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sawtooth values and coprime residue sums reduce to exact finite rational formulas. -/

/- Library-search audit trail (2026-08-14):
   * The frozen phase-1 `dedekindSum` and rational `sawtooth` are reused.
   * `Int.fract_div_natCast_eq_div_natCast_mod` supplies the fractional-part reduction.
   * No existing general nonzero-residue permutation sum was found in the pinned library.
-/

import D5.S1.Phase.Interference.DedekindBhkCertificates
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace D5.S1.Phase.Interference.DedekindReciprocityFiniteSums

open D5.S1.Phase.Interference.DedekindBhkCertificates

/-- Away from integral inputs, the phase-1 sawtooth is the reduced rational
remainder minus one half. -/
theorem sawtooth_div_eq_mod {k c : Nat} (hc : 0 < c) (hck : ¬c ∣ k) :
    sawtooth ((k : Rat) / (c : Rat)) =
      ((k % c : Nat) : Rat) / (c : Rat) - 1 / 2 := by
  rw [sawtooth, Int.fract_div_natCast_eq_div_natCast_mod]
  have hcRat : (c : Rat) ≠ 0 := by exact_mod_cast hc.ne'
  split_ifs with hzero
  · have hmodRat : ((k % c : Nat) : Rat) = 0 := by
      simpa [hcRat] using hzero
    have hmod : k % c = 0 := by exact_mod_cast hmodRat
    exact (hck (Nat.dvd_iff_mod_eq_zero.mpr hmod)).elim
  · rfl

/-- The phase-1 Dedekind sum is a finite rational sum of reduced residues. -/
theorem dedekindSum_eq_mod_sum {d c : Nat} (hc : 0 < c) (hdc : d.Coprime c) :
    dedekindSum d c =
      ∑ k ∈ Finset.Ico 1 c,
        (((k % c : Nat) : Rat) / (c : Rat) - 1 / 2) *
          ((((k * d) % c : Nat) : Rat) / (c : Rat) - 1 / 2) := by
  unfold dedekindSum
  have hinterval : Finset.Icc 1 (c - 1) = Finset.Ico 1 c := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hinterval]
  apply Finset.sum_congr rfl
  intro k hk
  have hkBounds := Finset.mem_Ico.mp hk
  have hck : ¬c ∣ k := by
    intro hdiv
    exact (not_le_of_gt hkBounds.2) (Nat.le_of_dvd (by omega) hdiv)
  have hckd : ¬c ∣ k * d := by
    intro hdiv
    exact hck ((hdc.symm.dvd_mul_right).mp hdiv)
  rw [sawtooth_div_eq_mod hc hck, sawtooth_div_eq_mod hc hckd]

/-- The sum of the rational integers in `1 <= k < c`. -/
theorem sum_Ico_cast (c : Nat) :
    ∑ k ∈ Finset.Ico 1 c, (k : Rat) =
      (c : Rat) * ((c : Rat) - 1) / 2 := by
  induction c with
  | zero => simp
  | succ c ih =>
      by_cases hc : c = 0
      · subst c
        simp
      · rw [Finset.sum_Ico_succ_top (by omega), ih]
        push_cast
        ring

/-- The sum of the rational squares in `1 <= k < c`. -/
theorem sum_Ico_cast_sq (c : Nat) :
    ∑ k ∈ Finset.Ico 1 c, (k : Rat) ^ 2 =
      ((c : Rat) - 1) * (c : Rat) * (2 * (c : Rat) - 1) / 6 := by
  induction c with
  | zero => simp
  | succ c ih =>
      by_cases hc : c = 0
      · subst c
        simp
      · rw [Finset.sum_Ico_succ_top (by omega), ih]
        push_cast
        ring

/-- Multiplication by a unit modulo `c` permutes the nonzero residues. -/
theorem sum_mul_mod_permutation {d c : Nat} (hc : 0 < c) (hdc : d.Coprime c)
    (f : Nat → Rat) :
    ∑ k ∈ Finset.Ico 1 c, f ((k * d) % c) =
      ∑ k ∈ Finset.Ico 1 c, f k := by
  classical
  let s := Finset.Ico 1 c
  let p : Nat → Nat := fun k => (k * d) % c
  have hp_mem : ∀ k ∈ s, p k ∈ s := by
    intro k hk
    have hkBounds := Finset.mem_Ico.mp hk
    have hpLt : p k < c := Nat.mod_lt _ hc
    have hpNe : p k ≠ 0 := by
      intro hpZero
      have hdiv : c ∣ k * d := Nat.dvd_iff_mod_eq_zero.mpr hpZero
      have : c ∣ k := (hdc.symm.dvd_mul_right).mp hdiv
      exact (not_le_of_gt hkBounds.2) (Nat.le_of_dvd (by omega) this)
    exact Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hpNe, hpLt⟩
  have hp_inj : Set.InjOn p s := by
    intro k hk l hl hkl
    have hmod : k * d ≡ l * d [MOD c] := hkl
    have hcancel : k ≡ l [MOD c] :=
      hmod.cancel_right_of_coprime (by simpa [Nat.gcd_comm] using hdc.gcd_eq_one)
    exact hcancel.eq_of_lt_of_lt (Finset.mem_Ico.mp hk).2 (Finset.mem_Ico.mp hl).2
  have himage : s.image p = s := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      exact hp_mem k hk
    · rw [Finset.card_image_iff.mpr hp_inj]
  apply Finset.sum_bij (fun k _ => p k)
  · exact hp_mem
  · intro k hk l hl hkl
    exact hp_inj hk hl hkl
  · intro r hr
    have : r ∈ s.image p := himage.symm ▸ hr
    rcases Finset.mem_image.mp this with ⟨k, hk, hkr⟩
    exact ⟨k, hk, hkr⟩
  · intro k hk
    rfl

/-- The reduced residues have the same linear sum as `1, ..., c - 1`. -/
theorem sum_mul_mod {d c : Nat} (hc : 0 < c) (hdc : d.Coprime c) :
    ∑ k ∈ Finset.Ico 1 c, (((k * d) % c : Nat) : Rat) =
      (c : Rat) * ((c : Rat) - 1) / 2 := by
  rw [sum_mul_mod_permutation hc hdc (fun k => (k : Rat)), sum_Ico_cast]

/-- The reduced residues also preserve the elementary square sum. -/
theorem sum_mul_mod_sq {d c : Nat} (hc : 0 < c) (hdc : d.Coprime c) :
    ∑ k ∈ Finset.Ico 1 c, (((k * d) % c : Nat) : Rat) ^ 2 =
      ((c : Rat) - 1) * (c : Rat) * (2 * (c : Rat) - 1) / 6 := by
  rw [sum_mul_mod_permutation hc hdc (fun k => (k : Rat) ^ 2), sum_Ico_cast_sq]

end D5.S1.Phase.Interference.DedekindReciprocityFiniteSums
