/- GID: D5/S3/Arith/Primes/PrimeDoubleCompositeWindow
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/PrimeDoubleCompositeWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.LSeries.PrimesInAP]
   utility: none
   digest: Arbitrarily large prime doubles lie at the center of prescribed composite windows. -/

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.PrimeDoubleCompositeWindow

private theorem residue_sieve (s : Finset ℤ) (hs : ∀ j ∈ s, j ≠ 0) :
    ∃ q a : ℕ, 0 < q ∧ a.Coprime q ∧
      ∀ j ∈ s, ∃ r : ℕ, r.Prime ∧ r ≤ q ∧
        ∀ z : ℕ, z ≡ a [MOD q] → (r : ℤ) ∣ 2 * z + j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, 0, by decide, by decide, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨q, a, hq, ha, hprev⟩ := ih (fun i hi => hs i (by simp [hi]))
    obtain ⟨r, hrbound, hr⟩ := Nat.exists_infinite_primes (max (max q j.natAbs) 2 + 1)
    have hqr : q < r := by omega
    have hjr : j.natAbs < r := by omega
    have h2r : 2 < r := by omega
    letI : Fact r.Prime := ⟨hr⟩
    have htwo : (2 : ZMod r) ≠ 0 := by
      intro h
      have hd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp (by simpa using h)
      have := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega
    have hjzero : (j : ZMod r) ≠ 0 := by
      intro hz
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd j r).mp hz
      have hzero := Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd.mp hd) hjr
      have := hs j (Finset.mem_insert_self _ _)
      exact this (Int.natAbs_eq_zero.mp hzero)
    let b : ℕ := (-(j : ZMod r) / 2).val
    have hbcast : (b : ZMod r) = -(j : ZMod r) / 2 := ZMod.natCast_zmod_val _
    have hb : b.Coprime r := by
      apply (ZMod.isUnit_iff_coprime b r).mp
      rw [hbcast]
      exact isUnit_iff_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr hjzero) htwo)
    have hcop : q.Coprime r := by
      apply (hr.coprime_iff_not_dvd.mpr ?_).symm
      intro hd
      have := Nat.le_of_dvd hq hd
      omega
    let c := Nat.chineseRemainder hcop a b
    have hcq : (c.val).Coprime q := by
      apply (ZMod.isUnit_iff_coprime c.val q).mp
      rw [(ZMod.natCast_eq_natCast_iff c.val a q).mpr c.property.1]
      exact (ZMod.isUnit_iff_coprime a q).mpr ha
    have hcr : (c.val).Coprime r := by
      apply (ZMod.isUnit_iff_coprime c.val r).mp
      rw [(ZMod.natCast_eq_natCast_iff c.val b r).mpr c.property.2]
      exact (ZMod.isUnit_iff_coprime b r).mpr hb
    refine ⟨q * r, c.val, Nat.mul_pos hq hr.pos, hcq.mul_right hcr, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · refine ⟨r, hr, Nat.le_mul_of_pos_left r hq, ?_⟩
      intro z hz
      have hzr : z ≡ b [MOD r] :=
        (hz.of_dvd (dvd_mul_left r q)).trans c.property.2
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (z : ℤ) + i) r).mp
      push_cast
      rw [(ZMod.natCast_eq_natCast_iff z b r).mpr hzr, hbcast]
      field_simp [htwo]
      ring
    · obtain ⟨l, hl, hlq, hldvd⟩ := hprev i hi
      refine ⟨l, hl, hlq.trans (Nat.le_mul_of_pos_right q hr.pos), ?_⟩
      intro z hz
      exact hldvd z ((hz.of_dvd (dvd_mul_right q r)).trans c.property.1)

/-- Every prescribed finite interval around twice a sufficiently large prime consists of composites. -/
theorem exists_prime_double_composite_window (H B : ℕ) :
    ∃ p : ℕ, B < p ∧ H < p ∧ p.Prime ∧
      ∀ t : ℕ, 2 * p - H ≤ t → t ≤ 2 * p + H → ¬t.Prime := by
  classical
  let s : Finset ℤ := (Finset.Icc (-(H : ℤ)) H).erase 0
  obtain ⟨q, a, hq, ha, hs⟩ := residue_sieve s (by
    intro j hj
    exact (Finset.mem_erase.mp hj).1)
  obtain ⟨p, hpbound, hp, hpa⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B (q + H + 2)) (ne_of_gt hq) ha
  have hBp : B < p := by omega
  have hHp : H < p := by omega
  refine ⟨p, hBp, hHp, hp, ?_⟩
  intro t htlo hthi
  by_cases ht : t = 2 * p
  · subst t
    exact Nat.not_prime_of_dvd_of_lt (dvd_mul_right 2 p) (by decide) (by omega)
  · let j : ℤ := (t : ℤ) - 2 * p
    have hjs : j ∈ s := by
      dsimp [s, j]
      simp only [Finset.mem_erase, ne_eq, Finset.mem_Icc]
      constructor
      · omega
      · constructor <;> omega
    obtain ⟨r, hr, hrq, hrdvd⟩ := hs j hjs
    have hd : r ∣ t := by
      apply Int.natCast_dvd_natCast.mp
      convert hrdvd p hpa using 1 <;> dsimp [j] <;> ring
    exact Nat.not_prime_of_dvd_of_lt hd hr.two_le (by omega)

end D5.S3.Arith.Primes.PrimeDoubleCompositeWindow
