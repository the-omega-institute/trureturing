/- GID: D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Basic]
   utility: none
   digest: The least self-divisor exponent is the least prime factor of n minus one. -/

import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.FiroozbakhtLeastSelfDivisorPowerMinusOne

/-- The literal OEIS A092028 definition. By convention, `sInf ∅ = 0`; the
main theorem proves that the defining set is nonempty whenever `2 < n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ m ∣ n ^ m - 1}

private theorem minFac_sub_one_le_of_dvd_pow_sub_one
    {n m : ℕ} (hn : 2 < n) (hm : 1 < m) (hdiv : m ∣ n ^ m - 1) :
    Nat.minFac (n - 1) ≤ m := by
  let q := Nat.minFac m
  have hqprime : q.Prime := Nat.minFac_prime (by omega)
  let _ : Fact q.Prime := ⟨hqprime⟩
  have hqdiv : q ∣ n ^ m - 1 := (Nat.minFac_dvd m).trans hdiv
  have hpowmod : Nat.ModEq q (n ^ m) 1 :=
    ((Nat.modEq_iff_dvd' (one_le_pow₀ (by omega : 1 ≤ n))).2 hqdiv).symm
  have hpow : (n : ZMod q) ^ m = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff (n ^ m) 1 q).2 hpowmod
  have hnzero : (n : ZMod q) ≠ 0 := by
    intro hnzero
    simp [hnzero, zero_pow (by omega : m ≠ 0)] at hpow
  have horder_m : orderOf (n : ZMod q) ∣ m :=
    orderOf_dvd_of_pow_eq_one hpow
  have horder_q : orderOf (n : ZMod q) ∣ q - 1 :=
    ZMod.orderOf_dvd_card_sub_one hnzero
  have hcoprime : m.Coprime (q - 1) :=
    Nat.coprime_of_lt_minFac
      (by have := hqprime.two_le; omega)
      (by have := hqprime.two_le; dsimp [q] at *; omega)
  have horder_gcd : orderOf (n : ZMod q) ∣ Nat.gcd m (q - 1) :=
    Nat.dvd_gcd horder_m horder_q
  rw [hcoprime.gcd_eq_one] at horder_gcd
  have hn_one : (n : ZMod q) = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp horder_gcd)
  have hqpred : q ∣ n - 1 :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ n)).mp
      ((ZMod.natCast_eq_natCast_iff n 1 q).mp
        (show (n : ZMod q) = ((1 : ℕ) : ZMod q) by simpa using hn_one)).symm
  exact (Nat.minFac_le_of_dvd hqprime.two_le hqpred).trans
    (Nat.minFac_le (by omega : 0 < m))

/-- OEIS A092028: for every `n > 2`, the least `m > 1` dividing
`n ^ m - 1` is the least prime factor of `n - 1`. -/
theorem firoozbakht_a092028 :
    ∀ n : ℕ, 2 < n → a n = Nat.minFac (n - 1) := by
  intro n hn
  let p := Nat.minFac (n - 1)
  have hpprime : p.Prime := Nat.minFac_prime (by omega)
  have hpdiv : p ∣ n - 1 := Nat.minFac_dvd (n - 1)
  have hnmod : Nat.ModEq p n 1 :=
    ((Nat.modEq_iff_dvd' (by omega : 1 ≤ n)).2 hpdiv).symm
  have hpmod : Nat.ModEq p (n ^ p) 1 := by
    simpa using hnmod.pow p
  have hpmem : p ∈ {m : ℕ | 1 < m ∧ m ∣ n ^ m - 1} := by
    refine ⟨hpprime.one_lt, ?_⟩
    exact (Nat.modEq_iff_dvd' (one_le_pow₀ (by omega : 1 ≤ n))).mp hpmod.symm
  have hnonempty : ({m : ℕ | 1 < m ∧ m ∣ n ^ m - 1} : Set ℕ).Nonempty :=
    ⟨p, hpmem⟩
  apply le_antisymm
  · unfold a
    exact Nat.sInf_le hpmem
  · have hamem : a n ∈ {m : ℕ | 1 < m ∧ m ∣ n ^ m - 1} := by
      unfold a
      exact Nat.sInf_mem hnonempty
    exact minFac_sub_one_le_of_dvd_pow_sub_one hn hamem.1 hamem.2

#print axioms firoozbakht_a092028

end D5.S3.Arith.Congruence.FiroozbakhtLeastSelfDivisorPowerMinusOne
