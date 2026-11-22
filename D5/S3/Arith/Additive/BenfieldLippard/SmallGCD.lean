/- GID: D5/S3/Arith/Additive/BenfieldLippard/SmallGCD
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/BenfieldLippard/SmallGCD
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Small shifted powers have gcd one for the odd-exponent bound. -/

import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace BenfieldLippard

def smallGenerators (k m : ℕ) : Set ℕ :=
  (fun a : ℕ ↦ a ^ k - 1) '' Set.Icc 1 m

private theorem roots_family_injective (m : ℕ) :
    Function.Injective (fun x : Fin 7 × Fin ((m + 1) / 2) ↦
      2 ^ x.1.val * (2 * x.2.val + 1)) := by
  intro x y h
  change 2 ^ x.1.val * (2 * x.2.val + 1) = 2 ^ y.1.val * (2 * y.2.val + 1) at h
  have valuation (z : Fin 7 × Fin ((m + 1) / 2)) :
      (2 ^ z.1.val * (2 * z.2.val + 1)).factorization 2 = z.1.val := by
    rw [Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by omega),
      add_zero]
  have e : x.1.val = y.1.val := by
    rw [← valuation x, ← valuation y, h]
  have h₁ : x.1 = y.1 := Fin.ext e
  rw [e] at h
  have h₂ := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ y.1.val) h
  exact Prod.ext h₁ (Fin.ext (by omega))

theorem small_gcd (p k : ℕ) (hp : 193 ≤ p) (hk : 0 < k) (hkp : k ≤ p)
    (hodd : Odd k) : Nat.setGcd (smallGenerators k (p / 3)) = 1 := by
  classical
  let m := p / 3
  have hm : 64 ≤ m := by omega
  change Nat.setGcd (smallGenerators k m) = 1
  by_contra hn
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hn
  let : Fact q.Prime := ⟨hq⟩
  have hroot (a : ℕ) (ha : 1 ≤ a) (ham : a ≤ m) : (a : ZMod q) ^ k = 1 := by
    have hd : q ∣ a ^ k - 1 := (Nat.dvd_setGcd_iff.mp hqd) _ ⟨a, ⟨ha, ham⟩, rfl⟩
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [Nat.cast_sub (Nat.one_le_pow _ _ ha), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at hz
    exact hz
  have hmq : m < q := by
    by_contra! h
    have hh := hroot q hq.one_lt.le h
    rw [ZMod.natCast_self, zero_pow hk.ne'] at hh
    exact zero_ne_one hh
  by_cases hqsmall : q ≤ m * m
  · let u := q / m
    let r := q % m
    have hu : 1 ≤ u := Nat.div_pos (by omega) (by omega)
    have hum : u ≤ m := (Nat.div_le_iff_le_mul (by omega : 0 < m)).mpr (by
      calc
        q ≤ m * m := hqsmall
        _ ≤ m * (m + 1) - 1 := by rw [Nat.mul_succ]; omega)
    have hrm : r < m := Nat.mod_lt q (by omega)
    have hr : 1 ≤ r := by
      by_contra! hh
      have hmdiv : m ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
      rcases (Nat.dvd_prime hq).mp hmdiv with h | h <;> omega
    have hdiv : r + m * u = q := Nat.mod_add_div q m
    have hcast : (r : ZMod q) + (m : ZMod q) * (u : ZMod q) = 0 := by
      simpa using congrArg (fun n : ℕ ↦ (n : ZMod q)) hdiv
    have hneg : (m : ZMod q) * (u : ZMod q) = -(r : ZMod q) :=
      eq_neg_of_add_eq_zero_right hcast
    have heq := congrArg (fun z : ZMod q ↦ z ^ k) hneg
    change ((m : ZMod q) * (u : ZMod q)) ^ k = (-(r : ZMod q)) ^ k at heq
    rw [mul_pow, hroot m (by omega) le_rfl, hroot u hu hum, one_mul,
      hodd.neg_pow, hroot r hr hrm.le] at heq
    have htwo : ((2 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_ofNat, ← one_add_one_eq_two]
      exact (congrArg (fun z : ZMod q ↦ 1 + z) heq).trans (add_neg_cancel 1)
    exact (show ¬ q ∣ 2 from fun h ↦ by have := Nat.le_of_dvd (by decide : 0 < 2) h; omega)
      ((ZMod.natCast_eq_zero_iff _ _).mp htwo)
  · let bases : Fin 7 × Fin ((m + 1) / 2) → ℕ :=
      fun x ↦ 2 ^ x.1.val * (2 * x.2.val + 1)
    have hbases (x : Fin 7 × Fin ((m + 1) / 2)) : bases x < q := by
      have hx₁ : 2 ^ x.1.val ≤ 64 := by
        calc
          _ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 64 := by decide
      have hx₂ : 2 * x.2.val + 1 ≤ m := by have := x.2.isLt; omega
      calc
        bases x ≤ 64 * m := Nat.mul_le_mul hx₁ hx₂
        _ ≤ m * m := Nat.mul_le_mul_right _ hm
        _ < q := lt_of_not_ge hqsmall
    let roots := Polynomial.nthRootsFinset k (1 : ZMod q)
    let f : Fin 7 × Fin ((m + 1) / 2) → roots := fun x ↦ ⟨bases x, by
      apply (Polynomial.mem_nthRootsFinset hk (1 : ZMod q)).mpr
      have hx₂ : 2 * x.2.val + 1 ≤ m := by have := x.2.isLt; omega
      change ((bases x : ℕ) : ZMod q) ^ k = 1
      simp only [bases, Nat.cast_mul, Nat.cast_pow]
      rw [mul_pow, ← pow_mul, Nat.mul_comm x.1.val k, pow_mul,
        hroot 2 (by decide) (by omega), one_pow, one_mul, hroot _ (by omega) hx₂]⟩
    have hf : Function.Injective f := by
      intro x y h
      apply roots_family_injective m
      have he : (bases x : ZMod q) = (bases y : ZMod q) := congrArg Subtype.val h
      simpa [ZMod.val_natCast_of_lt (hbases x), ZMod.val_natCast_of_lt (hbases y)]
        using congrArg ZMod.val he
    have hc : 7 * ((m + 1) / 2) ≤ roots.card := by
      simpa using Fintype.card_le_of_injective f hf
    have hcr : roots.card ≤ k := by
      dsimp [roots]
      rw [Polynomial.nthRootsFinset_def]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots k 1)
    omega

end BenfieldLippard
