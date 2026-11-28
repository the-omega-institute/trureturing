/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicPurePrimeResidueClock
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicPurePrimeResidueClock
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The full native ring-of-integers residue algebra has a pure clock at a class of primes. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeForwardSplitting
import D5.S3.Arith.GoldenApparition
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicPurePrimeResidueClock
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeForwardSplitting

private theorem goldenMod_phi_pair (p n : ℕ) :
    (GoldenMod.phi : GoldenMod p) ^ (n + 1) =
      ⟨(Nat.fib n : ZMod p), (Nat.fib (n + 1) : ZMod p)⟩ := by
  have h := congrArg (GoldenMod.reduce p) (golden_phi_pow_eq_fib_pair n)
  have hphi : GoldenMod.reduce p D5.S0.Carrier.phi = GoldenMod.phi := by
    apply GoldenMod.ext <;> norm_num [GoldenMod.reduce, D5.S0.Carrier.phi, GoldenMod.phi]
  have hr : GoldenMod.reduce p (⟨(Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ)⟩ : GoldenInt) =
      ⟨(Nat.fib n : ZMod p), (Nat.fib (n + 1) : ZMod p)⟩ := by
    apply GoldenMod.ext
    · change (((Nat.fib n : ℕ) : ℤ) : ZMod p) = (Nat.fib n : ZMod p)
      rw [Int.cast_natCast]
    · change (((Nat.fib (n + 1) : ℕ) : ℤ) : ZMod p) = (Nat.fib (n + 1) : ZMod p)
      rw [Int.cast_natCast]
  simpa only [map_pow, hphi, hr] using h

private theorem phi_square_period {p : ℕ} (hp : p.Prime) (hp5 : 5<p)
    (hsign : @legendreSym 5 ⟨Nat.prime_five⟩ p = -1) :
    (GoldenMod.phi : GoldenMod p) ^ (2 * (p + 1)) = 1 := by
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpNot : ¬p ∣ 5 := Nat.not_dvd_of_pos_of_lt (by decide) hp5
  have hentry := fibonacci_apparition_entry_point hp hpNot
  have hfnext : (Nat.fib (p + 1) : ZMod p) = 0 := by
    have h := hentry.1
    rw [hsign] at h
    have hh : (p : ℤ) - -1 = ((p + 1 : ℕ) : ℤ) := by omega
    rwa [hh, Int.fib_natCast, Int.cast_natCast] at h
  have hfp : (Nat.fib p : ZMod p) = -1 := by
    simpa only [Int.fib_natCast, Int.cast_natCast, hsign, Int.cast_neg, Int.cast_one] using hentry.2
  have hpow : (GoldenMod.phi : GoldenMod p) ^ (p + 1) = -1 := by
    have h := goldenMod_phi_pair p p
    apply GoldenMod.ext
    · simpa using (congrArg GoldenMod.a h).trans hfp
    · simpa using (congrArg GoldenMod.b h).trans hfnext
  rw [Nat.mul_comm 2, pow_mul, hpow]
  norm_num

/-- The native signed Lucas clock is purely periodic for primes in the
specified quadratic and mod-three class. Every native block is a unit
at those primes. The period transfer does not invoke Chebotarev. -/
theorem pure_clock_nonsplit_golden {p : ℕ} (hp : p.Prime) (hp5 : 5<p)
    (hp3 : p % 3 = 1) (hsign : @legendreSym 5 ⟨Nat.prime_five⟩ p = -1) :
    (∃ t : ℕ, 0<t ∧ ∀ j : ℕ,
      (goldenLucas (3 ^ (j + t)) : ZMod p) = (goldenLucas (3 ^ j) : ZMod p)) ∧
    (∀ j : ℕ, 1 ≤ j → (goldenLucas (3 ^ j) : ZMod p) ^ 2 + 3 ≠ 0) := by
  let M := 2 * (p + 1)
  have hm : 0<M := by dsimp [M]; omega
  let _ : NeZero M := ⟨hm.ne'⟩
  let g : GoldenMod p := GoldenMod.phi
  have hg : g ^ M = 1 := phi_square_period hp hp5 hsign
  have hcp : Nat.Coprime 3 M := Nat.prime_three.coprime_iff_not_dvd.mpr (by
    intro h
    have h0 := Nat.mod_eq_zero_of_dvd h
    dsimp [M] at h0
    omega)
  let u := ZMod.unitOfCoprime 3 hcp
  let t := orderOf u
  have ht : 0<t := orderOf_pos u
  have hmT : (3 : ZMod M) ^ t = 1 := by
    have h := congrArg (fun v : (ZMod M)ˣ => (v : ZMod M)) (pow_orderOf_eq_one u)
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, u, ZMod.coe_unitOfCoprime, Nat.cast_ofNat] using h
  have hgfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨M, hm, hg⟩
  have hdiv : orderOf g ∣ M := orderOf_dvd_of_pow_eq_one hg
  have hper (j : ℕ) : (goldenLucas (3 ^ (j + t)) : ZMod p) =
      (goldenLucas (3 ^ j) : ZMod p) := by
    have hcast : ((3 ^ (j + t) : ℕ) : ZMod M) = ((3 ^ j : ℕ) : ZMod M) := by
      push_cast
      rw [pow_add, hmT, mul_one]
    have he : Nat.ModEq M (3 ^ (j + t)) (3 ^ j) := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    have hgg : g ^ (3 ^ (j + t)) = g ^ (3 ^ j) := hgfin.pow_eq_pow_iff_modEq.mpr (he.of_dvd hdiv)
    have hred (n : ℕ) :
        (goldenLucas n : ZMod p) =
          2 * (g ^ n).a + (g ^ n).b := by
      have hr : GoldenMod.reduce p D5.S0.Carrier.phi = g := by
        apply GoldenMod.ext <;> norm_num [GoldenMod.reduce, D5.S0.Carrier.phi, GoldenMod.phi, g]
      have hpow : GoldenMod.reduce p (D5.S0.Carrier.phi ^ n) = g ^ n := by rw [map_pow, hr]
      rw [← hpow]
      simp [goldenLucas, trace, GoldenMod.reduce]
    rw [hred, hred, hgg]
  refine ⟨⟨t, ht, hper⟩, ?_⟩
  intro j hj hB
  have hz := later_lucas_vanishes j (j + t) hj (by omega) hB
  rw [hper j] at hz
  rw [hz, zero_pow (by decide : 2 ≠ 0), zero_add] at hB
  exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 3<p))
    ((ZMod.natCast_eq_zero_iff 3 p).mp hB)

open Polynomial NumberField
open scoped NumberField
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic

/-- Literal cubic reductions at any modulus; the root coefficient is
transported before taking the field-of-integers quotient. -/
theorem cubic_map_reduction (p : ℕ) (l : ℤ) :
    (cubic l).toPoly.map (Int.castRingHom (ZMod p)) = (cubic (l : ZMod p)).toPoly := by
  rw [← Cubic.map_toPoly]
  congr 1
  ext <;> simp [Cubic.map, cubic]

/-- Good-prime residue algebras, not only root counts, are periodic
along the actual native field sequence for primes of the specified class. -/
theorem pure_native_residue_ring_clock {p : ℕ} (hp : p.Prime) (hp5 : 5<p)
    (hp3 : p % 3 = 1) (hsign : @legendreSym 5 ⟨Nat.prime_five⟩ p = -1) :
    let K (j : ℕ) := ((cubic (goldenLucas (3 ^ j) : ℚ)).toPoly).SplittingField
    ∃ t : ℕ, 0<t ∧ ∀ j : ℕ, 1 ≤ j →
      Nonempty (((𝓞 (K (j + t))) ⧸ Ideal.span {(p : 𝓞 (K (j + t)))}) ≃+*
        ((𝓞 (K j)) ⧸ Ideal.span {(p : 𝓞 (K j))})) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let K (j : ℕ) := ((cubic (goldenLucas (3 ^ j) : ℚ)).toPoly).SplittingField
  let poly (j : ℕ) := (cubic (goldenLucas (3 ^ j) : ZMod p)).toPoly
  obtain ⟨⟨t, ht, hL⟩, hunit⟩ := pure_clock_nonsplit_golden hp hp5 hp3 hsign
  have hq (j : ℕ) (hj : 1 ≤ j) :
      Nonempty (((𝓞 (K j)) ⧸ Ideal.span {(p : 𝓞 (K j))}) ≃+*
        ((ZMod p)[X] ⧸ Ideal.span {poly j})) := by
    let _ : NumberField (K j) := ⟨⟩
    obtain ⟨α, hmin, hgood⟩ := native_conductor_witness j hj
    have he := hgood p (by omega) hp (hunit j hj)
    have h := (RingOfIntegers.ZModXQuotSpanEquivQuotSpan he).symm
    rw [hmin, cubic_map_reduction] at h
    exact ⟨h⟩
  refine ⟨t, ht, ?_⟩
  intro j hj
  obtain ⟨f⟩ := hq (j + t) (by omega)
  obtain ⟨g⟩ := hq j hj
  have hc : poly (j + t) = poly j := by
    dsimp [poly]
    rw [hL]
  rw [hc] at f
  exact ⟨f.trans g.symm⟩

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicPurePrimeResidueClock
