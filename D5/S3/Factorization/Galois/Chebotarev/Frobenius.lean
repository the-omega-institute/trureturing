/- GID: D5/S3/Factorization/Galois/Chebotarev/Frobenius
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/Frobenius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A prime ideal containing n also contains a rational prime divisor of n. -/
/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Frobenius
public import Mathlib.NumberTheory.RamificationInertia.Inertia

public import D5.S3.Analytic.Zeta.NumberField.Density
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Frobenius element of a Galois extension of number fields

For a Galois extension `L/K` of number fields and a prime `𝔓` of `𝓞 L` that
is unramified over its image `𝔭 = 𝔓 ∩ 𝓞 K`, the Frobenius automorphism
`Frob 𝔓 ∈ Gal(L/K)` is the unique element of the decomposition group whose
action on `𝓞 L / 𝔓` is the `N𝔭`-th power. As `𝔓` ranges over the primes of
`𝓞 L` above a fixed `𝔭`, the Frobenius elements form a single conjugacy
class in `Gal(L/K)`. This conjugacy class is the *Frobenius substitution* of
`𝔭` and is the object whose distribution Chebotarev describes.

The mathlib counterpart `ValuationSubring.decompositionSubgroup`
(`Mathlib.RingTheory.Valuation.RamificationGroup`) is defined for valuation
subrings of `L`, not for prime ideals of `𝓞 L`; we restate using ideals,
exploiting the `Pointwise` action `Ideal.pointwiseDistribMulAction`.

## Main definitions and results

* `Chebotarev.UnramifiedIn` states that `𝔭` is unramified in `L`.
* `Chebotarev.frobeniusClass` is the conjugacy class of
  Frobenius elements above a prime `𝔭` of `K`.
* Finiteness of the primes whose norm is not coprime to a fixed natural number is
  established at its use sites.

The Frobenius automorphism itself is mathlib's `arithFrobAt (𝓞 K) Gal(L/K) 𝔓`,
characterised among elements of `Gal(L/K)` by `IsArithFrobAt (𝓞 K) · 𝔓`; this
file does not wrap it.

## References

* Sharifi, *Algebraic Number Theory*, §2.6 (decomposition groups) and §7.2
  (`docs/algnum.pdf`).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, §3 (the
  Frobenius substitution) (`docs/cheb.pdf`).
-/

@[expose] public section

noncomputable section

open NumberField
open scoped Pointwise

namespace Chebotarev

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- A prime of `𝓞 K` is unramified in `L` if it is nonzero and every maximal prime above it
is unramified over `𝓞 K`. -/
@[nolint unusedArguments]
def UnramifiedIn [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : Prop :=
  𝔭 ≠ ⊥ ∧
    ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
      𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓

variable [NumberField K] [NumberField L]

/-- The Frobenius conjugacy class of a prime, with the trivial class as a default value. -/
def frobeniusClass [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : ConjClasses Gal(L/K) :=
  open Classical in
  if h : 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 then
    letI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
    haveI : 𝔭.IsPrime := h.1
    let e : ∃ 𝔓 : Ideal (𝓞 L), 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 := by
      obtain ⟨𝔓, hp, hcomap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
          rw [(RingHom.injective_iff_ker_eq_bot _).mp
            (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
          exact bot_le)
      exact ⟨𝔓, hp, ⟨hcomap.symm⟩⟩
    let 𝔓 := Classical.choose e
    haveI : 𝔓.IsPrime := (Classical.choose_spec e).1
    letI : 𝔓.LiesOver 𝔭 := (Classical.choose_spec e).2
    haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
      (Ideal.ne_bot_of_liesOver_of_ne_bot h.2.1 𝔓)
    ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
  else
    ConjClasses.mk 1



omit [NumberField K] in
/-- A prime ideal containing `(n : 𝓞 K)` for `1 < n` contains a prime factor of `n`. -/
theorem exists_prime_dvd_natCast_mem
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (n : ℕ) (hn1 : 1 < n) (hmem : (n : 𝓞 K) ∈ 𝔭) :
    ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ (r : 𝓞 K) ∈ 𝔭 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨r, hr, k, rfl⟩ := Nat.exists_prime_and_dvd (by lia : n ≠ 1)
    have hkpos : 0 < k := Nat.pos_of_ne_zero fun hk => by
      subst k
      simp only [mul_zero, Nat.not_lt_zero] at hn1
    have hcast : ((r * k : ℕ) : 𝓞 K) = (r : 𝓞 K) * (k : 𝓞 K) := by
      push_cast
      ring
    rw [hcast] at hmem
    rcases ‹𝔭.IsPrime›.mem_or_mem hmem with hrm | hkm
    · exact ⟨r, hr, ⟨k, rfl⟩, hrm⟩
    · by_cases hk1 : k = 1
      · subst hk1
        simp only [Nat.cast_one] at hkm
        exact absurd (Ideal.eq_top_of_isUnit_mem _ hkm isUnit_one) ‹𝔭.IsPrime›.ne_top
      · have hklt : k < r * k := (Nat.lt_mul_iff_one_lt_left hkpos).mpr hr.one_lt
        obtain ⟨s, hs, hsdvd, hsm⟩ := ih k hklt (by lia) hkm
        exact ⟨s, hs, hsdvd.trans ⟨r, by ring⟩, hsm⟩

end Chebotarev
