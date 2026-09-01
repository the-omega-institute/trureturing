/- GID: D5/S3/Factorization/Embeddings/RationalValuationRecovery
   generality: G
   mirror-B: D5/B/S3/Factorization/Embeddings/RationalValuationRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite prime valuations form a direct-sum profile recovering rationals up to sign. -/
/- Library-search audit trail (2026-08-28):
   * Repository search found `rational_finite_valuation_kernel_and_sign_recovery` in
     `RationalFiniteValuationKernel.lean`. Its profile is an inline abstract ledger, and no
     repository theorem identifies those coordinates with `padicValRat`; this file adds that
     concrete readout result rather than wrapping the existing theorem.
   * Pinned Mathlib hit `padicValRat`, `padicValRat_def`, `padicValRat.neg`, and `padicValInt` in
     `Mathlib.NumberTheory.Padics.PadicVal.Basic`; all applicable hits are used directly.
   * `Rat.num`, `Rat.den`, `Rat.reduced`, `Rat.mkRat`, and `Rat.mk'` were found in
     `Mathlib.Data.Rat.Defs`. Exact `Rat.mk` had no pinned-Mathlib source hit.
   * `Nat.factorization_def`, `Nat.factorization_inj`, and nonprime-coordinate vanishing were
     found in `Mathlib.Data.Nat.Factorization.Defs` and are applied directly.
   * `Finsupp.ofSupportFinite` in `Mathlib.Data.Finsupp.Defs` packages the proved finite support
     into the direct sum; its definitional coordinate equation is exposed below.
   * `UniqueFactorizationMonoid` was found in its ring-theory modules, but no rational recovery
     theorem was found. `Int.sign` was found in `Mathlib.Data.Int.Init`; `SignType.sign` is the
     exact sign readout used below. -/

import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Sign.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Embeddings.RationalValuationRecovery

/-- The finite support of the prime-valuation readout lies in the numerator and denominator
factorization supports. -/
private theorem rational_finite_valuation_support_finite (x : ℚ) :
    (Function.support fun p : Nat.Primes => padicValRat p x).Finite := by
  let primeEmbedding : Nat.Primes ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  let numSupport : Set Nat.Primes :=
    primeEmbedding ⁻¹' (x.num.natAbs.factorization.support : Set ℕ)
  let denSupport : Set Nat.Primes :=
    primeEmbedding ⁻¹' (x.den.factorization.support : Set ℕ)
  have hnumFinite : numSupport.Finite :=
    Set.Finite.preimage_embedding primeEmbedding x.num.natAbs.factorization.support.finite_toSet
  have hdenFinite : denSupport.Finite :=
    Set.Finite.preimage_embedding primeEmbedding x.den.factorization.support.finite_toSet
  apply (hnumFinite.union hdenFinite).subset
  intro p hp
  by_contra hpSupport
  have hpnumSupport : p ∉ numSupport := fun h => hpSupport (Or.inl h)
  have hpdenSupport : p ∉ denSupport := fun h => hpSupport (Or.inr h)
  have hpnum : x.num.natAbs.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff]
    exact hpnumSupport
  have hpden : x.den.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff]
    exact hpdenSupport
  apply hp
  simp only [padicValRat_def, padicValInt]
  rw [← Nat.factorization_def x.num.natAbs p.property,
    ← Nat.factorization_def x.den p.property, hpnum, hpden]
  norm_num

/-- The direct-sum profile of all finite prime valuations of a rational number. -/
noncomputable def rationalFiniteValuationProfile (x : ℚ) : Nat.Primes →₀ ℤ :=
  Finsupp.ofSupportFinite (fun p => padicValRat p x)
    (rational_finite_valuation_support_finite x)

/-- Each direct-sum coordinate is the corresponding `p`-adic valuation. -/
@[simp]
theorem rationalFiniteValuationProfile_apply (x : ℚ) (p : Nat.Primes) :
    rationalFiniteValuationProfile x p = padicValRat p x := by
  rfl
#print axioms rationalFiniteValuationProfile_apply

private theorem abs_eq_of_rational_finite_valuation_profile_eq
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hprofile : rationalFiniteValuationProfile x = rationalFiniteValuationProfile y) :
    |x| = |y| := by
  have hnumx : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx)
  have hnumy : y.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hy)
  have hcross : x.num.natAbs * y.den = y.num.natAbs * x.den := by
    apply Nat.factorization_inj
    · exact Nat.mul_ne_zero hnumx y.den_ne_zero
    · exact Nat.mul_ne_zero hnumy x.den_ne_zero
    · ext p
      by_cases hp : p.Prime
      · rw [Nat.factorization_mul hnumx y.den_ne_zero,
          Nat.factorization_mul hnumy x.den_ne_zero]
        simp only [Finsupp.add_apply]
        let prime : Nat.Primes := ⟨p, hp⟩
        have hv := DFunLike.congr_fun hprofile prime
        simp only [rationalFiniteValuationProfile_apply] at hv
        simp only [padicValRat_def, padicValInt] at hv
        rw [← Nat.factorization_def x.num.natAbs hp,
          ← Nat.factorization_def x.den hp,
          ← Nat.factorization_def y.num.natAbs hp,
          ← Nat.factorization_def y.den hp] at hv
        omega
      · simp [Nat.factorization_eq_zero_of_not_prime, hp]
  rw [Rat.abs_def, Rat.abs_def]
  apply (Rat.divInt_eq_divInt_iff
    (Int.natCast_ne_zero.mpr x.den_ne_zero)
    (Int.natCast_ne_zero.mpr y.den_ne_zero)).2
  exact_mod_cast hcross

/-- On nonzero rationals, equal finite-prime profiles are exactly equal absolute values.

Primality is load-bearing only through prime-factor coordinates and unique factorization:
`Nat.factorization_def` identifies a prime coordinate with `padicValNat`, while nonprime
coordinates vanish. No distribution theorem for primes is used, and `p > 1` alone is insufficient.
-/
theorem rational_finite_valuation_profile_eq_iff_abs_eq
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    rationalFiniteValuationProfile x = rationalFiniteValuationProfile y ↔ |x| = |y| := by
  constructor
  · exact abs_eq_of_rational_finite_valuation_profile_eq hx hy
  · intro habs
    ext p
    rcases abs_eq_abs.mp habs with hxy | hxy
    · rw [hxy]
    · rw [hxy]
      exact padicValRat.neg y
#print axioms rational_finite_valuation_profile_eq_iff_abs_eq

/-- A nonzero rational is uniquely determined by its sign and all finite prime valuations. -/
theorem rational_recovered_from_sign_and_finite_valuations
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hprofile : rationalFiniteValuationProfile x = rationalFiniteValuationProfile y)
    (hsign : SignType.sign x = SignType.sign y) :
    x = y := by
  have habs := (rational_finite_valuation_profile_eq_iff_abs_eq hx hy).mp hprofile
  rcases abs_eq_abs.mp habs with hxy | hxy
  · exact hxy
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · have hxpos : 0 < x := hxy.symm ▸ neg_pos.mpr hyneg
      rw [sign_pos hxpos, sign_neg hyneg] at hsign
      norm_num at hsign
    · have hxneg : x < 0 := hxy.symm ▸ neg_neg_of_pos hypos
      rw [sign_neg hxneg, sign_pos hypos] at hsign
      norm_num at hsign
#print axioms rational_recovered_from_sign_and_finite_valuations

/-- Equal `p`-adic valuations at every prime leave exactly the two possible rational signs. -/
theorem rational_finite_valuation_kernel
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hvaluation : ∀ p : ℕ, p.Prime → padicValRat p x = padicValRat p y) :
    x = y ∨ x = -y := by
  apply abs_eq_abs.mp
  apply (rational_finite_valuation_profile_eq_iff_abs_eq hx hy).mp
  ext p
  simp only [rationalFiniteValuationProfile_apply]
  exact hvaluation p p.property
#print axioms rational_finite_valuation_kernel

/-- Zero must be excluded on both sides because all its finite valuations equal those of one. -/
theorem nonzero_hypotheses_are_necessary :
    ((∀ p : ℕ, p.Prime → padicValRat p 0 = padicValRat p 1) ∧
      ¬((0 : ℚ) = 1 ∨ (0 : ℚ) = -1)) ∧
    ((∀ p : ℕ, p.Prime → padicValRat p 1 = padicValRat p 0) ∧
      ¬((1 : ℚ) = 0 ∨ (1 : ℚ) = -0)) := by
  constructor <;> constructor
  · simp
  · norm_num
  · simp
  · norm_num
#print axioms nonzero_hypotheses_are_necessary

/-- The equal-sign hypothesis is necessary: one and minus one have the same finite profile. -/
theorem sign_equality_is_necessary :
    rationalFiniteValuationProfile 1 = rationalFiniteValuationProfile (-1) ∧
      (1 : ℚ) ≠ -1 := by
  constructor
  · ext p
    simp [rationalFiniteValuationProfile]
  · norm_num
#print axioms sign_equality_is_necessary

/-- The valuation hypothesis is necessary: equal positive signs alone do not identify rationals. -/
theorem valuation_equality_is_necessary :
    SignType.sign (1 : ℚ) = SignType.sign (2 : ℚ) ∧ (1 : ℚ) ≠ 2 := by
  norm_num
#print axioms valuation_equality_is_necessary

/- Degenerate audit: `1`, `-1`, a negative rational, and a reduced fraction whose numerator and
denominator are both nontrivial. The last two coordinates read `v_2(6/35) = 1` and
`v_5(6/35) = -1`. -/
example :
    rationalFiniteValuationProfile 1 = rationalFiniteValuationProfile (-1) ∧
      rationalFiniteValuationProfile (-((6 : ℚ) / 35)) =
        rationalFiniteValuationProfile ((6 : ℚ) / 35) ∧
      rationalFiniteValuationProfile ((6 : ℚ) / 35) ⟨2, by norm_num⟩ = 1 ∧
      rationalFiniteValuationProfile ((6 : ℚ) / 35) ⟨5, by norm_num⟩ = -1 := by
  constructor
  · ext p
    simp [rationalFiniteValuationProfile]
  constructor
  · ext p
    simp [rationalFiniteValuationProfile]
  constructor
  · let two : Nat.Primes := ⟨2, by norm_num⟩
    letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    have htwo : rationalFiniteValuationProfile ((6 : ℚ) / 35) two = 1 := by
      rw [rationalFiniteValuationProfile_apply,
        padicValRat.div (by norm_num) (by norm_num)]
      have h6 : padicValNat 2 6 = 1 := by
        rw [show 6 = 2 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
          padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
      have h35 : padicValNat 2 35 = 0 :=
        padicValNat.eq_zero_of_not_dvd (by norm_num)
      norm_num [padicValRat, padicValInt, h6, h35]
    exact htwo
  · let five : Nat.Primes := ⟨5, by norm_num⟩
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hfive : rationalFiniteValuationProfile ((6 : ℚ) / 35) five = -1 := by
      rw [rationalFiniteValuationProfile_apply,
        padicValRat.div (by norm_num) (by norm_num)]
      have h6 : padicValNat 5 6 = 0 :=
        padicValNat.eq_zero_of_not_dvd (by norm_num)
      have h35 : padicValNat 5 35 = 1 := by
        rw [show 35 = 5 * 7 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
          padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
      norm_num [padicValRat, padicValInt, h6, h35]
    exact hfive

end D5.S3.Factorization.Embeddings.RationalValuationRecovery
