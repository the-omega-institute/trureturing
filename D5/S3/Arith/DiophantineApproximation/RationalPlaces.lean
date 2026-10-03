/- GID: D5/S3/Arith/DiophantineApproximation/RationalPlaces
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/RationalPlaces
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every rational p-adic absolute value is exactly a finite place of the rational field. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.DiophantineApproximation.PlacesOverFinite
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.NumberTheory.Height.NumberField

@[expose] public section

open NumberField Height

namespace Rat

/-- **Every finite place of `ℚ` is a `p`-adic absolute value, on the nose.** Ostrowski's theorem
gives the equivalence; the exponent is pinned to `1` by the height of `p⁻¹`. -/
theorem exists_prime_padic_eq (v : FinitePlace ℚ) :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, v.1 = AbsoluteValue.padic p := by
  have exists_prime_rpow_padic_eq (w : FinitePlace ℚ) :
      ∃ p : ℕ, ∃ _ : Fact p.Prime, ∃ c : ℝ, 0 < c ∧
        ∀ x : ℚ, w x ^ c = AbsoluteValue.padic p x := by
    have hbdd : ∀ n : ℕ, w.1 (n : ℚ) ≤ 1 := fun n ↦ by
      rw [← NumberField.FinitePlace.coe_apply]
      rw [← w.norm_embedding_eq, NumberField.FinitePlace.norm_embedding]
      exact HeightOneSpectrum.adicAbv_natCast_le_one ℚ w.maximalIdeal n
    have hnt : w.1.IsNontrivial := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.maximalIdeal.ne_bot
      refine ⟨((y : 𝓞 ℚ) : ℚ), ?_, ?_⟩
      · exact_mod_cast fun h ↦ hy0 (by exact_mod_cast h)
      · have h1 : NumberField.FinitePlace.mk w.maximalIdeal ((y : 𝓞 ℚ) : ℚ) < 1 :=
          ((show NumberField.FinitePlace.mk w.maximalIdeal (y : ℚ) < 1 ↔
              y ∈ w.maximalIdeal.asIdeal from by
        rw [NumberField.FinitePlace.mk_apply]
        exact NumberField.FinitePlace.norm_lt_one_iff_mem ℚ w.maximalIdeal y)).mpr hy
        rw [NumberField.FinitePlace.mk_maximalIdeal] at h1
        exact ne_of_lt h1
    obtain ⟨p, ⟨hp, heq⟩, -⟩ := AbsoluteValue.equiv_padic_of_bounded hnt hbdd
    obtain ⟨c, hc, hfun⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp heq
    exact ⟨p, hp, c, hc, fun x ↦ congrFun hfun x⟩
  obtain ⟨p, hp, c, hc, hv⟩ := exists_prime_rpow_padic_eq v
  refine ⟨p, hp, ?_⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
  have hFinitePlaceEq {v w : FinitePlace ℚ} {c c' : ℝ}
      (hc : 0 < c) (hc' : 0 < c') (hv : ∀ x : ℚ, v x ^ c = AbsoluteValue.padic p x)
      (hw : ∀ x : ℚ, w x ^ c' = AbsoluteValue.padic p x) : v = w := by
    refine NumberField.FinitePlace.maximalIdeal_injective ?_
    refine IsDedekindDomain.HeightOneSpectrum.ext (SetLike.ext fun y ↦ ?_)
    rw [← NumberField.FinitePlace.norm_lt_one_iff_mem ℚ v.maximalIdeal y,
      ← NumberField.FinitePlace.norm_lt_one_iff_mem ℚ w.maximalIdeal y,
      ← RingOfIntegers.coe_eq_algebraMap, NumberField.FinitePlace.norm_embedding_eq,
      NumberField.FinitePlace.norm_embedding_eq]
    have h1 : v (y : ℚ) < 1 ↔ AbsoluteValue.padic p (y : ℚ) < 1 := by
      rw [← hv (y : ℚ)]
      exact (Real.rpow_lt_one_iff' (by positivity) hc).symm
    have h2 : w (y : ℚ) < 1 ↔ AbsoluteValue.padic p (y : ℚ) < 1 := by
      rw [← hw (y : ℚ)]
      exact (Real.rpow_lt_one_iff' (by positivity) hc').symm
    exact h1.trans h2.symm
  -- the height of `p⁻¹` is `p`, and only `v` contributes to its finite part
  have hother : ∀ w : FinitePlace ℚ, w ≠ v → max (w ((p : ℚ)⁻¹)) 1 = 1 := by
    intro w hwv
    obtain ⟨q, hq, c', hc', hw⟩ := exists_prime_rpow_padic_eq w
    have hqp : q ≠ p := by
      rintro rfl
      exact hwv (hFinitePlaceEq hc' hc hw hv)
    have hwp : w ((p : ℚ)) = 1 := by
      have h1 : w ((p : ℚ)) ^ c' = 1 := by
        rw [hw]
        have : padicNorm q (p : ℚ) = 1 := by
          rw [show ((p : ℚ)) = ((p : ℕ) : ℚ) by norm_num, padicNorm.nat_eq_one_iff]
          exact fun hdvd ↦ hqp ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp hdvd)
        simp [AbsoluteValue.padic_eq_padicNorm, this]
      have h0 : 0 ≤ w ((p : ℚ)) := by positivity
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd h1 (ne_of_lt (Real.rpow_lt_one h0 hlt hc'))
      · exact absurd h1 (ne_of_gt (Real.one_lt_rpow hgt hc'))
    have hinv : w ((p : ℚ)⁻¹) = 1 := by
      rw [NumberField.FinitePlace.coe_apply, map_inv₀, ← NumberField.FinitePlace.coe_apply, hwp,
        inv_one]
    rw [hinv, max_self]
  have hheight : mulHeight₁ ((p : ℚ)⁻¹) = (p : ℝ) := by
    rw [Height.mulHeight₁_inv, show ((p : ℚ)) = ((p : ℕ) : ℚ) by norm_num,
      Rat.mulHeight₁_natCast]
  rw [NumberField.mulHeight₁_eq] at hheight
  have harch : (∏ u : InfinitePlace ℚ, max (u ((p : ℚ)⁻¹)) 1 ^ u.mult) = 1 := by
    refine Finset.prod_eq_one fun u _ ↦ ?_
    have hone : max (u ((p : ℚ)⁻¹)) 1 = 1 := by
      rw [Rat.infinitePlace_apply, max_eq_right]
      have hp1 : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.out.one_lt.le
      have hq1 : |((p : ℚ))⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]
        rw [inv_le_one₀ (by linarith)]
        exact hp1
      exact_mod_cast hq1
    rw [hone, one_pow]
  rw [harch, one_mul, finprod_eq_single _ v hother] at hheight
  have hvp : v ((p : ℚ)⁻¹) = (p : ℝ) := by
    rcases max_cases (v ((p : ℚ)⁻¹)) 1 with ⟨h, -⟩ | ⟨h, hlt⟩
    · rw [← h]; exact hheight
    · rw [h] at hheight; linarith
  have hvp' : v ((p : ℚ)) = ((p : ℝ))⁻¹ := by
    have h1 : v ((p : ℚ)) * v ((p : ℚ)⁻¹) = 1 := by
      rw [NumberField.FinitePlace.coe_apply, NumberField.FinitePlace.coe_apply, ← map_mul,
        mul_inv_cancel₀ (show ((p : ℚ)) ≠ 0 by exact_mod_cast hp.out.ne_zero), map_one]
    rw [hvp] at h1
    field_simp at h1 ⊢
    linarith
  have hc1 : c = 1 := by
    have h1 : ((p : ℝ))⁻¹ ^ c = ((p : ℝ))⁻¹ := by
      have := hv ((p : ℚ))
      rw [hvp'] at this
      rw [this, AbsoluteValue.padic_eq_padicNorm,
        show ((p : ℚ)) = ((p : ℕ) : ℚ) by norm_num, padicNorm.padicNorm_p_of_prime]
      push_cast
      ring
    have hne : ((p : ℝ))⁻¹ ≠ 1 := by
      intro h
      rw [inv_eq_one] at h
      linarith
    have h2 : ((p : ℝ))⁻¹ ^ c = ((p : ℝ))⁻¹ ^ (1 : ℝ) := by rw [Real.rpow_one]; exact h1
    exact (Real.rpow_right_inj (by positivity) hne).mp h2
  refine AbsoluteValue.ext fun x ↦ ?_
  have := hv x
  rw [hc1, Real.rpow_one] at this
  rw [← this, NumberField.FinitePlace.coe_apply]

/-- **Every `p`-adic absolute value of `ℚ` is a finite place, on the nose.** The converse of
`Rat.exists_prime_padic_eq`. -/
theorem exists_finitePlace_val_eq_padic (p : ℕ) [Fact p.Prime] :
    ∃ v : FinitePlace ℚ, v.1 = AbsoluteValue.padic p := by
  have hp0 : ((p : ℚ)) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero
  have hna : IsNonarchimedean ((AbsoluteValue.padic p : AbsoluteValue ℚ ℝ) : ℚ → ℝ) := by
    intro x y
    simpa [AbsoluteValue.padic_eq_padicNorm] using
      (show ((padicNorm p (x + y) : ℚ) : ℝ) ≤ ((max (padicNorm p x) (padicNorm p y) : ℚ) : ℝ) by
        exact_mod_cast padicNorm.nonarchimedean (p := p))
  have hle : ∀ y : 𝓞 ℚ, AbsoluteValue.padic p ((y : ℚ)) ≤ 1 := fun y ↦ by
    have hy : ((y : ℚ)) = ((Rat.ringOfIntegersEquiv y : ℤ) : ℚ) :=
      (Rat.ringOfIntegersEquiv_apply_coe y).symm
    rw [hy]
    exact AbsoluteValue.padic_le_one p _
  have hnt : ∃ y : 𝓞 ℚ, y ≠ 0 ∧ AbsoluteValue.padic p ((y : ℚ)) < 1 := by
    refine ⟨Rat.ringOfIntegersEquiv.symm (p : ℤ), ?_, ?_⟩
    · simpa using fun h ↦ (Fact.out (p := p.Prime)).ne_zero (by exact_mod_cast h)
    · rw [Rat.ringOfIntegersEquiv_symm_apply_coe]
      simpa [AbsoluteValue.padic_eq_padicNorm] using
        (show ((padicNorm p ((p : ℤ) : ℚ) : ℚ) : ℝ) < 1 by
          rw [show (((p : ℤ) : ℚ)) = ((p : ℕ) : ℚ) by push_cast; ring]
          exact_mod_cast padicNorm.padicNorm_p_lt_one_of_prime (p := p))
  obtain ⟨P, t, ht, hPt⟩ := AbsoluteValue.exists_heightOneSpectrum_rpow_eq hna hle hnt
  obtain ⟨q, hq, hqv⟩ := exists_prime_padic_eq (NumberField.FinitePlace.mk P)
  have hkey : ∀ x : ℚ, AbsoluteValue.padic p x = AbsoluteValue.padic q x ^ t := fun x ↦ by
    rw [hPt x, ← hqv, NumberField.FinitePlace.coe_apply]
  have hqp : q = p := by
    have h1 : AbsoluteValue.padic q ((p : ℚ)) ^ t = ((p : ℝ))⁻¹ := by
      rw [← hkey, AbsoluteValue.padic_eq_padicNorm,
        show ((p : ℚ)) = ((p : ℕ) : ℚ) by norm_num, padicNorm.padicNorm_p_of_prime]
      push_cast
      ring
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out (p := p.Prime)).two_le
    have hlt : AbsoluteValue.padic q ((p : ℚ)) < 1 := by
      by_contra hcon
      push Not at hcon
      have : (1 : ℝ) ≤ AbsoluteValue.padic q ((p : ℚ)) ^ t := Real.one_le_rpow hcon ht.le
      rw [h1] at this
      rw [le_inv_comm₀ (by norm_num) (by linarith)] at this
      linarith
    rw [AbsoluteValue.padic_eq_padicNorm, show ((p : ℚ)) = ((p : ℕ) : ℚ) by norm_num] at hlt
    have hdvd : q ∣ p := by
      by_contra hcon
      rw [show ((1 : ℝ)) = ((1 : ℚ) : ℝ) by norm_num, Rat.cast_lt] at hlt
      exact absurd ((padicNorm.nat_eq_one_iff (p := q) p).mpr hcon) (ne_of_lt hlt)
    exact (Nat.prime_dvd_prime_iff_eq hq.out (Fact.out (p := p.Prime))).mp hdvd
  subst hqp
  have ht1 : t = 1 := by
    have hp2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Fact.out (p := q.Prime)).two_le
    have h1 : ((q : ℝ))⁻¹ ^ t = ((q : ℝ))⁻¹ ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      have := hkey ((q : ℚ))
      rw [AbsoluteValue.padic_eq_padicNorm, show ((q : ℚ)) = ((q : ℕ) : ℚ) by norm_num,
        padicNorm.padicNorm_p_of_prime] at this
      push_cast at this
      rw [← this]
    have hne : ((q : ℝ))⁻¹ ≠ 1 := by
      intro h
      rw [inv_eq_one] at h
      linarith
    exact (Real.rpow_right_inj (by positivity) hne).mp h1
  subst ht1
  exact ⟨NumberField.FinitePlace.mk P, by simpa using hqv⟩

end Rat

/-- Every prime is prime. -/
instance Nat.Primes.instFactPrime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

namespace Rat

/-- The finite place of `ℚ` at a prime: the place whose absolute value is `padicNorm p`. -/
noncomputable def finitePlace (p : Nat.Primes) : FinitePlace ℚ :=
  (exists_finitePlace_val_eq_padic (p : ℕ)).choose

end Rat

end
