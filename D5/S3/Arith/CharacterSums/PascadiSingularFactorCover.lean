/- GID: D5/S3/Arith/CharacterSums/PascadiSingularFactorCover
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiSingularFactorCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted resultant bounds and a finite rational common-factor cover. -/

/- Provenance: integrated from the completed 2026-11-16 singular-cover research archive.
Original source SHA256: c2325493ea58a5a79ded8c4c26c14dc4813bbeac332f30d515346cb04cb282c4.
Canonical integration preserves the archived proofs; see the Pascadi Library note. -/

import D5.S3.Arith.CharacterSums.PascadiSingularResultant
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic

/-! # Weighted singular resultants and rational common factors -/

open Polynomial
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums

noncomputable section

private theorem resultant_abs_le_of_coeff_bound (f g : ℝ[X]) (d e : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ j, |f.coeff j| ≤ C) (hg : ∀ j, |g.coeff j| ≤ C) :
    |f.resultant g d e| ≤ ((d + e).factorial : ℝ) * C ^ (d + e) := by
  have h := Matrix.det_le (A := f.sylvester g d e)
    (abv := AbsoluteValue.abs) (x := C) (by
      intro i j
      induction j using Fin.addCases with
      | left j =>
          simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
          split_ifs <;> simp_all only [AbsoluteValue.abs_apply, abs_zero]
      | right j =>
          simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
          split_ifs <;> simp_all only [AbsoluteValue.abs_apply, abs_zero]
    )
  simpa only [Polynomial.resultant, AbsoluteValue.abs_apply, Fintype.card_fin,
    nsmul_eq_mul] using h

private theorem weight_cancel (J₁ J₂ : ℝ) (h₁ : J₁ ≠ 0) (h₂ : J₂ ≠ 0)
    (d j : ℕ) (hd : d = 2 ∨ d = 3) (hj : j ≤ d) :
    (J₁ ^ (3 - d) * J₂ ^ d)⁻¹ *
      (J₁ ^ (3 - j) * J₂ ^ j * (J₂ / J₁) ^ (d - j)) = 1 := by
  rcases hd with rfl | rfl <;> interval_cases j <;> norm_num <;>
    field_simp

private theorem normalized_coeff_bound (f : ℝ[X]) (J₁ J₂ C : ℝ)
    (h₁ : 0 < J₁) (h₂ : 0 < J₂) (hC : 0 ≤ C)
    (hd : f.natDegree = 2 ∨ f.natDegree = 3)
    (hf : ∀ j ≤ f.natDegree, |f.coeff j| ≤ C * J₁ ^ (3 - j) * J₂ ^ j) :
    ∀ j, |((Polynomial.C (J₁ ^ (3 - f.natDegree) * J₂ ^ f.natDegree)⁻¹) *
      f.scaleRoots (J₂ / J₁)).coeff j| ≤ C := by
  intro j
  by_cases hj : j ≤ f.natDegree
  · rw [coeff_C_mul, coeff_scaleRoots, abs_mul, abs_mul,
      abs_of_pos (inv_pos.mpr (mul_pos (pow_pos h₁ _) (pow_pos h₂ _))),
      abs_of_nonneg (pow_nonneg (div_nonneg h₂.le h₁.le) _)]
    calc
      _ ≤ (J₁ ^ (3 - f.natDegree) * J₂ ^ f.natDegree)⁻¹ *
          ((C * J₁ ^ (3 - j) * J₂ ^ j) * (J₂ / J₁) ^ (f.natDegree - j)) := by
        gcongr
        exact hf j hj
      _ = C * ((J₁ ^ (3 - f.natDegree) * J₂ ^ f.natDegree)⁻¹ *
          (J₁ ^ (3 - j) * J₂ ^ j * (J₂ / J₁) ^ (f.natDegree - j))) := by ring
      _ = C := by rw [weight_cancel J₁ J₂ h₁.ne' h₂.ne' _ _ hd hj, mul_one]
  · rw [coeff_C_mul, coeff_scaleRoots, coeff_eq_zero_of_natDegree_lt (by omega)]
    simpa using hC

private theorem undo_resultant_weight (J₁ J₂ : ℝ) (h₁ : J₁ ≠ 0) (h₂ : J₂ ≠ 0)
    (d e : ℕ) (hd : d = 2 ∨ d = 3) (he : e = 2 ∨ e = 3) :
    (J₁ ^ (3 - d) * J₂ ^ d)⁻¹ ^ e *
      ((J₁ ^ (3 - e) * J₂ ^ e)⁻¹ ^ d * (J₂ / J₁) ^ (d * e)) *
      (J₁ ^ (3 * (d + e) - d * e) * J₂ ^ (d * e)) = 1 := by
  rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;>
    norm_num <;> field_simp

/-- The actual resultant has the Sylvester determinant's exact weighted height. -/
theorem weighted_resultant_estimate (f g : ℝ[X]) (J₁ J₂ C : ℝ)
    (h₁ : 1 ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 1 ≤ C)
    (hd : f.natDegree = 2 ∨ f.natDegree = 3)
    (he : g.natDegree = 2 ∨ g.natDegree = 3)
    (hf : ∀ j ≤ f.natDegree, |f.coeff j| ≤ C * J₁ ^ (3 - j) * J₂ ^ j)
    (hg : ∀ j ≤ g.natDegree, |g.coeff j| ≤ C * J₁ ^ (3 - j) * J₂ ^ j) :
    |f.resultant g f.natDegree g.natDegree| ≤
      ((f.natDegree + g.natDegree).factorial : ℝ) * C ^ (f.natDegree + g.natDegree) *
        (J₁ ^ (3 * (f.natDegree + g.natDegree) - f.natDegree * g.natDegree) *
          J₂ ^ (f.natDegree * g.natDegree)) := by
  have h₁p : 0 < J₁ := lt_of_lt_of_le zero_lt_one h₁
  have h₂p : 0 < J₂ := lt_of_lt_of_le zero_lt_one h₂
  let a := J₁ ^ (3 - f.natDegree) * J₂ ^ f.natDegree
  let b := J₁ ^ (3 - g.natDegree) * J₂ ^ g.natDegree
  let r := J₂ / J₁
  let F := Polynomial.C a⁻¹ * f.scaleRoots r
  let G := Polynomial.C b⁻¹ * g.scaleRoots r
  have hbnd := resultant_abs_le_of_coeff_bound F G f.natDegree g.natDegree C
    (by positivity) (normalized_coeff_bound f J₁ J₂ C h₁p h₂p (by positivity) hd hf)
    (normalized_coeff_bound g J₁ J₂ C h₁p h₂p (by positivity) he hg)
  have heq : F.resultant G f.natDegree g.natDegree =
      a⁻¹ ^ g.natDegree * (b⁻¹ ^ f.natDegree * r ^ (f.natDegree * g.natDegree)) *
        f.resultant g f.natDegree g.natDegree := by
    dsimp [F, G]
    rw [resultant_C_mul_left, resultant_C_mul_right]
    rw [← natDegree_scaleRoots f r, ← natDegree_scaleRoots g r,
      resultant_scaleRoots]
    simp only [natDegree_scaleRoots]
    ring
  rw [heq, abs_mul, abs_of_pos (by dsimp [a, b, r]; positivity)] at hbnd
  have ht := mul_le_mul_of_nonneg_right hbnd
    (show 0 ≤ J₁ ^ (3 * (f.natDegree + g.natDegree) - f.natDegree * g.natDegree) *
      J₂ ^ (f.natDegree * g.natDegree) by positivity)
  have hu := undo_resultant_weight J₁ J₂ h₁p.ne' h₂p.ne' _ _ hd he
  dsimp only [a, b, r] at ht
  have hu' := congrArg (fun x : ℝ => x * |f.resultant g f.natDegree g.natDegree|) hu
  convert ht using 1
  linear_combination -hu'

/-- Uniform explicit height bound for degree two or three integer polynomials.
The coefficient hypotheses are weighted; the resultant bound is proved from them. -/
theorem integer_weighted_resultant_bound (f g : ℤ[X]) (J₁ J₂ C : ℝ)
    (h₁ : 1 ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 1 ≤ C)
    (hd : f.natDegree = 2 ∨ f.natDegree = 3)
    (he : g.natDegree = 2 ∨ g.natDegree = 3)
    (hf : ∀ j ≤ f.natDegree, |(f.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j)
    (hg : ∀ j ≤ g.natDegree, |(g.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j) :
    |(f.resultant g f.natDegree g.natDegree : ℝ)| ≤ 720 * C ^ 6 * (J₁ * J₂) ^ 9 := by
  have hmap : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hbound := weighted_resultant_estimate
    (f.map (Int.castRingHom ℝ)) (g.map (Int.castRingHom ℝ)) J₁ J₂ C h₁ h₂ hC
    (by simpa only [natDegree_map_eq_of_injective hmap] using hd)
    (by simpa only [natDegree_map_eq_of_injective hmap] using he)
    (by simpa only [natDegree_map_eq_of_injective hmap, coeff_map,
      Int.coe_castRingHom] using hf)
    (by simpa only [natDegree_map_eq_of_injective hmap, coeff_map,
      Int.coe_castRingHom] using hg)
  simp only [natDegree_map_eq_of_injective hmap, resultant_map_map,
    Int.coe_castRingHom] at hbound
  have hs : f.natDegree + g.natDegree ≤ 6 := by omega
  have ha : 3 * (f.natDegree + g.natDegree) - f.natDegree * g.natDegree ≤ 9 := by
    rcases hd with hd | hd <;> rcases he with he | he <;> simp [hd, he]
  have hb : f.natDegree * g.natDegree ≤ 9 := by
    rcases hd with hd | hd <;> rcases he with he | he <;> simp [hd, he]
  have hk : ((f.natDegree + g.natDegree).factorial : ℝ) ≤ 720 := by
    exact_mod_cast (Nat.factorial_le hs :
      (f.natDegree + g.natDegree).factorial ≤ (6 : ℕ).factorial)
  have hc : C ^ (f.natDegree + g.natDegree) ≤ C ^ 6 := pow_le_pow_right₀ hC hs
  have hw : J₁ ^ (3 * (f.natDegree + g.natDegree) - f.natDegree * g.natDegree) *
      J₂ ^ (f.natDegree * g.natDegree) ≤ J₁ ^ 9 * J₂ ^ 9 :=
    mul_le_mul (pow_le_pow_right₀ h₁ ha) (pow_le_pow_right₀ h₂ hb)
      (by positivity) (by positivity)
  calc
    _ ≤ _ := hbound
    _ ≤ (720 : ℝ) * C ^ 6 * (J₁ ^ 9 * J₂ ^ 9) :=
      mul_le_mul (mul_le_mul hk hc (by positivity) (by norm_num)) hw
        (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]

/-- The explicit weighted height gap and singular divisibility force zero resultant. -/
theorem weighted_singular_resultant_zero (f g : ℤ[X]) (b p : ℤ) (J₁ J₂ C : ℝ)
    (h₁ : 1 ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 1 ≤ C)
    (hd : f.natDegree = 2 ∨ f.natDegree = 3)
    (he : g.natDegree = 2 ∨ g.natDegree = 3)
    (hf : ∀ j ≤ f.natDegree, |(f.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j)
    (hg : ∀ j ≤ g.natDegree, |(g.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j)
    (hf₀ : p ^ 2 ∣ f.eval b) (hg₀ : p ^ 2 ∣ g.eval b)
    (hf₁ : p ∣ f.derivative.eval b) (hg₁ : p ∣ g.derivative.eval b)
    (hgap : 720 * C ^ 6 * (J₁ * J₂) ^ 9 < (p : ℝ) ^ 4) :
    f.resultant g f.natDegree g.natDegree = 0 := by
  have hdiv := singular_resultant_dvd_fourth f g b p (by omega) (by omega)
    hf₀ hg₀ hf₁ hg₁
  have hbnd := integer_weighted_resultant_bound f g J₁ J₂ C h₁ h₂ hC hd he hf hg
  by_contra hn
  have hle := Int.le_abs_of_dvd hn hdiv
  have hle' : (p : ℝ) ^ 4 ≤ |(f.resultant g f.natDegree g.natDegree : ℝ)| := by
    exact_mod_cast hle
  exact (not_lt_of_ge hle') (hbnd.trans_lt hgap)

open UniqueFactorizationMonoid

theorem rational_factor_card_le (f : ℚ[X]) (hf : f ≠ 0) :
    (normalizedFactors f).toFinset.card ≤ f.natDegree := by
  have hdeg := natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (prod_normalizedFactors hf))
  rw [natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)] at hdeg
  have hcard : (normalizedFactors f).card ≤
      ((normalizedFactors f).map Polynomial.natDegree).sum := by
    simpa using (Multiset.sum_map_le_sum_map (fun _ : ℚ[X] => (1 : ℕ))
      Polynomial.natDegree (s := normalizedFactors f)
      (fun q hq => (irreducible_of_normalized_factor q hq).natDegree_pos))
  exact (Multiset.toFinset_card_le _).trans (hcard.trans hdeg.le)

theorem rational_common_factor_of_resultant_zero (f g : ℚ[X]) (hf : f ≠ 0)
    (hres : f.resultant g f.natDegree g.natDegree = 0) :
    ∃ q ∈ (normalizedFactors f).toFinset, Irreducible q ∧ q ∣ f ∧ q ∣ g := by
  have hnot := (Polynomial.resultant_eq_zero_iff.mp hres).2
  classical
  by_contra hn
  apply hnot
  apply isCoprime_of_irreducible_dvd (by simp [hf])
  intro q hq hqf hqg
  obtain ⟨r, hr, ha⟩ := exists_mem_normalizedFactors_of_dvd hf hq hqf
  exact hn ⟨r, Multiset.mem_toFinset.mpr hr, irreducible_of_normalized_factor r hr,
    dvd_of_mem_normalizedFactors hr, ha.symm.dvd.trans hqg⟩

/-- A singular family satisfying the proved height bound has a cover by at most
three irreducible rational factors of any fixed member. No local root property
of the chosen common factor is asserted. -/
theorem weighted_singular_factor_cover (S : Set ℤ[X]) (f₀ : ℤ[X]) (hf₀ : f₀ ∈ S)
    (b p : ℤ) (J₁ J₂ C : ℝ) (h₁ : 1 ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 1 ≤ C)
    (hdeg : ∀ f ∈ S, f.natDegree = 2 ∨ f.natDegree = 3)
    (hcoeff : ∀ f ∈ S, ∀ j ≤ f.natDegree,
      |(f.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j)
    (hroot : ∀ f ∈ S, p ^ 2 ∣ f.eval b)
    (hderiv : ∀ f ∈ S, p ∣ f.derivative.eval b)
    (hgap : 720 * C ^ 6 * (J₁ * J₂) ^ 9 < (p : ℝ) ^ 4) :
    ∃ F : Finset ℚ[X], F.card ≤ 3 ∧
      (∀ q ∈ F, Irreducible q ∧ q ∣ f₀.map (Int.castRingHom ℚ)) ∧
      (∀ f ∈ S, ∃ q ∈ F, q ∣ f.map (Int.castRingHom ℚ)) := by
  have hmapQ : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hf₀ne : f₀ ≠ 0 := by
    intro hz
    have := hdeg f₀ hf₀
    simp [hz] at this
  have hf₀Q : f₀.map (Int.castRingHom ℚ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hf₀ne
  refine ⟨(normalizedFactors (f₀.map (Int.castRingHom ℚ))).toFinset, ?_, ?_, ?_⟩
  · have hc := rational_factor_card_le (f₀.map (Int.castRingHom ℚ)) hf₀Q
    rw [natDegree_map_eq_of_injective hmapQ] at hc
    exact hc.trans (by have := hdeg f₀ hf₀; omega)
  · intro q hq
    have hq' := Multiset.mem_toFinset.mp hq
    exact ⟨irreducible_of_normalized_factor q hq', dvd_of_mem_normalizedFactors hq'⟩
  · intro f hf
    have hz := weighted_singular_resultant_zero f₀ f b p J₁ J₂ C h₁ h₂ hC
      (hdeg f₀ hf₀) (hdeg f hf) (hcoeff f₀ hf₀) (hcoeff f hf)
      (hroot f₀ hf₀) (hroot f hf) (hderiv f₀ hf₀) (hderiv f hf) hgap
    have hzQ : (f₀.map (Int.castRingHom ℚ)).resultant (f.map (Int.castRingHom ℚ))
        (f₀.map (Int.castRingHom ℚ)).natDegree (f.map (Int.castRingHom ℚ)).natDegree = 0 := by
      simp only [natDegree_map_eq_of_injective hmapQ, resultant_map_map,
        hz, map_zero]
    obtain ⟨q, hq, _, _, hqf⟩ := rational_common_factor_of_resultant_zero
      (f₀.map (Int.castRingHom ℚ)) (f.map (Int.castRingHom ℚ)) hf₀Q hzQ
    exact ⟨q, hq, hqf⟩


end

end D5.S3.Arith.CharacterSums
