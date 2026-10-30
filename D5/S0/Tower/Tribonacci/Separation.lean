/- GID: D5/S0/Tower/Tribonacci/Separation
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/Separation
   mirror-E: none(waiver:infinite-family-arithmetic-estimate)
   anchors: []
   utility: none
   digest: Distinct admissible Tribonacci conjugate coordinates separate at their natural scale. -/

import D5.S0.Tower.Tribonacci.ModelSet
import D5.S0.Tower.Tribonacci.Gaps
import D5.S0.Tower.DBonacci.Irreducibility
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! The missing arithmetic fact is a uniform estimate for ALL distinct
length-Q admissible digit evaluations: integer cubic arithmetic prevents their
conjugate differences from collapsing below a fixed positive multiple of
`‖z‖ ^ Q`. The integer decoder does not supply this fact. The live proof must
bridge reversed admissible negative-power values to positive-power evaluation,
then establish a nonzero integral three-embedding norm and bound the Perron
factor. This is an infinite-family estimate, not bounded enumeration.

The method is the classical Pisot algebraic-norm separation argument. No
research novelty is asserted. The exact hypotheses are membership in the
existing Tribonacci characteristic root multiset and inequality to its Perron
root; either non-Perron root is in scope. -/

namespace D5.S0.Tower.Tribonacci.Separation

open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Values
open D5.S0.Tower.Tribonacci.ModelSet
open D5.S0.Tower.Tribonacci.Binet

set_option autoImplicit false
set_option relaxedAutoImplicit false

local notation "β" => tribonacciConstant

open Polynomial

private def digitPolynomial {Q : ℕ} (u : TribonacciName Q) : ℤ[X] :=
  ∑ i : Fin Q, if u.1 i then X ^ i.1 else 0

private theorem digitPolynomial_eval {R : Type*} [CommRing R]
    {Q : ℕ} (u : TribonacciName Q) (x : R) :
    (digitPolynomial u).eval₂ (Int.castRingHom R) x =
      ∑ i : Fin Q, if u.1 i then x ^ i.1 else 0 := by
  simp [digitPolynomial, eval₂_finsetSum, apply_ite]

private theorem admissible_reverse (Q : ℕ) (w : Fin Q → Bool)
    (hw : TribonacciAdmissible Q w) :
    TribonacciAdmissible Q (fun i => w i.rev) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
    match Q with
    | 0 => trivial
    | 1 => trivial
    | 2 => trivial
    | n + 3 =>
      rw [admissible_add_three_iff]
      constructor
      · intro h
        have hn := D5.S0.Tower.Tribonacci.Representation.admissible_no_three_at
          (n + 3) n w hw (by omega)
        apply hn
        rcases h with ⟨h0, h1, h2⟩
        convert And.intro h2 (And.intro h1 h0) using 1 <;>
          congr 1 <;> apply Fin.ext <;> simp [Fin.rev] <;> omega
      · have hi := ih (n + 2) (by omega) (Fin.init w)
          (D5.S0.Tower.Tribonacci.Representation.admissible_init (n + 2) w hw)
        convert hi using 1
        funext i
        apply congrArg w
        apply Fin.ext
        simp [Fin.tail, Fin.init, Fin.rev]
        omega

private def reverseName {Q : ℕ} (u : TribonacciName Q) : TribonacciName Q :=
  ⟨fun i => u.1 i.rev, admissible_reverse Q u.1 u.2⟩

private theorem reverse_value {Q : ℕ} (u : TribonacciName Q) :
    tribonacciNameValue Q (reverseName u) =
      β ^ (-(Q : ℤ)) * (digitPolynomial u).eval₂ (Int.castRingHom ℝ) β := by
  rw [tribonacciNameValue, tribonacciWordValue, digitPolynomial_eval,
    Finset.mul_sum, ← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro i _
  change (if u.1 i.rev.rev then β ^ (-((i.rev.1 + 1 : ℕ) : ℤ)) else 0) = _
  rw [Fin.rev_rev]
  split_ifs
  · rw [← zpow_natCast, ← zpow_add₀ tribonacciConstant_ne_zero]
    congr 1
    simp only [Fin.val_rev]
    have hi := i.2
    omega
  · ring

private theorem digit_difference_perron_ne_zero {Q : ℕ}
    (u v : TribonacciName Q) (huv : u ≠ v) :
    (digitPolynomial u - digitPolynomial v).eval₂ (Int.castRingHom ℝ) β ≠ 0 := by
  intro h
  rw [eval₂_sub] at h
  have hv : tribonacciNameValue Q (reverseName u) =
      tribonacciNameValue Q (reverseName v) := by
    rw [reverse_value, reverse_value, sub_eq_zero.mp h]
  have hn := D5.S0.Tower.Tribonacci.Gaps.tribonacciNameValue_injective Q hv
  apply huv
  apply Subtype.ext
  funext i
  have he := congrFun (congrArg Subtype.val hn) i.rev
  simpa [reverseName] using he

private def cubic : ℤ[X] := X ^ 3 - X ^ 2 - X - 1

private theorem cubic_irreducible :
    Irreducible (cubic.map (Int.castRingHom ℚ)) := by
  convert (D5.S0.Tower.DBonacci.PerronRoot.dbonacci_irreducible 3 (by norm_num)).2
    using 1 <;> simp [cubic, Finset.sum_range_succ] <;> ring

private theorem cubic_at_perron : cubic.eval₂ (Int.castRingHom ℝ) β = 0 := by
  simp only [cubic, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
  nlinarith [tribonacciConstant_cubic]

private theorem cubic_resultant_ne_zero (p : ℤ[X])
    (hp : p.eval₂ (Int.castRingHom ℝ) β ≠ 0) : cubic.resultant p ≠ 0 := by
  have hn : ¬ cubic.map (Int.castRingHom ℚ) ∣ p.map (Int.castRingHom ℚ) := by
    rintro ⟨a, ha⟩
    apply hp
    have he := congrArg (Polynomial.eval₂ (Rat.castHom ℝ) β) ha
    have hcomp : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
      ext n; simp
    simpa only [eval₂_mul, eval₂_map, hcomp, cubic_at_perron,
      zero_mul] using he
  have hc := cubic_irreducible.coprime_iff_not_dvd.mpr hn
  have hr := resultant_ne_zero _ _ hc
  have hdc := natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int cubic
  have hdp := natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int p
  intro hzero
  apply hr
  simpa only [hdc, hdp, resultant_map_map, hzero, map_zero]

private theorem secondary_root_relations {z : ℂ}
    (hz : z ∈ tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (β : ℂ)) :
    z + star z = ((1 - β : ℝ) : ℂ) ∧
      z * star z = ((β ^ 2 - β - 1 : ℝ) : ℂ) ∧
      β * ‖z‖ ^ 2 = 1 := by
  have hpoly : tribonacciCharacteristicPolynomial ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval (2 : ℂ)) h
    norm_num [tribonacciCharacteristicPolynomial] at he
  have he := (Polynomial.mem_roots hpoly).mp hz
  have hc : z ^ 3 = z ^ 2 + z + 1 := by
    have := he
    simp only [Polynomial.IsRoot, tribonacciCharacteristicPolynomial,
      eval_sub, eval_pow, eval_X, eval_one] at this
    linear_combination this
  have ht : (β : ℂ) ^ 3 = (β : ℂ) ^ 2 + β + 1 := by
    exact_mod_cast tribonacciConstant_cubic
  have hf : (z - (β : ℂ)) *
      (z ^ 2 + z * β + (β : ℂ) ^ 2 - z - β - 1) = 0 := by
    linear_combination hc - ht
  have hq := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hz_ne)
  have hi : β ^ 2 - β - 1 = β⁻¹ := by
    apply (eq_inv_iff_mul_eq_one₀ tribonacciConstant_ne_zero).mpr
    nlinarith [tribonacciConstant_cubic]
  have hquad : z ^ 2 + ((β - 1 : ℝ) : ℂ) * z + ((β⁻¹ : ℝ) : ℂ) = 0 := by
    rw [← hi]
    push_cast
    linear_combination hq
  have him := congrArg Complex.im hquad
  have hre := congrArg Complex.re hquad
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at him hre
  have him_ne : z.im ≠ 0 := by
    intro hzero
    rw [hzero] at hre
    have hd := D5.S0.Tower.Tribonacci.PerronRoot.tribonacci_errorEnergy_discriminant_pos
    nlinarith [sq_nonneg (2 * z.re + (β - 1))]
  have hre_eq : 2 * z.re + (β - 1) = 0 := by
    apply (mul_eq_zero.mp (show z.im * (2 * z.re + (β - 1)) = 0 by
      nlinarith [him])).resolve_left him_ne
  have hre_mul := congrArg (fun x : ℝ => z.re * x) hre_eq
  have hn : Complex.normSq z = β⁻¹ := by
    rw [Complex.normSq_apply]
    nlinarith [hre, hre_mul]
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ext <;> simp <;> linarith
  · rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, hn, hi]
  · rw [Complex.sq_norm, hn, mul_inv_cancel₀ tribonacciConstant_ne_zero]

private theorem cubic_factorization {z : ℂ}
    (hz : z ∈ tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (β : ℂ)) :
    cubic.map (Int.castRingHom ℂ) =
      (X - C (β : ℂ)) * (X - C z) * (X - C (star z)) := by
  obtain ⟨hsum, hprod, _⟩ := secondary_root_relations hz hz_ne
  have hquad : (X - C z) * (X - C (star z)) =
      X ^ 2 - C ((1 - β : ℝ) : ℂ) * X + C ((β ^ 2 - β - 1 : ℝ) : ℂ) := by
    calc
      _ = X ^ 2 - C (z + star z) * X + C (z * star z) := by
        simp only [map_add, map_mul]; ring
      _ = _ := by rw [hsum, hprod]
  rw [mul_assoc, hquad]
  have ht : (β : ℂ) ^ 3 = (β : ℂ) ^ 2 + β + 1 := by
    exact_mod_cast tribonacciConstant_cubic
  simp only [cubic, Polynomial.map_sub, Polynomial.map_pow, map_X, map_one]
  push_cast
  have hCt := congrArg (C : ℂ → ℂ[X]) ht
  simp only [map_add, map_pow, map_one] at hCt
  linear_combination hCt

private theorem resultant_three_embeddings {z : ℂ}
    (hz : z ∈ tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (β : ℂ)) (p : ℤ[X]) :
    (cubic.resultant p : ℂ) =
      (p.eval₂ (Int.castRingHom ℝ) β : ℂ) *
        p.eval₂ (Int.castRingHom ℂ) z *
        star (p.eval₂ (Int.castRingHom ℂ) z) := by
  let pc := p.map (Int.castRingHom ℂ)
  have hd : cubic.natDegree = 3 := by
    unfold cubic
    compute_degree!
  have hn : pc.natDegree ≤ p.natDegree := natDegree_map_le
  have htwo : ((X - C (β : ℂ)) * (X - C z)).natDegree = 2 := by
    rw [(monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
    simp
  have h12 := resultant_mul_left (X - C (β : ℂ)) (X - C z) pc p.natDegree hn
  have h123 := resultant_mul_left ((X - C (β : ℂ)) * (X - C z))
    (X - C (star z)) pc p.natDegree hn
  simp only [natDegree_X_sub_C, htwo, Nat.reduceAdd,
    resultant_X_sub_C_left _ _ _ hn] at h12 h123
  rw [h12] at h123
  have hmap := resultant_map_map cubic p cubic.natDegree p.natDegree (Int.castRingHom ℂ)
  rw [hd, cubic_factorization hz hz_ne] at hmap
  rw [← hmap, h123]
  simp only [pc, eval_map]
  have hreal := hom_eval₂ (Int.castRingHom ℝ) Complex.ofRealHom p β
  have hconj := hom_eval₂ (Int.castRingHom ℂ) (starRingEnd ℂ) p z
  have hcompR : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext n; simp
  have hcompC : (starRingEnd ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ := by
    ext n; simp
  rw [hcompR] at hreal
  rw [hcompC] at hconj
  rw [← hreal, ← hconj]
  rfl

private theorem integer_norm_lower_bound {z : ℂ}
    (hz : z ∈ tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (β : ℂ)) (p : ℤ[X])
    (hp : p.eval₂ (Int.castRingHom ℝ) β ≠ 0) :
    1 ≤ |p.eval₂ (Int.castRingHom ℝ) β| *
      ‖p.eval₂ (Int.castRingHom ℂ) z‖ ^ 2 := by
  have hn := cubic_resultant_ne_zero p hp
  have hi : (1 : ℤ) ≤ |cubic.resultant p| := by
    have := abs_pos.mpr hn
    omega
  have hc : (1 : ℝ) ≤ ‖(cubic.resultant p : ℂ)‖ := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast hi
  rw [resultant_three_embeddings hz hz_ne p, norm_mul, norm_mul,
    norm_star, Complex.norm_real, Real.norm_eq_abs] at hc
  nlinarith only [hc]

private theorem perron_difference_bound {Q : ℕ} (u v : TribonacciName Q) :
    |(digitPolynomial u - digitPolynomial v).eval₂ (Int.castRingHom ℝ) β| * (β - 1)
      ≤ β ^ Q := by
  have hb : |(digitPolynomial u - digitPolynomial v).eval₂ (Int.castRingHom ℝ) β|
      ≤ ∑ i : Fin Q, β ^ i.1 := by
    rw [eval₂_sub, digitPolynomial_eval, digitPolynomial_eval, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    cases hu : u.1 i <;> cases hv : v.1 i <;>
      simp [hu, hv, abs_of_nonneg (pow_nonneg tribonacciConstant_pos.le i.1)] <;>
      positivity
  have hg : (∑ i : Fin Q, β ^ i.1) * (β - 1) = β ^ Q - 1 := by
    rw [Fin.sum_univ_eq_sum_range, geom_sum_mul]
  have hm := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr one_lt_tribonacciConstant.le)
  rw [hg] at hm
  linarith

/-- Distinct length-`Q` admissible names are uniformly separated at the
natural conjugate scale, at either non-Perron Tribonacci root. -/
theorem conjugateCoordinate_separation {z : ℂ}
    (hz : z ∈ tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (β : ℂ)) (Q : ℕ) (u v : TribonacciName Q) (huv : u ≠ v) :
    Real.sqrt (β - 1) * ‖z‖ ^ Q ≤
      dist (conjugateCoordinate z u) (conjugateCoordinate z v) := by
  let p := digitPolynomial u - digitPolynomial v
  have hp : p.eval₂ (Int.castRingHom ℝ) β ≠ 0 :=
    digit_difference_perron_ne_zero u v huv
  have hn := integer_norm_lower_bound hz hz_ne p hp
  have hb := perron_difference_bound u v
  have hscale := (secondary_root_relations hz hz_ne).2.2
  have hpow : β ^ Q * (‖z‖ ^ Q) ^ 2 = 1 := by
    calc
      β ^ Q * (‖z‖ ^ Q) ^ 2 = (β * ‖z‖ ^ 2) ^ Q := by
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm Q 2]
      _ = 1 := by rw [hscale, one_pow]
  have ha : 0 < β - 1 := sub_pos.mpr one_lt_tribonacciConstant
  have hcoord : p.eval₂ (Int.castRingHom ℂ) z =
      conjugateCoordinate z u - conjugateCoordinate z v := by
    simp only [p, eval₂_sub, digitPolynomial_eval, conjugateCoordinate]
  rw [dist_eq_norm]
  rw [hcoord] at hn
  have ht : (β - 1) * (‖z‖ ^ Q) ^ 2 ≤
      ‖conjugateCoordinate z u - conjugateCoordinate z v‖ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hn ha.le
    have h2 := mul_le_mul_of_nonneg_right hb
      (sq_nonneg ‖conjugateCoordinate z u - conjugateCoordinate z v‖)
    change |p.eval₂ (Int.castRingHom ℝ) β| * (β - 1) *
      ‖conjugateCoordinate z u - conjugateCoordinate z v‖ ^ 2 ≤ _ at h2
    have h3 : β - 1 ≤ β ^ Q * ‖conjugateCoordinate z u - conjugateCoordinate z v‖ ^ 2 := by
      nlinarith only [h1, h2]
    have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (‖z‖ ^ Q))
    calc
      (β - 1) * (‖z‖ ^ Q) ^ 2 ≤
          (β ^ Q * (‖z‖ ^ Q) ^ 2) *
            ‖conjugateCoordinate z u - conjugateCoordinate z v‖ ^ 2 := by
              nlinarith only [h4]
      _ = _ := by rw [hpow, one_mul]
  have hs := Real.sq_sqrt ha.le
  have hnonneg : 0 ≤ Real.sqrt (β - 1) * ‖z‖ ^ Q := by positivity
  have hsquare : (Real.sqrt (β - 1) * ‖z‖ ^ Q) ^ 2 =
      (β - 1) * (‖z‖ ^ Q) ^ 2 := by rw [mul_pow, hs]
  nlinarith [norm_nonneg (conjugateCoordinate z u - conjugateCoordinate z v)]

end D5.S0.Tower.Tribonacci.Separation
