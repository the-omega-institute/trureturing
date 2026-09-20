/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema]
   utility: none
   digest: Every positive crown has a log-concave full geometric face vector, including the empty face. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeChebyshev
import D5.S3.Analytic.RealRootedCoefficientNewton
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open Polynomial Polynomial.Chebyshev
open D5.S3.Analytic.RealRootedCoefficientNewton

/-- Conjecture 3.7 for the actual geometric crown order-polytope face vector:
the empty face and the whole polytope are included, for every positive size. -/
theorem crownGeometricFVector_log_concave (n : ℕ) (hn : 0 < n)
    (k : ℕ) (hk : 0 < k) (hkn : k < 2*n+1) :
    crownGeometricFVector n ⟨k-1, by omega⟩ *
      crownGeometricFVector n ⟨k+1, by omega⟩ ≤
        crownGeometricFVector n ⟨k, by omega⟩ ^ 2 := by
  classical
  have scalar_comp_identity (n : ℕ) : crownScalarPolynomial n =
      (1 + X) ^ (n + 1) * (crownAuxiliaryPolynomial n).comp (1 + X) := by
    classical
    unfold crownScalarPolynomial crownAuxiliaryPolynomial
    rw [sum_comp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    rw [mul_comp, C_comp, pow_comp, X_comp]
    calc
      C (crownScalarWeight n m) * (1 + X) ^ (n + m) =
          C (crownScalarWeight n m) * ((1 + X) ^ (n + 1) * (1 + X) ^ (m - 1)) := by
        rw [← pow_add, show n + 1 + (m - 1) = n + m by omega]
      _ = _ := by ring

  let crownScalarReal (n : ℕ) : ℝ[X] :=
    (crownScalarPolynomial n).map (algebraMap ℚ ℝ)

  have crownScalarReal_chebyshev (n : ℕ) :
      crownScalarReal n =
        2 * (1 + X) ^ n *
          ((Chebyshev.T ℝ (n : ℤ)).comp ((X + 3) * C (1 / 2)) - 1) := by
    dsimp [crownScalarReal]
    have hq := congrArg (fun p : ℚ[X] => p.comp (1 + X))
      (crownAuxiliaryPolynomial_chebyshev n)
    simp only [mul_comp, X_comp, ofNat_comp, sub_comp, one_comp, comp_assoc,
      add_comp, C_comp] at hq
    norm_num only [Nat.cast_ofNat] at hq
    have hs : crownScalarPolynomial n =
        2 * (1 + X) ^ n *
          ((T ℚ (n : ℤ)).comp ((X + 3) * C (1 / 2)) - 1) := by
      rw [scalar_comp_identity, pow_succ, mul_assoc, hq]
      have he : (1 + X + 2 : ℚ[X]) = X + 3 := by ring
      rw [he]
      ring
    rw [hs]
    norm_num [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_comp, Chebyshev.map_T]

  have chebyshev_pell_identity (m : ℕ) (hm : 1 ≤ m) :
      (T ℝ (m : ℤ)) ^ 2 - 1 = (X ^ 2 - 1) * (U ℝ ((m : ℤ) - 1)) ^ 2 := by
    induction m, hm using Nat.le_induction with
    | base =>
        simp [T_one, U_zero]
    | succ m hm ih =>
        have ht := T_eq_X_mul_T_sub_pol_U (R := ℝ) ((m : ℤ) - 1)
        have hu := U_eq_X_mul_U_add_T (R := ℝ) ((m : ℤ) - 1)
        have h1 : (m : ℤ) - 1 + 2 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
        have h2 : (m : ℤ) - 1 + 1 = (m : ℤ) := by ring
        have h3 : ((m : ℤ) - 1 + 1 : ℤ) = (m : ℤ) := by ring
        rw [h1, h2] at ht
        rw [h3] at hu
        have ht' : T ℝ ((m + 1 : ℕ) : ℤ) =
            X * T ℝ (m : ℤ) + (X ^ 2 - 1) * U ℝ ((m : ℤ) - 1) := by
          convert ht using 1 <;> ring
        have hu' : U ℝ (m : ℤ) = X * U ℝ ((m : ℤ) - 1) + T ℝ (m : ℤ) := by
          simpa [sub_eq_add_neg] using hu
        have hmcast : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
        rw [hmcast, ht', hu']
        linear_combination ih
  have chebyshev_odd_factorization (m : ℕ) :
      T ℝ ((2*m+1 : ℕ) : ℤ) - 1 =
        (X - 1) * (U ℝ (m : ℤ) + U ℝ ((m : ℤ) - 1)) ^ 2 := by
    by_cases hzero : m = 0
    · subst m
      simp [T_one, U_zero, U_neg_one]
    · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hzero
      have hs := chebyshev_pell_identity m hm
      have ht := T_mul_T (R := ℝ) ((m+1 : ℕ) : ℤ) (m : ℤ)
      have hu := U_eq_X_mul_U_add_T (R := ℝ) ((m : ℤ) - 1)
      have ht1 : T ℝ ((2*m+1 : ℕ) : ℤ) =
          2 * T ℝ ((m+1 : ℕ) : ℤ) * T ℝ (m : ℤ) - X := by
        rw [show ((m+1 : ℕ) : ℤ) + (m : ℤ) = ((2*m+1 : ℕ) : ℤ) by omega,
          show ((m+1 : ℕ) : ℤ) - (m : ℤ) = 1 by omega, T_one] at ht
        linear_combination -ht
      have hu1 : U ℝ (m : ℤ) = X * U ℝ ((m : ℤ) - 1) + T ℝ (m : ℤ) := by
        have h3 : (m : ℤ) - 1 + 1 = (m : ℤ) := by ring
        rw [h3] at hu
        exact hu
      have ht2 : T ℝ ((m+1 : ℕ) : ℤ) =
          X * T ℝ (m : ℤ) + (X^2-1) * U ℝ ((m : ℤ)-1) := by
        have h := T_eq_X_mul_T_sub_pol_U (R := ℝ) ((m : ℤ)-1)
        have h1 : (m : ℤ)-1+2=((m+1:ℕ):ℤ) := by push_cast; ring
        have h2 : (m : ℤ)-1+1=(m:ℤ) := by ring
        rw [h1,h2] at h
        convert h using 1 <;> ring
      rw [ht1, ht2, hu1]
      linear_combination (X + 1) * hs
  have chebyshev_even_factorization (m : ℕ) :
      T ℝ ((2*m : ℕ) : ℤ) - 1 =
        2 * (X ^ 2 - 1) * (U ℝ ((m : ℤ) - 1)) ^ 2 := by
    have ht := T_mul_T (R := ℝ) (m : ℤ) (m : ℤ)
    by_cases hm : m = 0
    · subst m; simp [T_zero, U_neg_one]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hs := chebyshev_pell_identity m hm1
      have hzero : (m : ℤ) - (m : ℤ) = 0 := by ring
      rw [hzero, T_zero] at ht
      have hadd : (m : ℤ) + (m : ℤ) = ((2*m : ℕ) : ℤ) := by push_cast; ring
      rw [hadd] at ht
      have ht' : T ℝ ((2*m : ℕ) : ℤ) = 2 * T ℝ (m : ℤ)^2 - 1 := by
        linear_combination -ht
      rw [ht']
      linear_combination 2 * hs
  have chebyshev_U_doubling : ∀ m : ℕ,
      (U ℝ (2*(m:ℤ)) = (U ℝ (m:ℤ))^2 - (U ℝ ((m:ℤ)-1))^2) ∧
      (U ℝ (2*(m:ℤ)+1) = U ℝ (m:ℤ) * (U ℝ ((m:ℤ)+1) - U ℝ ((m:ℤ)-1))) := by
    intro m
    induction m with
    | zero => constructor <;> simp [U_zero, U_one, U_neg_one]
    | succ m ih =>
        rcases ih with ⟨he, ho⟩
        have h2e := U_add_two (R := ℝ) (2*(m:ℤ))
        have h2o := U_add_two (R := ℝ) (2*(m:ℤ)+1)
        have hm := U_add_two (R := ℝ) (m:ℤ)
        have hm1 := U_add_two (R := ℝ) ((m:ℤ)-1)
        have hm2 := U_add_two (R := ℝ) ((m:ℤ)+1)
        have he' : U ℝ (2*((m:ℤ)+1)) =
            2*X*U ℝ (2*(m:ℤ)+1) - U ℝ (2*(m:ℤ)) := by
          convert h2e using 1 <;> ring
        have ho' : U ℝ (2*((m:ℤ)+1)+1) =
            2*X*U ℝ (2*((m:ℤ)+1)) - U ℝ (2*(m:ℤ)+1) := by
          convert h2o using 1 <;> ring
        have hm' : U ℝ ((m:ℤ)+2) = 2*X*U ℝ ((m:ℤ)+1) - U ℝ (m:ℤ) := by
          exact hm
        have hm1' : U ℝ ((m:ℤ)+1) = 2*X*U ℝ (m:ℤ) - U ℝ ((m:ℤ)-1) := by
          convert hm1 using 1 <;> ring
        have hm2' : U ℝ ((m:ℤ)+3) = 2*X*U ℝ ((m:ℤ)+2) - U ℝ ((m:ℤ)+1) := by
          convert hm2 using 1 <;> ring
        have he_next : U ℝ (2*((m:ℤ)+1)) =
            (U ℝ ((m:ℤ)+1))^2 - (U ℝ (m:ℤ))^2 := by
          rw [he', ho, he]
          rw [hm1']
          ring
        have ho_next : U ℝ (2*((m:ℤ)+1)+1) =
            U ℝ ((m:ℤ)+1) *
              (U ℝ ((m:ℤ)+2) - U ℝ ((m:ℤ))) := by
          rw [ho', he_next, ho]
          rw [hm', hm1']
          ring
        have hm'' : U ℝ ((m:ℤ)+1+1) = 2*X*U ℝ ((m:ℤ)+1) - U ℝ (m:ℤ) := by
          convert hm' using 1 <;> congr 1 <;> ring
        constructor
        · simpa [Nat.cast_add, Nat.cast_one] using he_next
        · simpa [Nat.cast_add, Nat.cast_one, hm''] using ho_next

  have scalar_splits (n : ℕ) : (crownScalarReal n).Splits := by
    have hU (m : ℕ) : (U ℝ (m : ℤ)).Splits := by
      rw [splits_iff_card_roots, roots_U_real, ← Finset.card_def,
        Finset.card_image_of_injOn]
      · rw [Finset.card_range, natDegree_eq_of_degree_eq_some (degree_U_natCast ℝ m)]
      · exact (Finset.range m).nodup_map_iff_injOn.mp (roots_U_real_nodup m)
    have hV (m : ℕ) : (U ℝ (m : ℤ) + U ℝ ((m : ℤ) - 1)).Splits := by
      apply (hU (2*m)).of_dvd
      · exact U_ne_zero ℝ _ (by omega)
      · refine ⟨U ℝ (m : ℤ) - U ℝ ((m : ℤ) - 1), ?_⟩
        have he := (chebyshev_U_doubling m).1
        push_cast
        rw [he]
        ring
    have hT : (T ℝ (n : ℤ) - 1).Splits := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · have he : n = 2*m := by omega
        rw [he, chebyshev_even_factorization]
        have hUm : (U ℝ ((m : ℤ)-1)).Splits := by
          cases m with
          | zero => simp [U_neg_one]
          | succ m => simpa using hU m
        have hlin : (X^2-1 : ℝ[X]).Splits := by
          have heq : (X^2-1 : ℝ[X]) = (X-Polynomial.C 1)*(X+Polynomial.C 1) := by simp; ring
          rw [heq]
          exact (Splits.X_sub_C 1).mul (Splits.X_add_C 1)
        exact ((Splits.C (2 : ℝ)).mul hlin).mul (hUm.pow 2)
      · have he : n = 2*m+1 := by omega
        rw [he, chebyshev_odd_factorization]
        have hlin : (X-1 : ℝ[X]).Splits := by simpa using Splits.X_sub_C (1 : ℝ)
        exact hlin.mul ((hV m).pow 2)
    rw [crownScalarReal_chebyshev]
    have hc := hT.comp_of_natDegree_le_one
      (g := (X + 3) * Polynomial.C (1/2)) (by compute_degree)
    simp only [sub_comp, one_comp] at hc
    have hlin : (1 + X : ℝ[X]).Splits := by simpa [add_comm] using Splits.X_add_C (1 : ℝ)
    have htwo : (2 : ℝ[X]).Splits := Splits.of_natDegree_le_one (by norm_num)
    exact (htwo.mul (hlin.pow n)).mul hc
  have scalar_bounds (n : ℕ) (hn : 2 ≤ n) :
      let s := fun k => (crownScalarPolynomial n).coeff k
      (∀ k, 0 ≤ s k) ∧ (n : ℚ)^2 ≤ s 0 ∧ s 0 ≤ s 1 ∧ s 1 ≤ 2*n*s 0 := by
    classical
    dsimp only
    have hw (m : ℕ) : 0 ≤ crownScalarWeight n m := by
      unfold crownScalarWeight
      positivity
    have hcoeff (d : ℕ) : (crownScalarPolynomial n).coeff d =
        ∑ m ∈ Finset.Icc 1 n, crownScalarWeight n m * Nat.choose (n+m) d := by
      simp only [crownScalarPolynomial, finsetSum_coeff, coeff_C_mul, coeff_one_add_X_pow]
    have h0 : (crownScalarPolynomial n).coeff 0 =
        ∑ m ∈ Finset.Icc 1 n, crownScalarWeight n m := by simp [hcoeff]
    have h1 : (crownScalarPolynomial n).coeff 1 =
        ∑ m ∈ Finset.Icc 1 n, crownScalarWeight n m * (n+m : ℕ) := by simp [hcoeff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d
      rw [hcoeff]
      exact Finset.sum_nonneg (fun m _ => mul_nonneg (hw m) (Nat.cast_nonneg _))
    · rw [h0]
      have he : crownScalarWeight n 1 = (n : ℚ)^2 := by
        simp [crownScalarWeight, pow_two]
      rw [← he]
      exact Finset.single_le_sum (fun m _ => hw m) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · rw [h0, h1]
      apply Finset.sum_le_sum
      intro m hm
      have hm1 := (Finset.mem_Icc.mp hm).1
      have hx : (1 : ℚ) ≤ (n+m : ℕ) := by exact_mod_cast (by omega : 1 ≤ n+m)
      nlinarith [hw m]
    · rw [h0, h1, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      have hm2 := (Finset.mem_Icc.mp hm).2
      have hx : ((n+m : ℕ) : ℚ) ≤ 2*n := by exact_mod_cast (by omega : n+m ≤ 2*n)
      nlinarith [hw m]

  have corrected_lc (n : ℕ) (hn : 2 ≤ n)
      (hnew : ∀ k : ℕ, (k+1 : ℚ) * (crownScalarPolynomial n).coeff (k+1)^2 ≥
        (k+2 : ℚ) * (crownScalarPolynomial n).coeff k *
          (crownScalarPolynomial n).coeff (k+2)) :
      (∀ d : ℕ, 1 ≤ d → crownGeometricFaceCount n (d-1) *
        crownGeometricFaceCount n (d+1) ≤ crownGeometricFaceCount n d ^ 2) ∧
      crownGeometricFaceCount n 1 ≤ crownGeometricFaceCount n 0 ^ 2 := by
    let s := fun k => (crownScalarPolynomial n).coeff k
    obtain ⟨hpos, h0, h01, h10⟩ := scalar_bounds n hn
    change (∀ k, 0 ≤ s k) at hpos
    change (n : ℚ)^2 ≤ s 0 at h0
    change s 0 ≤ s 1 at h01
    change s 1 ≤ 2*n*s 0 at h10
    have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
    have hs0 : 2 ≤ s 0 := by nlinarith
    have hs1 : 2 ≤ s 1 := hs0.trans h01
    have hr0 : s 1 + 1 ≤ (s 0+2)^2 := by
      have hnb : 2*(n : ℚ) ≤ s 0 := by nlinarith
      nlinarith [mul_nonneg (hpos 0) (sub_nonneg.mpr hnb)]
    have hr1 : (s 0+2)*s 2 ≤ (s 1+1)^2 := by
      have h := hnew 0
      change (0+1 : ℚ)*(s 1)^2 ≥ (0+2 : ℚ)*s 0*s 2 at h
      nlinarith [mul_nonneg (sub_nonneg.mpr hs0) (hpos 2)]
    have hr2 : (s 1+1)*s 3 ≤ (s 2)^2 := by
      have h := hnew 1
      change (1+1 : ℚ)*(s 2)^2 ≥ (1+2 : ℚ)*s 1*s 3 at h
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (hpos 3)]
    have hf (d : ℕ) := crownGeometricFaceCount_eq_scalar_coeff n d (by omega : 0<n)
    change ∀ d : ℕ, (crownGeometricFaceCount n d : ℚ) =
      (if d=0 then 2 else 0) + (if d=1 then 1 else 0) + s d at hf
    constructor
    · intro d hd
      apply (Nat.cast_le (α := ℚ)).mp
      push_cast
      rw [hf, hf, hf]
      by_cases hd1 : d=1
      · subst d
        norm_num
        nlinarith [hr1]
      · by_cases hd2 : d=2
        · subst d
          norm_num
          nlinarith [hr2]
        · have hd3 : 3 ≤ d := by omega
          simp only [if_neg (by omega : ¬d-1=0), if_neg (by omega : ¬d-1=1),
            if_neg (by omega : ¬d+1=0), if_neg (by omega : ¬d+1=1),
            if_neg (by omega : ¬d=0), if_neg hd1, zero_add]
          have h := hnew (d-1)
          have he1 : d-1+1=d := by omega
          have he2 : d-1+2=d+1 := by omega
          rw [he1, he2] at h
          have hcast : ((d-1 : ℕ) : ℚ) = d-1 := by rw [Nat.cast_sub (by omega)]; norm_num
          change ((d-1 : ℕ)+1 : ℚ)*s d^2 ≥ ((d-1 : ℕ)+2 : ℚ)*s (d-1)*s (d+1) at h
          rw [hcast] at h
          have hprod := mul_nonneg (hpos (d-1)) (hpos (d+1))
          nlinarith
    · apply (Nat.cast_le (α := ℚ)).mp
      push_cast
      rw [hf, hf]
      norm_num
      nlinarith [hr0]
  by_cases hn1 : n = 1
  · subst n
    have htriangle : crownGeometricFVector 1 = ![1, 3, 3, 1] := by
      funext i
      fin_cases i
      · rfl
      all_goals
        simp only [crownGeometricFVector, Nat.reduceEqDiff, Nat.reduceSub, if_false]
        apply Nat.cast_injective (R := ℚ)
        rw [crownGeometricFaceCount_eq_scalar_coeff _ _ (by norm_num)]
        norm_num [crownScalarPolynomial, crownScalarWeight, coeff_one_add_X_pow]
    rw [htriangle]
    have hki : k = 1 ∨ k = 2 := by omega
    rcases hki with rfl | rfl <;> norm_num
  · have hn2 : 2 ≤ n := by omega
    have hnew (j : ℕ) : (j+1 : ℚ) * (crownScalarPolynomial n).coeff (j+1)^2 ≥
        (j+2 : ℚ) * (crownScalarPolynomial n).coeff j *
          (crownScalarPolynomial n).coeff (j+2) := by
      let p := crownScalarReal n
      have hp : p.Splits := scalar_splits n
      have h :
      (j + 1 : ℝ) * p.coeff (j + 1) ^ 2 ≥
            (j + 2 : ℝ) * p.coeff j * p.coeff (j + 2) := by
        by_cases hdeg : j + 2 ≤ p.natDegree
        · let s := p.roots.map Neg.neg
          let r := p.natDegree - j - 2
          have hcard : s.card = p.natDegree := by
            simp only [s, Multiset.card_map, hp.natDegree_eq_card_roots]
          have hcoeff (i : ℕ) (hi : i ≤ p.natDegree) :
              p.coeff i = p.leadingCoeff * s.esymm (p.natDegree - i) := by
            rw [p.coeff_eq_esymm_roots_of_splits hp hi]
            simp only [s, Multiset.esymm_neg, mul_assoc]
          have h0 : p.natDegree - j = r + 2 := by dsimp [r]; omega
          have h1 : p.natDegree - (j + 1) = r + 1 := by dsimp [r]; omega
          have h2 : p.natDegree - (j + 2) = r := by dsimp [r]; omega
          have hdegree : p.natDegree = r + j + 2 := by dsimp [r]; omega
          have hs := D5.S3.Analytic.RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm s r
          rw [hcard, hdegree] at hs
          push_cast at hs
          have hs' : (r + 2 : ℝ) * (j + 2) * (s.esymm r * s.esymm (r + 2)) ≤
              (r + 1 : ℝ) * (j + 1) * s.esymm (r + 1) ^ 2 := by
            nlinarith only [hs]
          have hlc := mul_le_mul_of_nonneg_left hs' (sq_nonneg p.leadingCoeff)
          rw [hcoeff j (by omega), hcoeff (j+1) (by omega), hcoeff (j+2) hdeg,
            h0, h1, h2]
          have hh : (r + 2 : ℝ) *
                ((j + 2) * (p.leadingCoeff * s.esymm (r + 2)) *
                  (p.leadingCoeff * s.esymm r)) ≤
              (r + 2 : ℝ) *
                ((j + 1) * (p.leadingCoeff * s.esymm (r + 1)) ^ 2) := by
            nlinarith only [hlc, mul_nonneg (show (0 : ℝ) ≤ j+1 by positivity)
              (sq_nonneg (p.leadingCoeff * s.esymm (r+1)))]
          exact (mul_le_mul_iff_right₀ (show (0 : ℝ) < r+2 by positivity)).mp hh
        · rw [p.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j+2)]
          simp only [mul_zero]
          positivity
      dsimp only [p] at h
      simp only [crownScalarReal, coeff_map] at h
      change (j+1 : ℝ) * ((crownScalarPolynomial n).coeff (j+1) : ℝ)^2 ≥
        (j+2 : ℝ) * ((crownScalarPolynomial n).coeff j : ℝ) *
          ((crownScalarPolynomial n).coeff (j+2) : ℝ) at h
      exact_mod_cast h
    obtain ⟨hfaces, hempty⟩ := corrected_lc n hn2 hnew
    by_cases hk1 : k=1
    · subst k
      simpa [crownGeometricFVector] using hempty
    · have hk2 : 2 ≤ k := by omega
      have h := hfaces (k-1) (by omega)
      simpa [crownGeometricFVector, show k-1 ≠ 0 by omega,
        show k+1 ≠ 0 by omega, show k ≠ 0 by omega, Nat.sub_sub,
        Nat.sub_add_cancel (by omega : 1 ≤ k)] using h

#print axioms crownGeometricFVector_log_concave

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
