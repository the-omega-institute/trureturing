/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDenominator
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDenominator
   mirror-E: none(waiver:column-mode-denominator-pairing)
   anchors: [mathlib/module/Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots]
   utility: none
   digest: Fixed-root mixed confluence and Lucas pairing identify the column denominator. -/

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnBranches

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDenominator

open Polynomial Finset CiglerMotzkinHankelDefs CiglerMotzkinColumnDefs
open CiglerMotzkinHankelOrthogonal

/-- Reciprocal modes pair to Cigler's signed factors, with the central mode counted once. -/
theorem mode_denominator {K : Type*} [Field K] (phi : ℤ[X] →+* K) (alpha : Kˣ)
    (parameter : phi X = (alpha : K) + ((alpha⁻¹ : Kˣ) : K)) (k m : ℕ) :
    let eps : K := (-1) ^ (k + 1).choose 2
    let Q := Polynomial.map phi (columnDenominator k m)
    Q = (∏ j ∈ range (m + 1),
      (1 - C (eps * ((alpha ^ ((k + 1 : ℕ) * ((m : ℤ) - 2 * j)) : Kˣ) : K)) *
        X ^ (k + 1)) ^ (1 + j * (m - j))) ∧
    Q.natDegree = (k + 1) * (m + 1 + (m + 1).choose 3) ∧ Q.leadingCoeff ≠ 0 := by
  classical
  dsimp only
  let eps : K := (-1) ^ (k + 1).choose 2
  have split : Polynomial.map phi (columnDenominator k m) =
      ∏ j ∈ range (m + 1),
        (1 - C (eps * ((alpha ^ ((k + 1 : ℕ) * ((m : ℤ) - 2 * j)) : Kˣ) : K)) *
          X ^ (k + 1)) ^ (1 + j * (m - j)) := by
    have lucas_formula (r : ℕ) : phi (specialize (lucas r)) =
        ((alpha ^ r : Kˣ) : K) + ((alpha⁻¹ ^ r : Kˣ) : K) := by
      induction r using Nat.twoStepInduction with
      | zero => norm_num [lucas, map_ofNat]
      | one => simpa [lucas, specialize, tVar] using parameter
      | more r previous current =>
        rw [lucas, map_sub, map_mul, map_sub, map_mul,
          show specialize tVar = (X : ℤ[X]) by simp [specialize, tVar],
          parameter, current, previous]
        simp only [pow_succ, Units.val_mul]
        have inverse : (alpha : K) * ((alpha⁻¹ : Kˣ) : K) = 1 := by simp
        linear_combination ((alpha ^ r : Kˣ) + (alpha⁻¹ ^ r : Kˣ)) * inverse
    let f (j : ℕ) : K[X] :=
      (1 - C (eps * ((alpha ^ ((k + 1 : ℕ) * ((m : ℤ) - 2 * j)) : Kˣ) : K)) *
        X ^ (k + 1)) ^ (1 + j * (m - j))
    have pair (j : ℕ) (hj : j < m / 2 + 1) :
        Polynomial.map phi (columnFactor k ((k + 1) * (m - 2 * j)) ^ (1 + j * (m - j))) =
          f j * (if m = 2 * j then 1 else f (m - j)) := by
      have bounded : 2 * j ≤ m := by omega
      rw [Polynomial.map_pow]
      by_cases central : m = 2 * j
      · simp [central, columnFactor, f, eps, Nat.cast_mul]
      · have positive : m - 2 * j ≠ 0 := by omega
        have argument_ne : (k + 1) * (m - 2 * j) ≠ 0 :=
          Nat.mul_ne_zero (by omega) positive
        rw [columnFactor, if_neg argument_ne]
        simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one,
          Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
        rw [map_mul, map_pow, map_neg, map_one, lucas_formula]
        have exponent : (alpha ^ ((k + 1 : ℕ) * ((m : ℤ) - 2 * j)) : Kˣ) =
            alpha ^ ((k + 1) * (m - 2 * j)) := by
          rw [← zpow_natCast]
          congr 1
          rw [Nat.cast_mul, Nat.cast_sub bounded]
          push_cast
          ring
        have opposite :
            (alpha ^ ((k + 1 : ℕ) * ((m : ℤ) - 2 * ((m - j : ℕ) : ℤ))) : Kˣ) =
              alpha⁻¹ ^ ((k + 1) * (m - 2 * j)) := by
          rw [inv_pow, ← zpow_natCast, ← zpow_neg]
          congr 1
          rw [Nat.cast_mul, Nat.cast_sub bounded, Nat.cast_sub (by omega : j ≤ m)]
          push_cast
          ring
        have weights : 1 + (m - j) * (m - (m - j)) = 1 + j * (m - j) := by
          rw [Nat.sub_sub_self (by omega), Nat.mul_comm]
        dsimp only [f]; rw [if_neg central, exponent, opposite, weights, ← mul_pow]
        congr 1
        have inverse : ((alpha ^ ((k + 1) * (m - 2 * j)) : Kˣ) : K) *
            ((alpha⁻¹ ^ ((k + 1) * (m - 2 * j)) : Kˣ) : K) = 1 := by
          rw [← Units.val_mul, ← mul_pow]
          simp
        have eps_sq : eps * eps = 1 := by
          dsimp only [eps]
          rw [← pow_add, ← two_mul, pow_mul]
          simp
        change 1 - C (eps * (((alpha ^ ((k + 1) * (m - 2 * j)) : Kˣ) : K) +
          ((alpha⁻¹ ^ ((k + 1) * (m - 2 * j)) : Kˣ) : K))) * X ^ (k + 1) +
            X ^ (2 * (k + 1)) = _
        rw [mul_add, C_add]
        have constant_product :
            C (eps * ((alpha ^ ((k + 1) * (m - 2 * j)) : Kˣ) : K)) *
              C (eps * ((alpha⁻¹ ^ ((k + 1) * (m - 2 * j)) : Kˣ) : K)) = (1 : K[X]) := by
          rw [← C_mul]
          have product : (eps * ((alpha ^ ((k + 1) * (m - 2 * j)) : Kˣ) : K)) *
              (eps * ((alpha⁻¹ ^ ((k + 1) * (m - 2 * j)) : Kˣ) : K)) = 1 := by
            calc
              _ = (eps * eps) * (((alpha ^ ((k + 1) * (m - 2 * j)) : Kˣ) : K) *
                ((alpha⁻¹ ^ ((k + 1) * (m - 2 * j)) : Kˣ) : K)) := by ring
              _ = 1 := by rw [eps_sq, inverse, mul_one]
          rw [product, C_1]
        rw [show (X : K[X]) ^ (2 * (k + 1)) = (X ^ (k + 1)) ^ 2 by
          rw [show 2 * (k + 1) = (k + 1) * 2 by omega, pow_mul]]
        linear_combination -(X ^ (k + 1)) ^ 2 * constant_product
    let lo := (m + 1) / 2
    let hi := m / 2 + 1
    have partition : hi + lo = m + 1 := by dsimp [hi, lo]; omega
    have second : (∏ j ∈ range hi, if m = 2 * j then 1 else f (m - j)) =
        ∏ j ∈ range lo, f (m - j) := by
      symm
      apply prod_subset_one_on_sdiff (range_mono (by dsimp [lo, hi]; omega))
      · intro j hj
        simp only [mem_sdiff, mem_range] at hj
        rw [if_pos (by dsimp [lo, hi] at hj; omega)]
      · intro j hj
        rw [if_neg (by simp only [mem_range] at hj; dsimp [lo] at hj; omega)]
    rw [columnDenominator, Polynomial.map_prod]
    have paired : (∏ j ∈ range (m / 2 + 1),
        Polynomial.map phi (columnFactor k ((k + 1) * (m - 2 * j)) ^ (1 + j * (m - j)))) =
          ∏ j ∈ range hi, f j * (if m = 2 * j then 1 else f (m - j)) := by
      apply prod_congr rfl
      intro j hj; exact pair j (mem_range.mp hj)
    rw [paired]; rw [prod_mul_distrib, second]
    change (∏ j ∈ range hi, f j) * (∏ j ∈ range lo, f (m - j)) =
      ∏ j ∈ range (m + 1), f j
    conv_rhs => rw [← partition, prod_range_add]
    congr 1
    rw [← prod_range_reflect (fun j => f (hi + j)) lo]; apply prod_congr rfl
    intro j hj
    congr 1
    simp only [mem_range] at hj
    omega
  have total (n : ℕ) : (∑ j ∈ range (n + 1), j * (n - j)) = (n + 1).choose 3 := by
    induction n with
    | zero => simpa using (Nat.choose_eq_zero_of_lt (show 1 < 3 by omega)).symm
    | succ n ih =>
      rw [sum_range_succ]; simp only [Nat.sub_self, mul_zero, add_zero]
      have summand (j : ℕ) (hj : j ∈ range (n + 1)) :
          j * (n + 1 - j) = j * (n - j) + j := by
        have hjn : j ≤ n := by simp only [mem_range] at hj; omega
        rw [show n + 1 - j = n - j + 1 by omega]; ring
      rw [sum_congr rfl summand, sum_add_distrib, ih, sum_range_id]
      have choose := Nat.choose_succ_succ (n + 1) 2
      rw [Nat.choose_two_right] at choose
      change (n + 1 + 1).choose 3 = (n + 1) * n / 2 + (n + 1).choose 3 at choose
      simp only [Nat.add_sub_cancel] at ⊢
      omega
  have linear_degree (w : Kˣ) : (1 - C (w : K) * X ^ (k + 1)).natDegree = k + 1 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro h hh
      simp [coeff_sub, coeff_one, coeff_X_pow, show h ≠ 0 by omega,
        show h ≠ k + 1 by omega]
    · simp [coeff_sub, coeff_one, coeff_X_pow, Units.ne_zero]
  have linear_nonzero (w : Kˣ) : (1 - C (w : K) * X ^ (k + 1)) ≠ 0 := by
    intro h
    have equality := congrArg (fun P : K[X] => P.coeff 0) h
    simp [coeff_sub, coeff_one] at equality
  let rho (j : ℕ) : Kˣ := Units.mk0
    (eps * ((alpha ^ ((k + 1 : ℕ) * ((m : ℤ) - 2 * j)) : Kˣ) : K))
    (mul_ne_zero (by dsimp [eps]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Units.ne_zero _))
  refine ⟨split, ?_, ?_⟩
  · rw [split]
    change (∏ j ∈ range (m + 1),
      (1 - C (rho j : K) * X ^ (k + 1)) ^ (1 + j * (m - j))).natDegree = _
    rw [natDegree_prod _ _ (fun j _ => pow_ne_zero _ (linear_nonzero _))]
    simp_rw [natDegree_pow, linear_degree]
    rw [← sum_mul, sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one, total]
    ring
  · rw [split]
    apply leadingCoeff_ne_zero.mpr
    apply prod_ne_zero_iff.mpr
    intro j _
    exact pow_ne_zero _ (linear_nonzero (rho j))

/-- The reciprocal pairs of a primitive root produce all fixed Chebyshev nodes. -/
theorem fixed_roots {K : Type*} [Field K] [CharZero K]
    (phi : ℤ[X] →+* K) (k : ℕ) (zeta : K) (primitive : IsPrimitiveRoot zeta (2 * (k + 1))) :
    let r (i : Fin k) := phi X + zeta ^ (i.val + 1) + (zeta ^ (i.val + 1))⁻¹
    Function.Injective r ∧
    (∀ i : Fin k, (zeta ^ (i.val + 1)) ^ (k + 1) = (-1 : K) ^ (i.val + 1)) ∧
    (∀ i : Fin k, ∀ n : ℕ,
      (zeta ^ (i.val + 1) - (zeta ^ (i.val + 1))⁻¹) *
        (Polynomial.map (phi.comp specialize.toRingHom) (orthogonal n)).eval (r i) =
          (zeta ^ (i.val + 1)) ^ (n + 1) - ((zeta ^ (i.val + 1))⁻¹) ^ (n + 1)) ∧
    Polynomial.map (phi.comp specialize.toRingHom) (orthogonal k) =
      ∏ i : Fin k, (X - C (r i)) ∧
    (∀ m : ℕ, ∀ f : Fin (m + k) → K[X], ∀ c : Fin m → K,
      let A := Matrix.of fun i j : Fin (m + k) =>
        if hj : j.val < m then PowerSeries.rescale (c ⟨j.val, hj⟩) (f i)
        else PowerSeries.C ((f i).eval (r ⟨j.val - m, by omega⟩))
      let g := X ^ m * Polynomial.map (phi.comp specialize.toRingHom) (orthogonal k)
      PowerSeries.coeff (m.choose 2) A.det =
        (Matrix.vandermonde c).det * (Matrix.vandermonde r).det * (∏ i, r i ^ m) *
          (Matrix.of fun i j : Fin (m + k) => ((f i) %ₘ g).coeff j.val).det) := by
  classical
  dsimp only
  let psi : Base →+* K := phi.comp specialize.toRingHom
  let r (i : Fin k) := phi X + zeta ^ (i.val + 1) + (zeta ^ (i.val + 1))⁻¹
  have t_image : psi tVar = phi X := by simp [psi, specialize, tVar]
  have s_image : psi sVar = phi X := by simp [psi, specialize, sVar]
  have zeta_ne : zeta ≠ 0 := primitive.ne_zero (by omega)
  have half : zeta ^ (k + 1) = -1 := by
    have square : (zeta ^ (k + 1)) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm (k + 1) 2, primitive.pow_eq_one]
    have different : zeta ^ (k + 1) ≠ 1 :=
      primitive.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    exact (sq_eq_one_iff.mp square).resolve_left different
  have separated (i : Fin k) : zeta ^ (i.val + 1) - (zeta ^ (i.val + 1))⁻¹ ≠ 0 := by
    intro equal
    have same := sub_eq_zero.mp equal
    have square : (zeta ^ (i.val + 1)) ^ 2 = 1 := by
      calc
        (zeta ^ (i.val + 1)) ^ 2 =
            zeta ^ (i.val + 1) * zeta ^ (i.val + 1) := pow_two _
        _ = zeta ^ (i.val + 1) * (zeta ^ (i.val + 1))⁻¹ := congrArg (_ * ·) same
        _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ zeta_ne)
    have impossible : zeta ^ (2 * (i.val + 1)) = 1 := by
      simpa [pow_mul, Nat.mul_comm] using square
    exact primitive.pow_ne_one_of_pos_of_lt (by omega) (by omega) impossible
  have injective : Function.Injective r := by
    intro i j equal
    let u := zeta ^ (i.val + 1)
    let v := zeta ^ (j.val + 1)
    have u_ne : u ≠ 0 := pow_ne_zero _ zeta_ne
    have v_ne : v ≠ 0 := pow_ne_zero _ zeta_ne
    have reciprocal : u + u⁻¹ = v + v⁻¹ := by
      dsimp only [r] at equal
      dsimp only [u, v]
      linear_combination equal
    have factor : (u - v) * (u * v - 1) = 0 := by
      have multiplied := congrArg (fun x : K => x * (u * v)) reciprocal
      field_simp at multiplied
      linear_combination multiplied
    rcases mul_eq_zero.mp factor with direct | reversed
    · apply Fin.ext
      have indices := primitive.pow_inj (by omega : i.val + 1 < 2 * (k + 1))
        (by omega : j.val + 1 < 2 * (k + 1)) (sub_eq_zero.mp direct)
      omega
    · have impossible : zeta ^ (i.val + 1 + (j.val + 1)) = 1 := by
        rw [pow_add]
        exact sub_eq_zero.mp reversed
      exact False.elim (primitive.pow_ne_one_of_pos_of_lt (by omega) (by omega) impossible)
  have evaluated (w : K) (nonzero : w ≠ 0) : ∀ n : ℕ,
      (w - w⁻¹) * (Polynomial.map psi (orthogonal n)).eval (phi X + w + w⁻¹) =
        w ^ (n + 1) - (w⁻¹) ^ (n + 1) := by
    apply Nat.twoStepInduction
    · simp [orthogonal]
    · simp only [orthogonal, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        eval_sub, eval_X, eval_C, s_image, Nat.reduceAdd, pow_two]
      ring
    · intro n previous current
      simp only [orthogonal, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
        Polynomial.map_C, eval_sub, eval_mul, eval_X, eval_C, t_image]
      have location : phi X + w + w⁻¹ - phi X = w + w⁻¹ := by ring
      rw [location]
      have recurrence :
          w ^ (n + 2 + 1) - (w⁻¹) ^ (n + 2 + 1) =
            (w + w⁻¹) * (w ^ (n + 1 + 1) - (w⁻¹) ^ (n + 1 + 1)) -
              (w ^ (n + 1) - (w⁻¹) ^ (n + 1)) := by
        simp only [pow_succ]
        have inverse : w * w⁻¹ = 1 := mul_inv_cancel₀ nonzero
        linear_combination -(w ^ (n + 1) - (w⁻¹) ^ (n + 1)) * inverse
      rw [recurrence, ← current, ← previous]
      ring
  have roots (i : Fin k) : (Polynomial.map psi (orthogonal k)).eval (r i) = 0 := by
    have identity := evaluated (zeta ^ (i.val + 1)) (pow_ne_zero _ zeta_ne) k
    have power : (zeta ^ (i.val + 1)) ^ (k + 1) = (-1 : K) ^ (i.val + 1) := by
      rw [← pow_mul, Nat.mul_comm (i.val + 1) (k + 1), pow_mul, half]
    rw [power, inv_pow, power] at identity
    have inverse : (((-1 : K) ^ (i.val + 1))⁻¹) = (-1 : K) ^ (i.val + 1) := by
      rw [← inv_pow, inv_neg, inv_one]
    rw [inverse, sub_self] at identity
    exact (mul_eq_zero.mp identity).resolve_left (separated i)
  have p_monic : (Polynomial.map psi (orthogonal k)).Monic :=
    (orthogonal_basis k).1.monic.map psi
  have divisor : (∏ i : Fin k, (X - C (r i))) ∣ Polynomial.map psi (orthogonal k) := by
    apply Fintype.prod_dvd_of_coprime
    · intro i j different
      apply isCoprime_X_sub_C_of_isUnit_sub
      exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (injective.ne different))
    · intro i
      exact (dvd_iff_isRoot).mpr (roots i)
  refine ⟨injective, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← pow_mul, Nat.mul_comm (i.val + 1) (k + 1), pow_mul, half]
  · intro i n
    exact evaluated (zeta ^ (i.val + 1)) (pow_ne_zero _ zeta_ne) n
  · apply eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C r univ) p_monic divisor
    rw [(orthogonal_basis k).1.monic.natDegree_map, (orthogonal_basis k).1.natDegree_eq,
      natDegree_finsetProd_X_sub_C_eq_card, card_univ, Fintype.card_fin]
  · intro m f c
    let p := Polynomial.map psi (orthogonal k)
    let g : K[X] := X ^ m * p
    have p_degree : p.IsMonicOfDegree k :=
      ⟨by rw [(orthogonal_basis k).1.monic.natDegree_map,
          (orthogonal_basis k).1.natDegree_eq], p_monic⟩
    have g_degree : g.IsMonicOfDegree (m + k) :=
      by simpa [g] using ((isMonicOfDegree_X (R := K)).pow m).mul p_degree
    let Cmat : Matrix (Fin (m + k)) (Fin (m + k)) K :=
      Matrix.of fun i j => ((f i) %ₘ g).coeff j.val
    let B : Matrix (Fin (m + k)) (Fin (m + k)) K := Matrix.of fun i j =>
      if hj : j.val < m then (if i.val = j.val then 1 else 0)
      else r ⟨j.val - m, by omega⟩ ^ i.val
    let J : Matrix (Fin (m + k)) (Fin (m + k)) K := Matrix.of fun i j =>
      if hj : j.val < m then (f i).coeff j.val
      else (f i).eval (r ⟨j.val - m, by omega⟩)
    have reconstruction (i : Fin (m + k)) :
        (f i) %ₘ g = ∑ a : Fin (m + k), C (Cmat i a) * X ^ a.val := by
      have below : ((f i) %ₘ g).degree < m + k := by
        simpa [degree_eq_natDegree g_degree.monic.ne_zero, g_degree.natDegree_eq] using
          degree_modByMonic_lt (f i) g_degree.monic
      change (f i) %ₘ g = ∑ a : Fin (m + k), C (((f i) %ₘ g).coeff a.val) * X ^ a.val
      have finite := Polynomial.sum_fin (R := K) (S := K[X])
        (n := m + k) (p := (f i) %ₘ g) (fun a v => C v * X ^ a) (by simp) below
      exact ((f i) %ₘ g).sum_C_mul_X_pow_eq.symm.trans finite.symm
    have product : Cmat * B = J := by
      ext i j
      by_cases hj : j.val < m
      · have entry : (Cmat * B) i j = Cmat i j := by
          simp only [Matrix.mul_apply, B, Matrix.of_apply, dif_pos hj]
          rw [sum_eq_single j]
          · simp
          · intro a _ different
            have unequal : a.val ≠ j.val := fun equal => different (Fin.ext equal)
            simp [unequal]
          · simp
        rw [entry]
        change ((f i) %ₘ g).coeff j.val = _
        have division := congrArg (fun q : K[X] => q.coeff j.val)
          (modByMonic_add_div (f i) g)
        have vanished : (g * ((f i) /ₘ g)).coeff j.val = 0 := by
          dsimp only [g]
          rw [mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
        rw [coeff_add, vanished, add_zero] at division
        simpa only [J, Matrix.of_apply, dif_pos hj] using division
      · have evaluated_remainder := congrArg (fun q : K[X] =>
          q.eval (r ⟨j.val - m, by omega⟩)) (reconstruction i)
        simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] at evaluated_remainder
        have remainder_value : ((f i) %ₘ g).eval (r ⟨j.val - m, by omega⟩) =
            (f i).eval (r ⟨j.val - m, by omega⟩) := by
          rw [modByMonic_eq_sub_mul_div, eval_sub, eval_mul]
          have root : g.eval (r ⟨j.val - m, by omega⟩) = 0 := by
            simp only [g, eval_mul, p, roots, mul_zero]
          rw [root, zero_mul, sub_zero]
        simp only [Matrix.mul_apply, B, J, Matrix.of_apply, dif_neg hj]
        exact (evaluated_remainder.symm.trans remainder_value)
    let top : Matrix (Fin m) (Fin k) K := Matrix.of fun i j => r j ^ i.val
    let bottom : Matrix (Fin k) (Fin k) K :=
      Matrix.of fun i j => r j ^ m * (Matrix.vandermonde r).transpose i j
    let index : Fin m ⊕ Fin k ≃ Fin (m + k) := finSumFinEquiv
    have block : B.submatrix index index = Matrix.fromBlocks 1 top 0 bottom := by
      ext i j
      cases i with
      | inl i =>
        cases j with
        | inl j =>
          simp [B, index, Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.one_apply,
            Fin.ext_iff]
        | inr j => simp [B, index, top, Matrix.submatrix_apply, Matrix.fromBlocks]
      | inr i =>
        cases j with
        | inl j =>
          simp [B, index, Matrix.submatrix_apply, Matrix.fromBlocks,
            show m + i.val ≠ j.val by omega]
        | inr j =>
          simp [B, index, bottom, Matrix.submatrix_apply, Matrix.fromBlocks,
            Matrix.transpose_apply, Matrix.vandermonde_apply, pow_add]
    have B_det : B.det = (∏ i, r i ^ m) * (Matrix.vandermonde r).det := by
      rw [← Matrix.det_submatrix_equiv_self index B, block,
        Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
      rw [show bottom = Matrix.of (fun i j : Fin k =>
        r j ^ m * (Matrix.vandermonde r).transpose i j) from rfl,
        Matrix.det_mul_row, Matrix.det_transpose]
    have J_det : J.det = (Matrix.vandermonde r).det * (∏ i, r i ^ m) * Cmat.det := by
      rw [← product, Matrix.det_mul, B_det]
      ring
    have extraction := (CiglerMotzkinColumnDeterminant.mixed_confluence m k
      (fun i => (f i : PowerSeries K))
      (fun i j => (f i).eval (r j)) c).2
    simp only [Polynomial.coeff_coe] at extraction
    change _ = (Matrix.vandermonde c).det * J.det at extraction
    rw [J_det] at extraction
    convert extraction using 1; dsimp only [Cmat, g, p]; ring

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDenominator
