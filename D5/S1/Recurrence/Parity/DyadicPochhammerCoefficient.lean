/- GID: D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/DyadicPochhammerCoefficient
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The positive-even dyadic step gives the cleared recurrence for the literal rational ascending Pochhammer coefficients. -/

import D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.RingTheory.Polynomial.Pochhammer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient

open Polynomial
open D5.S1.Digit.DyadicRowPolynomialRecurrence (D R R_zero R_odd R_even D_X_mul
  wt wt_zero wt_even wt_odd)
open D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock (T T_one T_odd T_even)
open D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge (support)

private noncomputable def pochhammerSequence : Polynomial.Sequence ℚ where
  elems' := ascPochhammer ℚ
  degree_eq' j := by
    rw [degree_eq_natDegree (monic_ascPochhammer ℚ j).ne_zero, ascPochhammer_natDegree]

/-- The basis of ascending Pochhammer polynomials, indexed by degree. -/
noncomputable def pochhammerBasis : Module.Basis ℕ ℚ (Polynomial ℚ) :=
  pochhammerSequence.basis fun j => by
    change IsUnit (ascPochhammer ℚ j).leadingCoeff
    rw [show (ascPochhammer ℚ j).leadingCoeff = 1 from monic_ascPochhammer ℚ j]
    exact isUnit_one

private theorem basis_apply (j : ℕ) : pochhammerBasis j = ascPochhammer ℚ j :=
  pochhammerSequence.basis_eq_self _ j

theorem coord_basis (i j : ℕ) :
    pochhammerBasis.coord i (ascPochhammer ℚ j) = if j = i then 1 else 0 := by
  rw [← basis_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply]

noncomputable def rationalRow (n : ℕ) : Polynomial ℚ :=
  (R n).map (Int.castRingHom ℚ)

/-- The polynomial whose ascending Pochhammer coordinates encode the literal row. -/
noncomputable def rowPolynomial (n : ℕ) : Polynomial ℚ := X * rationalRow n

noncomputable def difference : Polynomial ℚ →ₗ[ℚ] Polynomial ℚ where
  toFun p := X * (p.comp (X + 1) - p)
  map_add' p q := by
    simp only [add_comp]
    ring
  map_smul' r p := by
    simp only [RingHom.id_apply, smul_comp, smul_eq_C_mul, mul_comp, C_comp]
    ring

private theorem difference_apply (p : Polynomial ℚ) :
    difference p = X * (p.comp (X + 1) - p) := rfl

private theorem map_difference (p : Polynomial ℤ) :
    (D p).map (Int.castRingHom ℚ) = difference (p.map (Int.castRingHom ℚ)) := by
  simp only [D, difference_apply, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_comp, Polynomial.map_add, map_X, Polynomial.map_one]

private theorem rationalRow_zero : rationalRow 0 = X := by
  simp only [rationalRow, R_zero, map_X]

theorem rationalRow_odd (n : ℕ) : rationalRow (2 * n + 1) = X * rationalRow n := by
  simp only [rationalRow, R_odd, Polynomial.map_mul, map_X]

theorem rationalRow_even (n : ℕ) (hn : 0 < n) :
    rationalRow (2 * n) = difference (rationalRow n) := by
  change (R (2 * n)).map (Int.castRingHom ℚ) = difference (rationalRow n)
  rw [show R (2 * n) = D (R n) from R_even n hn, map_difference] <;> rfl

private theorem rowPolynomial_odd (n : ℕ) :
    rowPolynomial (2 * n + 1) = X * rowPolynomial n := by
  simp only [rowPolynomial, rationalRow_odd]

private theorem rowPolynomial_even (n : ℕ) (hn : 0 < n) :
    (X + 1) * rowPolynomial (2 * n) =
      X * (difference (rowPolynomial n) - rowPolynomial n) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) (D_X_mul (R n))
  simp only [map_difference, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_one, map_X] at h
  change difference (rowPolynomial n) =
    rowPolynomial n + (X + 1) * difference (rationalRow n) at h
  rw [h]
  conv_lhs => rw [rowPolynomial, rationalRow_even n hn]
  ring

private theorem X_mul_pochhammer (j : ℕ) :
    X * ascPochhammer ℚ j =
      ascPochhammer ℚ (j + 1) - (j : ℚ) • ascPochhammer ℚ j := by
  rw [ascPochhammer_succ_right, smul_eq_C_mul, C_eq_natCast]
  ring

theorem difference_pochhammer (j : ℕ) :
    difference (ascPochhammer ℚ j) = (j : ℚ) • ascPochhammer ℚ j := by
  rw [difference_apply, mul_sub, ← ascPochhammer_succ_left, X_mul_pochhammer]
  ring

private theorem coord_X_succ (p : Polynomial ℚ) (i : ℕ) :
    pochhammerBasis.coord (i + 1) (X * p) =
      pochhammerBasis.coord i p - ((i + 1 : ℕ) : ℚ) * pochhammerBasis.coord (i + 1) p := by
  have h :
      (pochhammerBasis.coord (i + 1)).comp (LinearMap.mulLeft ℚ (X : Polynomial ℚ)) =
        pochhammerBasis.coord i - ((i + 1 : ℕ) : ℚ) • pochhammerBasis.coord (i + 1) := by
    apply pochhammerBasis.ext
    intro j
    rw [basis_apply]
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, X_mul_pochhammer, map_sub, map_smul, coord_basis, smul_eq_mul]
    by_cases hji : j = i
    · subst j
      simp [show i ≠ i + 1 by omega]
    · by_cases hjs : j = i + 1
      · subst j
        simp [show i + 1 ≠ i by omega, show i + 1 + 1 ≠ i + 1 by omega]
      · have hne : j + 1 ≠ i + 1 := by omega
        simp [hji, hjs, hne]
  exact congrArg (fun f : Polynomial ℚ →ₗ[ℚ] ℚ => f p) h

private theorem coord_difference (p : Polynomial ℚ) (i : ℕ) :
    pochhammerBasis.coord i (difference p) = (i : ℚ) * pochhammerBasis.coord i p := by
  have h : (pochhammerBasis.coord i).comp difference =
      (i : ℚ) • pochhammerBasis.coord i := by
    apply pochhammerBasis.ext
    intro j
    rw [basis_apply]
    simp only [LinearMap.comp_apply, difference_pochhammer, LinearMap.smul_apply,
      map_smul, coord_basis, smul_eq_mul]
    by_cases hji : j = i <;> simp [hji]
  exact congrArg (fun f : Polynomial ℚ →ₗ[ℚ] ℚ => f p) h

private theorem eval_zero_coord (p : Polynomial ℚ) :
    p.eval 0 = pochhammerBasis.coord 0 p := by
  have h : (Polynomial.leval (0 : ℚ)) = pochhammerBasis.coord 0 := by
    apply pochhammerBasis.ext
    intro j
    rw [basis_apply]
    change (ascPochhammer ℚ j).eval 0 = _
    rw [ascPochhammer_eval_zero, coord_basis]
  exact congrArg (fun f : Polynomial ℚ →ₗ[ℚ] ℚ => f p) h

private theorem eval_neg_one_coords (p : Polynomial ℚ) :
    p.eval (-1) = pochhammerBasis.coord 0 p - pochhammerBasis.coord 1 p := by
  have h : (Polynomial.leval (-1 : ℚ)) = pochhammerBasis.coord 0 - pochhammerBasis.coord 1 := by
    apply pochhammerBasis.ext
    intro j
    rw [basis_apply]
    change (ascPochhammer ℚ j).eval (-1) = _
    simp only [LinearMap.sub_apply, coord_basis]
    rcases j with _ | _ | j
    · simp
    · simp
    · have hz := ascPochhammer_eval_neg_coe_nat_of_lt (R := ℚ)
        (n := j + 2) (k := 1) (by omega)
      simpa using hz
  exact congrArg (fun f : Polynomial ℚ →ₗ[ℚ] ℚ => f p) h

private theorem row_evaluations (n : ℕ) :
    (rationalRow n).eval 0 = 0 ∧
      (rationalRow n).eval (-1) = (-1 : ℚ) ^ (wt n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      simp [rationalRow_zero, wt_zero]
    · by_cases he : n % 2 = 0
      · have hn : n = 2 * (n / 2) := by omega
        obtain ⟨k, hk, hnk⟩ : ∃ k : ℕ, 0 < k ∧ n = 2 * k :=
          ⟨n / 2, by omega, hn⟩
        have hsub := ih k (by omega)
        rw [hnk, rationalRow_even k hk, wt_even, difference_apply]
        constructor
        · simp
        · simp only [eval_mul, eval_X, eval_sub, eval_comp, eval_add, eval_one,
            neg_add_cancel, hsub.1, hsub.2, zero_sub]
          ring
      · obtain ⟨k, hnk⟩ : ∃ k : ℕ, n = 2 * k + 1 := ⟨n / 2, by omega⟩
        have hsub := ih k (by omega)
        rw [hnk, rationalRow_odd, wt_odd]
        constructor
        · simp
        · simp only [eval_mul, eval_X, hsub.2, pow_succ]
          ring

/-- Pochhammer coordinates with the parity correction on the entire basis. -/
noncomputable def signedCoefficient (n i : ℕ) : ℚ :=
  (-1 : ℚ) ^ (wt n + i) * pochhammerBasis.coord i (rowPolynomial n)

private theorem coord_row_zero (n : ℕ) : pochhammerBasis.coord 0 (rowPolynomial n) = 0 := by
  rw [← eval_zero_coord]
  simp [rowPolynomial]

private theorem signed_zero (n : ℕ) : signedCoefficient n 0 = 0 := by
  simp only [signedCoefficient, coord_row_zero, mul_zero]

private theorem signed_one (n : ℕ) : signedCoefficient n 1 = 1 := by
  have h := eval_neg_one_coords (rowPolynomial n)
  have he : (rowPolynomial n).eval (-1) = -((-1 : ℚ) ^ (wt n + 1)) := by
    simp [rowPolynomial, (row_evaluations n).2]
  rw [he, coord_row_zero] at h
  have hc : pochhammerBasis.coord 1 (rowPolynomial n) = (-1 : ℚ) ^ (wt n + 1) := by
    linear_combination h
  rw [signedCoefficient, hc, ← mul_pow]
  norm_num

private theorem zero_row (i : ℕ) : signedCoefficient 0 i = T 0 i := by
  have hq : rowPolynomial 0 = ascPochhammer ℚ 2 - ascPochhammer ℚ 1 := by
    rw [rowPolynomial, rationalRow_zero]
    rw [ascPochhammer_succ_right ℚ 1, ascPochhammer_one]
    norm_num <;> ring
  by_cases h0 : i = 0
  · subst i
    rw [signed_zero, T] <;> simp
  · by_cases h1 : i = 1
    · subst i
      exact (signed_one 0).trans (T_one 0).symm
    · by_cases h2 : i = 2
      · subst i
        rw [signedCoefficient, wt_zero, hq, T]
        simp only [map_sub, coord_basis]
        norm_num
      · rw [signedCoefficient, hq, T]
        simp only [map_sub, coord_basis]
        simp [h0, h1, h2, Ne.symm h1, Ne.symm h2]

private theorem signed_odd (n j : ℕ) :
    signedCoefficient (2 * n + 1) (j + 1) =
      ((j + 1 : ℕ) : ℚ) * signedCoefficient n (j + 1) + signedCoefficient n j := by
  simp only [signedCoefficient, wt_odd, rowPolynomial_odd, coord_X_succ,
    show wt n + 1 + (j + 1) = wt n + j + 1 + 1 by omega,
    show wt n + (j + 1) = wt n + j + 1 by omega, pow_succ]
  ring

private theorem even_cleared_succ (n j : ℕ) (hn : 0 < n) :
    (((j + 1 : ℕ) : ℚ) - 1) * signedCoefficient (2 * n) (j + 1) +
      signedCoefficient (2 * n) j =
    ((j + 1 : ℕ) : ℚ) * (((j + 1 : ℕ) : ℚ) - 1) * signedCoefficient n (j + 1) +
      ((j : ℚ) - 1) * signedCoefficient n j := by
  have h := congrArg (fun p : Polynomial ℚ => pochhammerBasis.coord (j + 1) p)
    (rowPolynomial_even n hn)
  change pochhammerBasis.coord (j + 1) ((X + 1) * rowPolynomial (2 * n)) =
    pochhammerBasis.coord (j + 1) (X * (difference (rowPolynomial n) - rowPolynomial n)) at h
  rw [add_mul, one_mul] at h
  simp only [map_add, coord_X_succ, map_sub, coord_difference] at h
  have hs := congrArg (fun a : ℚ => (-1 : ℚ) ^ (wt n + j) * a) h
  simp only [signedCoefficient, wt_even,
    show wt n + (j + 1) = (wt n + j) + 1 by omega, pow_succ]
  linear_combination hs

private theorem even_cleared (n i : ℕ) (hn : 0 < n) (hi : 2 ≤ i) :
    ((i : ℚ) - 1) * signedCoefficient (2 * n) i + signedCoefficient (2 * n) (i - 1) =
      (i : ℚ) * ((i : ℚ) - 1) * signedCoefficient n i +
        ((i : ℚ) - 2) * signedCoefficient n (i - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have h := even_cleared_succ n j hn
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h ⊢
  linear_combination h

private theorem signed_eq_array (n i : ℕ) : signedCoefficient n i = T n i := by
  induction n using Nat.strong_induction_on generalizing i with
  | h n rowIH =>
    by_cases hn : n = 0
    · subst n
      exact zero_row i
    induction i using Nat.strong_induction_on with
    | h i columnIH =>
      by_cases h0 : i = 0
      · subst i
        rw [signed_zero, T] <;> simp
      · by_cases h1 : i = 1
        · subst i
          rw [signed_one, T_one]
        · have hi : 2 ≤ i := by omega
          let k := n / 2
          have hlt : k < n := by dsimp [k]; omega
          have hk := rowIH k hlt i
          have hprev := rowIH k hlt (i - 1)
          by_cases he : n % 2 = 0
          · have hnk : n = 2 * k := by dsimp [k]; omega
            have hpos : 0 < k := by omega
            have hcol : signedCoefficient (2 * k) (i - 1) = T (2 * k) (i - 1) := by
              rw [← hnk]
              exact columnIH (i - 1) (by omega)
            have hc := even_cleared k i hpos hi
            rw [hcol, hk, hprev] at hc
            have hden : (i : ℚ) - 1 ≠ 0 := by
              have hp : (1 : ℚ) < (i : ℚ) := by exact_mod_cast (by omega : 1 < i)
              exact sub_ne_zero.mpr (ne_of_gt hp)
            have hT : ((i : ℚ) - 1) * T (2 * k) i + T (2 * k) (i - 1) =
                (i : ℚ) * ((i : ℚ) - 1) * T k i + ((i : ℚ) - 2) * T k (i - 1) := by
              rw [T_even k i hpos hi]
              field_simp [hden] <;> ring
            rw [hnk]
            apply mul_left_cancel₀ hden
            exact add_right_cancel (hc.trans hT.symm)
          · have hnk : n = 2 * k + 1 := by dsimp [k]; omega
            have hc : signedCoefficient (2 * k + 1) i =
                (i : ℚ) * signedCoefficient k i + signedCoefficient k (i - 1) := by
              obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
              simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using signed_odd k j
            rw [hnk, hc, hk, hprev, T_odd k i hi]

theorem source_coordinate (n j : ℕ) :
    pochhammerBasis.coord j (rowPolynomial n) = (-1 : ℚ) ^ (wt n + 2 - j) * T n j := by
  have h := signed_eq_array n j
  have hinv : (-1 : ℚ) ^ (wt n + j) * (-1 : ℚ) ^ (wt n + j) = 1 := by
    rw [← mul_pow]
    norm_num
  have hcoord : pochhammerBasis.coord j (rowPolynomial n) =
      (-1 : ℚ) ^ (wt n + j) * T n j := by
    rw [← h, signedCoefficient, ← mul_assoc, hinv, one_mul]
  by_cases hj : j ≤ wt n + 2
  · have hs : (-1 : ℚ) ^ (wt n + j) = (-1 : ℚ) ^ (wt n + 2 - j) := by
      rw [neg_one_pow_eq_pow_mod_two (wt n + j), neg_one_pow_eq_pow_mod_two (wt n + 2 - j)]
      congr 1 <;> omega
    rwa [hs] at hcoord
  · simp only [hcoord, support n j (by omega), mul_zero]

/-- The positive-even coefficient relation, cleared before dividing by the column minus one,
together with the literal rational coordinates of both rows. -/
theorem positiveEvenCoefficient (n i : ℕ) (hn : 0 < n) (hi : 2 ≤ i) :
    (((i : ℚ) - 1) * signedCoefficient (2 * n) i + signedCoefficient (2 * n) (i - 1) =
      (i : ℚ) * ((i : ℚ) - 1) * signedCoefficient n i +
        ((i : ℚ) - 2) * signedCoefficient n (i - 1)) ∧
    (∀ j : ℕ,
      pochhammerBasis.coord j (rowPolynomial (2 * n)) =
        (-1 : ℚ) ^ (wt (2 * n) + 2 - j) * T (2 * n) j ∧
      pochhammerBasis.coord j (rowPolynomial n) =
        (-1 : ℚ) ^ (wt n + 2 - j) * T n j) :=
  ⟨even_cleared n i hn hi, fun j => ⟨source_coordinate (2 * n) j, source_coordinate n j⟩⟩

end D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
