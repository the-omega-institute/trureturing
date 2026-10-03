/- GID: D5/S3/Combinatorics/PartialTheta/PartialThetaHankelQuotient
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PartialTheta/PartialThetaHankelQuotient
   mirror-E: none(waiver:integral-shifted-quotient-proof)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.NoZeroDivisors]
   utility: none
   digest: Scaled truncated rows and integral alternant division construct the Hankel quotient. -/

import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import D5.S3.Combinatorics.PartialTheta.PartialThetaHankelLowest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PartialTheta.PartialThetaHankelQuotient

open Polynomial Finset
open PartialThetaHankelDefs

set_option maxHeartbeats 1600000 in
theorem integral_quotient (m n : ℕ) :
    let dimension := n + m + 1
    let rowShift : Fin dimension → ℕ :=
      fun row => if (row : ℕ) < m then (m - row) * dimension else 0
    let augmented : Matrix (Fin dimension) (Fin dimension)
        (MvPolynomial (Fin (n + 1)) ℤ[X]) :=
      fun row column =>
        if before : (row : ℕ) < m then
          MvPolynomial.C (if (column : ℕ) < m - row then 0 else
            X ^ ((m - row + 1).choose 2 + (m - row) * (dimension - column)))
        else MvPolynomial.X ⟨(row : ℕ) - m, by omega⟩ ^ (column : ℕ)
    ∃ quotient : ℤ[X],
      hankel m dimension =
        (-1) ^ (m + 1).choose 2 * quotient * X ^ (m * n.choose 2) *
          hankel 0 (n + 1) ∧
      ∃ divided : MvPolynomial (Fin (n + 1)) ℤ[X],
        augmented.det =
          (∏ lower : Fin (n + 1), ∏ upper ∈ Ioi lower,
            (MvPolynomial.X upper - MvPolynomial.X lower)) * divided ∧
        X ^ ((∑ row : Fin dimension, rowShift row) + dimension * n.choose 2) * quotient =
          (-1) ^ (m + 1).choose 2 *
            X ^ ((∑ column : Fin dimension, (column : ℕ).choose 2) +
              2 * (n + 1).choose 3) *
            MvPolynomial.eval₂ (RingHom.id ℤ[X])
              (fun index : Fin (n + 1) => X ^ (index : ℕ)) divided := by
  classical
  dsimp only
  let dimension := n + m + 1
  let normalizer : ℤ[X] :=
    ∏ distance ∈ range n, (X ^ (distance + 1) - 1) ^ (n - distance)
  let rowShift : Fin dimension → ℕ :=
    fun row => if (row : ℕ) < m then (m - row) * dimension else 0
  let rowFactor : Fin dimension → ℕ :=
    fun row => if (row : ℕ) < m then 0 else ((row : ℕ) - m).choose 2
  let augmented : Matrix (Fin dimension) (Fin dimension)
      (MvPolynomial (Fin (n + 1)) ℤ[X]) :=
    fun row column =>
      if before : (row : ℕ) < m then
        MvPolynomial.C (if (column : ℕ) < m - row then 0 else
          X ^ ((m - row + 1).choose 2 + (m - row) * (dimension - column)))
      else MvPolynomial.X ⟨(row : ℕ) - m, by omega⟩ ^ (column : ℕ)
  let specialize : MvPolynomial (Fin (n + 1)) ℤ[X] →+* ℤ[X] :=
    MvPolynomial.eval₂Hom (RingHom.id ℤ[X]) (fun index => X ^ (index : ℕ))
  have choose_add : ∀ left right : ℕ,
      (left + right).choose 2 = left.choose 2 + right.choose 2 + left * right := by
    intro left right
    induction right with
    | zero => simp
    | succ right induction_hypothesis =>
      rw [Nat.add_succ, Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.choose_succ_succ, Nat.choose_one_right, induction_hypothesis]
      ring
  have sum_choose : ∀ size : ℕ,
      ∑ index ∈ range size, index.choose 2 = size.choose 3 := by
    intro size
    induction size with
    | zero => simp
    | succ size induction_hypothesis =>
      rw [sum_range_succ, induction_hypothesis, Nat.choose_succ_succ' size 2]
      norm_num only [Nat.reduceAdd]
      omega
  have sum_bottom : (∑ row : Fin dimension, rowFactor row) = (n + 1).choose 3 := by
    change (∑ row : Fin dimension,
      if (row : ℕ) < m then 0 else ((row : ℕ) - m).choose 2) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun row => if row < m then 0 else (row - m).choose 2) dimension]
    change (∑ row ∈ range (n + m + 1),
      if row < m then 0 else (row - m).choose 2) = (n + 1).choose 3
    rw [show n + m + 1 = m + (n + 1) by omega, sum_range_add]
    have initial : (∑ row ∈ range m, if row < m then 0 else (row - m).choose 2) = 0 := by
      apply sum_eq_zero
      intro row member
      simp [mem_range.mp member]
    rw [initial, zero_add]
    simpa using sum_choose (n + 1)
  let bottom : Fin (n + 1) → Fin dimension :=
    fun index => ⟨m + index, by dsimp [dimension]; omega⟩
  have bottom_injective : Function.Injective bottom := by
    intro left right equal
    apply Fin.ext
    have equal_values := congrArg Fin.val equal
    dsimp [bottom] at equal_values
    omega
  have bottom_powers : ∀ index column,
      augmented (bottom index) column = MvPolynomial.X index ^ (column : ℕ) := by
    intro index column
    simp [augmented, bottom]
  have alternant_division {R : Type} [CommRing R] [IsDomain R]
      (size dimension : ℕ)
      (matrix : Matrix (Fin dimension) (Fin dimension) (MvPolynomial (Fin size) R))
      (rows : Fin size → Fin dimension) (rows_injective : Function.Injective rows)
      (power_rows : ∀ index column,
        matrix (rows index) column = MvPolynomial.X index ^ (column : ℕ)) :
      ∃! quotient : MvPolynomial (Fin size) R,
        matrix.det =
          (∏ lower : Fin size, ∏ upper ∈ Ioi lower,
            (MvPolynomial.X upper - MvPolynomial.X lower)) * quotient := by
    classical
    let pairs : Finset (Fin size × Fin size) := univ.filter (fun pair => pair.1 < pair.2)
    let difference : Fin size × Fin size → MvPolynomial (Fin size) R :=
      fun pair => MvPolynomial.X pair.2 - MvPolynomial.X pair.1
    have identify_prime : ∀ lower upper : Fin size, lower < upper →
        Prime (MvPolynomial.X upper - MvPolynomial.X lower : MvPolynomial (Fin size) R) ∧
        ∀ polynomial : MvPolynomial (Fin size) R,
          MvPolynomial.X upper - MvPolynomial.X lower ∣ polynomial ↔
            (MvPolynomial.eval₂Hom MvPolynomial.C (fun index =>
              if index = upper then MvPolynomial.X lower else MvPolynomial.X index))
                polynomial = 0 := by
      intro lower upper ordered
      have distinct : lower ≠ upper := ne_of_lt ordered
      let remaining := {index : Fin size // index ≠ upper}
      let coordinate : MvPolynomial (Fin size) R ≃ₐ[R]
          Polynomial (MvPolynomial remaining R) :=
        (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe upper).symm).trans
          (MvPolynomial.optionEquivLeft R _)
      have coordinate_upper : coordinate (MvPolynomial.X upper) = Polynomial.X := by
        simp [coordinate, MvPolynomial.optionEquivLeft_X_none]
      have coordinate_lower : coordinate (MvPolynomial.X lower) =
          Polynomial.C (MvPolynomial.X ⟨lower, distinct⟩) := by
        simp [coordinate, Equiv.optionSubtypeNe_symm_of_ne distinct]
      have coordinate_difference : coordinate (MvPolynomial.X upper - MvPolynomial.X lower) =
          Polynomial.X - Polynomial.C (MvPolynomial.X (⟨lower, distinct⟩ : remaining)) := by
        rw [map_sub, coordinate_upper, coordinate_lower]
      have prime : Prime
          (MvPolynomial.X upper - MvPolynomial.X lower : MvPolynomial (Fin size) R) := by
        apply (MulEquiv.prime_iff coordinate.toMulEquiv).mp
        change Prime (coordinate (MvPolynomial.X upper - MvPolynomial.X lower))
        rw [coordinate_difference]
        exact Polynomial.prime_X_sub_C _
      refine ⟨prime, ?_⟩
      intro polynomial
      let collapse : MvPolynomial (Fin size) R →+* MvPolynomial (Fin size) R :=
        MvPolynomial.eval₂Hom MvPolynomial.C
          (fun index => if index = upper then MvPolynomial.X lower else MvPolynomial.X index)
      let inclusion : MvPolynomial remaining R →+* MvPolynomial (Fin size) R :=
        (MvPolynomial.rename Subtype.val).toRingHom
      have include_injective : Function.Injective inclusion :=
        MvPolynomial.rename_injective _ Subtype.val_injective
      have evaluation_identity :
          inclusion.comp ((Polynomial.evalRingHom
            (MvPolynomial.X (⟨lower, distinct⟩ : remaining))).comp
            coordinate.toRingHom) = collapse := by
        apply MvPolynomial.ringHom_ext
        · intro coefficient
          simp [inclusion, coordinate, collapse]
        · intro index
          by_cases is_upper : index = upper
          · subst index
            simp [inclusion, collapse, coordinate_upper]
          · simp [inclusion, coordinate, collapse,
              Equiv.optionSubtypeNe_symm_of_ne is_upper, is_upper]
      have zero_equivalence :
          Polynomial.eval (MvPolynomial.X (⟨lower, distinct⟩ : remaining))
            (coordinate polynomial) = 0 ↔
            collapse polynomial = 0 := by
        rw [← include_injective.eq_iff]
        have evaluated := congrArg
          (fun hom : MvPolynomial (Fin size) R →+* MvPolynomial (Fin size) R =>
            hom polynomial) evaluation_identity
        change inclusion (Polynomial.eval (MvPolynomial.X (⟨lower, distinct⟩ : remaining))
          (coordinate polynomial)) = collapse polynomial at evaluated
        rw [evaluated, map_zero]
      change MvPolynomial.X upper - MvPolynomial.X lower ∣ polynomial ↔ collapse polynomial = 0
      have divides_equivalence : MvPolynomial.X upper - MvPolynomial.X lower ∣ polynomial ↔
          coordinate (MvPolynomial.X upper - MvPolynomial.X lower) ∣ coordinate polynomial :=
        ⟨map_dvd coordinate, fun divides => by simpa using map_dvd coordinate.symm divides⟩
      rw [divides_equivalence, coordinate_difference, Polynomial.dvd_iff_isRoot]
      exact zero_equivalence
    have prime_factors : ∀ pair ∈ pairs, Prime (difference pair) := by
      intro pair pair_mem
      exact (identify_prime pair.1 pair.2 (mem_filter.mp pair_mem).2).1
    have factor_divides : ∀ pair ∈ pairs, difference pair ∣ matrix.det := by
      intro pair pair_mem
      have ordered := (mem_filter.mp pair_mem).2
      rw [(identify_prime pair.1 pair.2 ordered).2]
      rw [RingHom.map_det]
      apply Matrix.det_zero_of_row_eq (rows_injective.ne (ne_of_lt ordered))
      funext column
      change (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun index => if index = pair.2 then MvPolynomial.X pair.1 else MvPolynomial.X index))
          (matrix (rows pair.1) column) =
        (MvPolynomial.eval₂Hom MvPolynomial.C
          (fun index => if index = pair.2 then MvPolynomial.X pair.1 else MvPolynomial.X index))
          (matrix (rows pair.2) column)
      simp only [power_rows, map_pow, MvPolynomial.eval₂Hom_X']
      simp [ne_of_lt ordered]
    have factors_separate : ∀ pair ∈ pairs, ∀ other ∈ pairs,
        pair ≠ other → ¬ difference pair ∣ difference other := by
      intro pair pair_mem other other_mem distinct divides
      have ordered := (mem_filter.mp pair_mem).2
      have other_ordered := (mem_filter.mp other_mem).2
      have collapsed := ((identify_prime pair.1 pair.2 ordered).2 (difference other)).mp divides
      simp only [difference, map_sub, MvPolynomial.eval₂Hom_X', sub_eq_zero] at collapsed
      have identified :
          (if other.2 = pair.2 then pair.1 else other.2) =
            (if other.1 = pair.2 then pair.1 else other.1) := by
        apply MvPolynomial.X_injective (R := R)
        simpa only [apply_ite] using collapsed
      by_cases upper_same : other.2 = pair.2 <;>
        by_cases lower_same : other.1 = pair.2 <;>
        simp only [upper_same, lower_same, ite_true, ite_false] at identified
      · exact (ne_of_lt other_ordered) (lower_same.trans upper_same.symm)
      · apply distinct
        exact Prod.ext identified upper_same.symm
      · have : pair.1 < pair.2 := ordered
        have : pair.2 < pair.1 := by simpa [lower_same, identified] using other_ordered
        exact (not_lt_of_ge (le_of_lt ordered)) this
      · exact (ne_of_lt other_ordered) identified.symm
    have avoids_product : ∀ pair ∈ pairs, ∀ selected : Finset (Fin size × Fin size),
        (∀ other ∈ selected, ¬ difference pair ∣ difference other) →
          ¬ difference pair ∣ ∏ other ∈ selected, difference other := by
      intro pair pair_mem selected
      induction selected using Finset.induction_on with
      | empty =>
        intro _
        simpa using (prime_factors pair pair_mem).not_dvd_one
      | @insert other rest absent induction_hypothesis =>
        intro avoids
        rw [prod_insert absent, (prime_factors pair pair_mem).dvd_mul]
        exact not_or.mpr ⟨avoids other (mem_insert_self _ _),
          induction_hypothesis (fun element element_mem =>
            avoids element (mem_insert_of_mem element_mem))⟩
    have product_divides : ∀ selected : Finset (Fin size × Fin size), selected ⊆ pairs →
        (∏ pair ∈ selected, difference pair) ∣ matrix.det := by
      intro selected
      induction selected using Finset.induction_on with
      | empty => simp
      | @insert pair selected absent induction_hypothesis =>
        intro subset
        have pair_mem := subset (mem_insert_self _ _)
        have selected_subset : selected ⊆ pairs := fun other other_mem =>
          subset (mem_insert_of_mem other_mem)
        obtain ⟨residual, residual_identity⟩ := induction_hypothesis selected_subset
        have divides_residual : difference pair ∣ residual := by
          have divides_product : difference pair ∣
              (∏ other ∈ selected, difference other) * residual :=
            residual_identity ▸ factor_divides pair pair_mem
          rcases (prime_factors pair pair_mem).dvd_mul.mp divides_product with
            divides_previous | divides_residual
          · exfalso
            apply avoids_product pair pair_mem selected _ divides_previous
            intro other other_mem
            apply factors_separate pair pair_mem other (selected_subset other_mem)
            intro equality
            exact absent (equality ▸ other_mem)
          · exact divides_residual
        obtain ⟨quotient, quotient_identity⟩ := divides_residual
        refine ⟨quotient, ?_⟩
        rw [prod_insert absent, residual_identity, quotient_identity, mul_assoc]
        ring
    have product_nonzero : (∏ pair ∈ pairs, difference pair) ≠ 0 := by
      apply prod_ne_zero_iff.mpr
      intro pair pair_mem
      exact (prime_factors pair pair_mem).ne_zero
    obtain ⟨quotient, quotient_identity⟩ := product_divides pairs (Subset.refl _)
    have product_identity :
        (∏ pair ∈ pairs, difference pair) =
          ∏ lower : Fin size, ∏ upper ∈ Ioi lower,
            (MvPolynomial.X upper - MvPolynomial.X lower : MvPolynomial (Fin size) R) := by
      simp only [pairs, prod_filter, difference]
      rw [← univ_product_univ, prod_product]
      apply prod_congr rfl
      intro lower _
      have interval_identity : Ioi lower = univ.filter (fun upper : Fin size => lower < upper) := by
        ext upper
        simp
      rw [interval_identity, prod_filter]
    refine ⟨quotient, product_identity ▸ quotient_identity, ?_⟩
    intro other other_identity
    apply mul_left_cancel₀ product_nonzero
    rw [product_identity, ← other_identity, ← product_identity, ← quotient_identity]
  obtain ⟨divided, division, _⟩ := alternant_division
    (n + 1) dimension augmented bottom bottom_injective bottom_powers
  have scaled_entries :
      (Matrix.of fun row column : Fin dimension =>
        (X : ℤ[X]) ^ rowShift row *
          coeffA (-(m : ℤ) + (row : ℕ) + (column : ℕ))) =
      Matrix.of (fun row column : Fin dimension =>
        X ^ rowFactor row * (X ^ (column : ℕ).choose 2 *
          specialize (augmented row column))) := by
    apply Matrix.ext
    intro row column
    simp only [Matrix.of_apply]
    by_cases before : (row : ℕ) < m
    · by_cases missing : (column : ℕ) < m - row
      · have negative : ¬ 0 ≤ -(m : ℤ) + (row : ℕ) + (column : ℕ) := by omega
        simp [rowShift, rowFactor, augmented, before, missing, coeffA, negative]
      · have nonnegative : 0 ≤ -(m : ℤ) + (row : ℕ) + (column : ℕ) := by omega
        have shifted : (-(m : ℤ) + (row : ℕ) + (column : ℕ)).toNat =
            (column : ℕ) - (m - row) := by omega
        simp only [rowShift, rowFactor, augmented, before, dite_true, if_true,
          if_false, missing, specialize, MvPolynomial.eval₂Hom_C, RingHom.id_apply,
          coeffA, nonnegative, shifted, pow_zero, one_mul]
        rw [← pow_add, ← pow_add]
        congr 1
        have column_bound := column.isLt
        have shifted_add : (column : ℕ) = (column : ℕ) - (m - row) + (m - row) := by
          omega
        have binomial := choose_add ((column : ℕ) - (m - row)) (m - row)
        rw [← shifted_add] at binomial
        have successor := Nat.choose_succ_succ' (m - row) 1
        rw [Nat.choose_one_right] at successor
        norm_num only [Nat.reduceAdd] at successor
        have subtraction : dimension - (column : ℕ) + (column : ℕ) = dimension := by
          omega
        have triangle : ∀ size : ℕ, 2 * size.choose 2 + size = size * size := by
          intro size
          induction size with
          | zero => simp
          | succ size induction_hypothesis =>
            rw [Nat.choose_succ_succ' size 1, Nat.choose_one_right]
            norm_num only [Nat.reduceAdd]
            nlinarith
        have square := triangle (m - row)
        nlinarith
    · have nonnegative : 0 ≤ -(m : ℤ) + (row : ℕ) + (column : ℕ) := by omega
      have shifted : (-(m : ℤ) + (row : ℕ) + (column : ℕ)).toNat =
          (row : ℕ) - m + column := by omega
      simp only [rowShift, rowFactor, augmented, before, dite_false, if_false,
        specialize, map_pow, coeffA, nonnegative,
        if_true, shifted, pow_zero, one_mul]
      rw [choose_add]
      simp [pow_add, pow_mul, mul_assoc]
  have scaled_determinant :
      X ^ (∑ row : Fin dimension, rowShift row) * hankel m dimension =
        X ^ ((∑ column : Fin dimension, (column : ℕ).choose 2) + (n + 1).choose 3) *
          specialize augmented.det := by
    have mapped : (Matrix.of fun row column => specialize (augmented row column)).det =
        specialize augmented.det := (specialize.map_det augmented).symm
    calc
      _ = (∏ row : Fin dimension, (X : ℤ[X]) ^ rowShift row) * hankel m dimension := by
        rw [prod_pow_eq_pow_sum]
      _ = (Matrix.of fun row column : Fin dimension =>
          (X : ℤ[X]) ^ rowShift row *
            coeffA (-(m : ℤ) + (row : ℕ) + (column : ℕ))).det :=
        (Matrix.det_mul_column
          (fun row : Fin dimension => (X : ℤ[X]) ^ rowShift row)
          (Matrix.of fun row column : Fin dimension =>
            coeffA (-(m : ℤ) + (row : ℕ) + (column : ℕ)))).symm
      _ = (Matrix.of fun row column : Fin dimension =>
          (X : ℤ[X]) ^ rowFactor row * (X ^ (column : ℕ).choose 2 *
            specialize (augmented row column))).det := congrArg Matrix.det scaled_entries
      _ = (∏ row : Fin dimension, (X : ℤ[X]) ^ rowFactor row) *
          (Matrix.of fun row column : Fin dimension =>
            X ^ (column : ℕ).choose 2 * specialize (augmented row column)).det :=
        Matrix.det_mul_column
          (fun row : Fin dimension => (X : ℤ[X]) ^ rowFactor row)
          (Matrix.of fun row column : Fin dimension =>
            (X : ℤ[X]) ^ (column : ℕ).choose 2 * specialize (augmented row column))
      _ = (∏ row : Fin dimension, (X : ℤ[X]) ^ rowFactor row) *
          ((∏ column : Fin dimension, (X : ℤ[X]) ^ (column : ℕ).choose 2) *
            (Matrix.of fun row column => specialize (augmented row column)).det) :=
        congrArg (fun value => (∏ row : Fin dimension, (X : ℤ[X]) ^ rowFactor row) * value)
          (Matrix.det_mul_row
            (fun column : Fin dimension => (X : ℤ[X]) ^ (column : ℕ).choose 2)
            (Matrix.of fun row column : Fin dimension => specialize (augmented row column)))
      _ = _ := by
        rw [mapped, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, sum_bottom, pow_add]
        ring
  have coprime : IsCoprime normalizer (X : ℤ[X]) := by
    apply IsCoprime.prod_left
    intro distance _
    apply IsCoprime.pow_left
    refine ⟨-1, X ^ distance, ?_⟩
    rw [pow_succ]
    ring
  have unshifted_entries :
      (Matrix.of fun row column : Fin (n + 1) =>
        coeffA (-(0 : ℤ) + (row : ℕ) + (column : ℕ))) =
      Matrix.of (fun row column : Fin (n + 1) =>
        (X : ℤ[X]) ^ (row : ℕ).choose 2 *
          (X ^ (column : ℕ).choose 2 *
            Matrix.vandermonde (fun index : Fin (n + 1) =>
              (X : ℤ[X]) ^ (index : ℕ)) row column)) := by
    apply Matrix.ext
    intro row column
    simp only [Matrix.of_apply, coeffA, neg_zero, zero_add, ← Int.natCast_add,
      Int.natCast_nonneg, ite_true, Int.toNat_natCast, Matrix.vandermonde_apply]
    rw [choose_add]
    simp [pow_add, pow_mul, mul_assoc]
  have power_total : (∑ index : Fin (n + 1), (index : ℕ).choose 2) =
      (n + 1).choose 3 := by
    rw [Fin.sum_univ_eq_sum_range (fun index => index.choose 2) (n + 1), sum_choose]
  have vandermonde_scaled : hankel 0 (n + 1) =
      X ^ (2 * (n + 1).choose 3) *
        (Matrix.vandermonde (fun index : Fin (n + 1) =>
          (X : ℤ[X]) ^ (index : ℕ))).det := by
    unfold hankel
    simp only [Nat.cast_zero]
    rw [unshifted_entries]
    erw [Matrix.det_mul_column
      (fun row : Fin (n + 1) => (X : ℤ[X]) ^ (row : ℕ).choose 2)
      (Matrix.of fun row column : Fin (n + 1) =>
        (X : ℤ[X]) ^ (column : ℕ).choose 2 *
          Matrix.vandermonde (fun index : Fin (n + 1) =>
            (X : ℤ[X]) ^ (index : ℕ)) row column),
      Matrix.det_mul_row
        (fun column : Fin (n + 1) => (X : ℤ[X]) ^ (column : ℕ).choose 2)
        (Matrix.vandermonde (fun index : Fin (n + 1) => (X : ℤ[X]) ^ (index : ℕ)))]
    simp only [prod_pow_eq_pow_sum, power_total]
    rw [show 2 * (n + 1).choose 3 = (n + 1).choose 3 + (n + 1).choose 3 by omega,
      pow_add]
    ring
  have exponent : (n + 1) * n.choose 2 = 3 * (n + 1).choose 3 := by
    simpa [mul_comm] using Nat.add_one_mul_choose_eq n 2
  have vandermonde_factor :
      (Matrix.vandermonde (fun index : Fin (n + 1) =>
        (X : ℤ[X]) ^ (index : ℕ))).det = X ^ (n + 1).choose 3 * normalizer := by
    apply mul_left_cancel₀ (pow_ne_zero (2 * (n + 1).choose 3) X_ne_zero)
    rw [← vandermonde_scaled, (PartialThetaHankelVandermonde.unshifted n).1]
    change X ^ ((n + 1) * n.choose 2) * normalizer = _
    rw [exponent, ← mul_assoc, ← pow_add]
    congr 2
    omega
  have specialized_division : specialize augmented.det =
      X ^ (n + 1).choose 3 * normalizer * specialize divided := by
    rw [division, map_mul]
    have product_identity : specialize
        (∏ lower : Fin (n + 1), ∏ upper ∈ Ioi lower,
          (MvPolynomial.X upper - MvPolynomial.X lower)) =
        (Matrix.vandermonde (fun index : Fin (n + 1) =>
          (X : ℤ[X]) ^ (index : ℕ))).det := by
      rw [Matrix.det_vandermonde]
      simp [specialize]
    rw [product_identity, vandermonde_factor]
  have expanded :
      X ^ (∑ row : Fin dimension, rowShift row) * hankel m dimension =
        X ^ ((∑ column : Fin dimension, (column : ℕ).choose 2) +
          2 * (n + 1).choose 3) * normalizer * specialize divided := by
    rw [scaled_determinant, specialized_division]
    rw [show (∑ column : Fin dimension, (column : ℕ).choose 2) +
        2 * (n + 1).choose 3 =
        ((∑ column : Fin dimension, (column : ℕ).choose 2) + (n + 1).choose 3) +
          (n + 1).choose 3 by omega, pow_add]
    ring
  have distance_divides : normalizer ∣ hankel m dimension := by
    apply (coprime.pow_right (n := ∑ row : Fin dimension, rowShift row)).dvd_of_dvd_mul_left
    rw [expanded]
    exact dvd_mul_of_dvd_left (dvd_mul_left normalizer _) _
  have monomial_divides : (X : ℤ[X]) ^ (dimension * n.choose 2) ∣ hankel m dimension := by
    apply X_pow_dvd_iff.mpr
    simpa [dimension, add_comm, add_left_comm, add_assoc] using
      (PartialThetaHankelLowest.lowest_term m n).1
  obtain ⟨residual, residual_identity⟩ :=
    (coprime.pow_right (n := dimension * n.choose 2)).symm.mul_dvd
      monomial_divides distance_divides
  let quotient : ℤ[X] := (-1) ^ (m + 1).choose 2 * residual
  have sign_square : ((-1 : ℤ[X]) ^ (m + 1).choose 2) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have quotient_identity : hankel m dimension =
      (-1) ^ (m + 1).choose 2 * quotient * X ^ (dimension * n.choose 2) * normalizer := by
    dsimp [quotient]
    rw [show (-1 : ℤ[X]) ^ (m + 1).choose 2 *
        ((-1) ^ (m + 1).choose 2 * residual) = residual by
      rw [← mul_assoc, ← pow_two, sign_square, one_mul]]
    rw [residual_identity]
    ring
  refine ⟨quotient, ?_, divided, division, ?_⟩
  · rw [(PartialThetaHankelVandermonde.unshifted n).1]
    change hankel m dimension = _ * _ * _ * (_ * normalizer)
    rw [quotient_identity]
    have exponents : dimension * n.choose 2 =
        m * n.choose 2 + (n + 1) * n.choose 2 := by dsimp [dimension]; ring
    rw [exponents, pow_add]
    ring
  · have equation := expanded
    rw [residual_identity] at equation
    have cancelled :
        X ^ ((∑ row : Fin dimension, rowShift row) + dimension * n.choose 2) * residual =
          X ^ ((∑ column : Fin dimension, (column : ℕ).choose 2) +
            2 * (n + 1).choose 3) * specialize divided := by
      apply mul_left_cancel₀ (PartialThetaHankelVandermonde.unshifted n).2.2.1.ne_zero
      change normalizer * _ = normalizer * _
      rw [pow_add]
      convert equation using 1 <;> ring
    change _ * quotient = _ * _ * specialize divided
    dsimp [quotient]
    rw [mul_left_comm, cancelled]
    ring

end D5.S3.Combinatorics.PartialTheta.PartialThetaHankelQuotient
