/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnBranches
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnBranches
   mirror-E: none(waiver:mixed-branch-confluence-bound)
   anchors: [mathlib/module/Mathlib.Algebra.Group.ForwardDiff]
   utility: none
   digest: Same-branch pairs among confluent nodes bound the mixed exponent polynomials. -/

import Mathlib.Algebra.Group.ForwardDiff
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDeterminant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnBranches

open Polynomial Finset CiglerMotzkinHankelBranches

/-- Only the confluent nodes force same-branch zeros in a mixed Vandermonde. -/
theorem mixed_branch_coefficients {K : Type*} [Field K] [CharZero K]
    (size : ℕ) (zeroNodes : Finset (Fin size))
    (u : Fin size → (PowerSeries K)ˣ) (α : Kˣ)
    (constant : ∀ i ∈ zeroNodes, PowerSeries.constantCoeff (u i : PowerSeries K) = α)
    (a b : Fin size → PowerSeries K) :
    ∃ P : Finset (Fin size) → K[X],
      (∀ S, (P S).natDegree ≤
        (zeroNodes ∩ S).card * (zeroNodes.card - (zeroNodes ∩ S).card)) ∧
      ∀ n : ℤ, PowerSeries.coeff (zeroNodes.card.choose 2)
        (Matrix.of fun row column : Fin size =>
          a column * ((u column ^ (n + row.val) : (PowerSeries K)ˣ) : PowerSeries K) +
          b column * ((u column ^ (-(n + row.val)) : (PowerSeries K)ˣ) : PowerSeries K)).det =
        ∑ S : Finset (Fin size),
          ((Units.map PowerSeries.constantCoeff.toMonoidHom
            (∏ i, if i ∈ S then (u i)⁻¹ else u i) ^ n : Kˣ) : K) * (P S).eval (n : K) := by
  classical
  let w (S : Finset (Fin size)) (i : Fin size) := if i ∈ S then (u i)⁻¹ else u i
  let h (S : Finset (Fin size)) (i : Fin size) := if i ∈ S then b i else a i
  let v (S : Finset (Fin size)) : (PowerSeries K)ˣ := ∏ i, w S i
  let β (S : Finset (Fin size)) : Kˣ :=
    Units.map PowerSeries.constantCoeff.toMonoidHom (v S)
  let pairs : Finset (Fin size × Fin size) :=
    (univ ×ˢ univ).filter (fun p => p.1 < p.2)
  let same (S : Finset (Fin size)) := pairs.filter
    (fun p => p.1 ∈ zeroNodes ∧ p.2 ∈ zeroNodes ∧ (p.1 ∈ S ↔ p.2 ∈ S))
  let j (S : Finset (Fin size)) := (zeroNodes ∩ S).card
  have constant_unit (i : Fin size) (hi : i ∈ zeroNodes) :
      Units.map PowerSeries.constantCoeff.toMonoidHom (u i) = α :=
    Units.ext (constant i hi)
  have branch_constant (S : Finset (Fin size)) (i : Fin size) (hi : i ∈ zeroNodes) :
      PowerSeries.constantCoeff (w S i : PowerSeries K) =
        (if i ∈ S then ((α⁻¹ : Kˣ) : K) else (α : K)) := by
    by_cases inside : i ∈ S
    · have inverse := congrArg Units.val
        (show Units.map PowerSeries.constantCoeff.toMonoidHom ((u i)⁻¹) = α⁻¹ by
          rw [map_inv, constant_unit i hi])
      change PowerSeries.constantCoeff (((u i)⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) =
        ((α⁻¹ : Kˣ) : K) at inverse
      simpa only [w, inside, if_true] using inverse
    · simpa only [w, inside, if_false] using constant i hi
  have product_constant (S : Finset (Fin size)) :
      PowerSeries.constantCoeff (v S : PowerSeries K) = β S := rfl
  have pair_count (S : Finset (Fin size)) :
      (same S).card = (j S).choose 2 + (zeroNodes.card - j S).choose 2 := by
    have partition : same S =
        (((zeroNodes ∩ S) ×ˢ (zeroNodes ∩ S)).filter (fun p => p.1 < p.2)) ∪
          (((zeroNodes \ S) ×ˢ (zeroNodes \ S)).filter (fun p => p.1 < p.2)) := by
      ext p
      simp only [same, pairs, mem_filter, mem_product, mem_univ, true_and,
        mem_union, mem_inter, mem_sdiff]
      tauto
    have disjoint : Disjoint
        (((zeroNodes ∩ S) ×ˢ (zeroNodes ∩ S)).filter (fun p => p.1 < p.2))
        (((zeroNodes \ S) ×ˢ (zeroNodes \ S)).filter (fun p => p.1 < p.2)) := by
      rw [Finset.disjoint_left]
      intro p left right
      have positive := (mem_inter.mp (mem_product.mp (mem_filter.mp left).1).1).2
      have negative := (mem_sdiff.mp (mem_product.mp (mem_filter.mp right).1).1).2
      exact negative positive
    rw [partition, card_union_of_disjoint disjoint, card_product_filter_lt,
      card_product_filter_lt, card_sdiff, inter_comm S zeroNodes]
  have triangle_add (j k : ℕ) : (j + k).choose 2 = j.choose 2 + k.choose 2 + j * k := by
    induction j with
    | zero => simp
    | succ j previous =>
      rw [show j + 1 + k = (j + k) + 1 by omega, Nat.choose_succ_succ,
        Nat.choose_one_right, previous, Nat.choose_succ_succ, Nat.choose_one_right]
      change j + k + (j.choose 2 + k.choose 2 + j * k) =
        j + j.choose 2 + k.choose 2 + (j + 1) * k
      ring
  have order_split (S : Finset (Fin size)) :
      (same S).card + j S * (zeroNodes.card - j S) = zeroNodes.card.choose 2 := by
    rw [pair_count, ← triangle_add]
    congr 1
    have bound : j S ≤ zeroNodes.card := card_le_card inter_subset_left
    omega
  have vandermonde_product (S : Finset (Fin size)) :
      (Matrix.vandermonde (fun i => (w S i : PowerSeries K))).det =
        ∏ p ∈ pairs, ((w S p.2 : PowerSeries K) - (w S p.1 : PowerSeries K)) := by
    rw [Matrix.det_vandermonde]; dsimp only [pairs]
    rw [prod_filter, prod_product]; apply prod_congr rfl
    intro i _
    have interval : (Ioi i : Finset (Fin size)) = univ.filter (i < ·) := by ext j; simp
    rw [interval, prod_filter]
  have cancellation (S : Finset (Fin size)) :
      ∃ G : PowerSeries K,
        (Matrix.vandermonde (fun i => (w S i : PowerSeries K))).det =
          PowerSeries.X ^ (same S).card * G := by
    have common : PowerSeries.X ^ (same S).card ∣
        ∏ p ∈ same S, ((w S p.2 : PowerSeries K) - (w S p.1 : PowerSeries K)) := by
      simpa only [prod_const] using
        (prod_dvd_prod_of_dvd (s := same S) (fun _ => (PowerSeries.X : PowerSeries K))
          (fun p => (w S p.2 : PowerSeries K) - (w S p.1 : PowerSeries K)) (by
            intro p hp; apply PowerSeries.X_dvd_iff.mpr
            have members := (mem_filter.mp hp).2
            rw [map_sub, branch_constant S p.2 members.2.1,
              branch_constant S p.1 members.1]
            have matching := members.2.2
            by_cases inside : p.1 ∈ S
            · simp [inside, matching.mp inside]
            · simp [inside,
                show p.2 ∉ S from fun member => inside (matching.mpr member)]))
    have extension := prod_dvd_prod_of_subset (same S) pairs
      (fun p => (w S p.2 : PowerSeries K) - (w S p.1 : PowerSeries K))
      (filter_subset _ _)
    obtain ⟨G, product⟩ := common.trans extension
    exact ⟨G, by rw [vandermonde_product]; exact product⟩
  have contribution (S : Finset (Fin size)) :
      ∃ Q : K[X], Q.natDegree ≤ j S * (zeroNodes.card - j S) ∧ ∀ n : ℤ,
        PowerSeries.coeff (zeroNodes.card.choose 2)
          (Matrix.of fun row column : Fin size =>
            h S column * ((w S column ^ (n + row.val) : (PowerSeries K)ˣ) :
              PowerSeries K)).det =
          ((β S ^ n : Kˣ) : K) * Q.eval (n : K) := by
    obtain ⟨G, factored⟩ := cancellation S
    let scalar : (PowerSeries K)ˣ := Units.map PowerSeries.C.toMonoidHom (β S)
    let normalized : (PowerSeries K)ˣ := scalar⁻¹ * v S
    have normalized_constant : PowerSeries.constantCoeff (normalized : PowerSeries K) = 1 := by
      dsimp only [normalized, scalar]; rw [Units.val_mul, map_mul, product_constant]
      simp
    let H : PowerSeries K := (∏ i, h S i) * G
    obtain ⟨Q, degree_bound, polynomial⟩ :=
      unit_power_coefficients normalized normalized_constant H (j S * (zeroNodes.card - j S))
    refine ⟨Q, degree_bound, ?_⟩
    intro n
    have factor_matrix :
        (Matrix.of fun row column : Fin size =>
          h S column * ((w S column ^ (n + row.val) : (PowerSeries K)ˣ) :
            PowerSeries K)) =
          Matrix.of (fun row column : Fin size =>
            (h S column * ((w S column ^ n : (PowerSeries K)ˣ) : PowerSeries K)) *
              ((Matrix.vandermonde (fun i => (w S i : PowerSeries K))).transpose
                row column)) := by
      ext row column
      simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
        zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
      ring
    rw [factor_matrix, Matrix.det_mul_row
      (fun i => h S i * ((w S i ^ n : (PowerSeries K)ˣ) : PowerSeries K))
      (Matrix.vandermonde (fun i => (w S i : PowerSeries K))).transpose,
      Matrix.det_transpose, prod_mul_distrib]
    have product_power :
        (∏ i, ((w S i ^ n : (PowerSeries K)ˣ) : PowerSeries K)) =
          ((v S ^ n : (PowerSeries K)ˣ) : PowerSeries K) := by
      change (∏ i, (Units.coeHom (PowerSeries K)) (w S i ^ n)) = _
      rw [← map_prod, prod_zpow]; rfl
    rw [product_power, factored]
    have normalized_power : ((v S ^ n : (PowerSeries K)ˣ) : PowerSeries K) =
        PowerSeries.C ((β S ^ n : Kˣ) : K) *
          ((normalized ^ n : (PowerSeries K)ˣ) : PowerSeries K) := by
      have v_split : v S = scalar * normalized := by dsimp only [normalized]; simp
      rw [v_split, mul_zpow, Units.val_mul]
      congr 1
      change ((scalar ^ n : (PowerSeries K)ˣ) : PowerSeries K) =
        ((Units.map PowerSeries.C.toMonoidHom (β S ^ n) : (PowerSeries K)ˣ) : PowerSeries K)
      exact (congrArg Units.val
        (map_zpow (Units.map PowerSeries.C.toMonoidHom) (β S) n)).symm
    rw [normalized_power]
    have reordered :
        (∏ i, h S i) *
          (PowerSeries.C ((β S ^ n : Kˣ) : K) *
            ((normalized ^ n : (PowerSeries K)ˣ) : PowerSeries K)) *
          (PowerSeries.X ^ (same S).card * G) =
        PowerSeries.C ((β S ^ n : Kˣ) : K) *
          (PowerSeries.X ^ (same S).card *
            (H * ((normalized ^ n : (PowerSeries K)ˣ) : PowerSeries K))) := by
      dsimp only [H]; ring
    rw [reordered, PowerSeries.coeff_C_mul,
      show zeroNodes.card.choose 2 = (same S).card + j S * (zeroNodes.card - j S)
        from (order_split S).symm,
      Nat.add_comm (same S).card, PowerSeries.coeff_X_pow_mul]
    rw [polynomial]
  choose P degree_bound formula using contribution
  refine ⟨P, degree_bound, ?_⟩
  intro n
  have expansion :
      (Matrix.of fun row column : Fin size =>
        a column * ((u column ^ (n + row.val) : (PowerSeries K)ˣ) : PowerSeries K) +
        b column * ((u column ^ (-(n + row.val)) : (PowerSeries K)ˣ) : PowerSeries K)).det =
      ∑ S : Finset (Fin size), (Matrix.of fun row column : Fin size =>
        h S column * ((w S column ^ (n + row.val) : (PowerSeries K)ˣ) :
          PowerSeries K)).det := by
    rw [← Matrix.det_transpose]
    have expanded := Matrix.detRowAlternating.map_add_univ
      (fun column row => b column *
        ((u column ^ (-(n + row.val)) : (PowerSeries K)ˣ) : PowerSeries K))
      (fun column row => a column *
        ((u column ^ (n + row.val) : (PowerSeries K)ˣ) : PowerSeries K))
    convert expanded using 1
    · congr 1
      ext row column; simp [Matrix.transpose_apply, Matrix.of_apply, Pi.add_apply, add_comm]
    · apply sum_congr rfl
      intro S _; rw [← Matrix.det_transpose]
      congr 1
      ext row column
      by_cases inside : row ∈ S <;>
        simp [Matrix.transpose_apply, Matrix.of_apply, Finset.piecewise, h, w, inside]
  rw [expansion, map_sum]; apply sum_congr rfl
  intro S _; rw [formula S n]


/-- A step-sized difference annihilates every mode in its common power class. -/
theorem grouped_recurrence {K : Type*} [Field K] [CharZero K]
    {I J : Type*} [Fintype I] [Fintype J]
    (step : ℕ) (positive : 0 < step) (index : I → J) (rho : I → Kˣ) (mode : J → Kˣ)
    (mode_power : ∀ i, rho i ^ step = mode (index i))
    (P : I → K[X]) (e : J → ℕ) (degree : ∀ i, (P i).natDegree < e (index i)) :
    let Q := ∏ j, (1 - C (mode j : K) * X ^ step) ^ e j
    ∀ n : ℤ, ∑ k ∈ range (Q.natDegree + 1), Q.coeff k *
      (∑ i, ((rho i ^ (n - k) : Kˣ) : K) * (P i).eval ((n - k : ℤ) : K)) = 0 := by
  classical
  dsimp only
  have step_ne : (step : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  let T : Module.End K (ℤ → K) :=
    { toFun := fun u n => u (n - 1)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let Q : K[X] := ∏ j, (1 - C (mode j : K) * X ^ step) ^ e j
  let V (i : I) (n : ℤ) : K := ((rho i ^ n : Kˣ) : K) * (P i).eval (n : K)
  have shift (k : ℕ) (u : ℤ → K) (n : ℤ) : (T ^ k) u n = u (n - k) := by
    induction k generalizing n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      change (T ^ k) u (n - 1) = _
      rw [ih]
      congr 1
      push_cast
      ring
  have single (i : I) :
      (aeval T ((1 - C (mode (index i) : K) * X ^ step) ^ e (index i))) (V i) = 0 := by
    let B : Module.End K (ℤ → K) := 1 - (mode (index i) : K) • (T ^ step)
    let PP : K[X] := (P i).comp (C (step : K) * X)
    have degree_scaled : PP.natDegree < e (index i) := by
      apply lt_of_le_of_lt _ (degree i)
      calc
        PP.natDegree ≤ (P i).natDegree * (C (step : K) * X).natDegree :=
          natDegree_comp_le
        _ ≤ (P i).natDegree * 1 :=
          Nat.mul_le_mul_left _ (by simpa using natDegree_C_mul_le (step : K) (X : K[X]))
        _ = (P i).natDegree := Nat.mul_one _
    have scaled (x : K) : PP.eval (x / (step : K)) = (P i).eval x := by
      simp only [PP, eval_comp, eval_mul, eval_C, eval_X]
      congr 1
      field_simp
    have action (r : ℕ) (n : ℤ) : (B ^ r) (V i) n =
        ((rho i ^ n : Kˣ) : K) *
          (fwdDiff 1)^[r] PP.eval ((n : K) / (step : K) - r) := by
      induction r generalizing n with
      | zero => simpa [V] using congrArg (((rho i ^ n : Kˣ) : K) * ·) (scaled (n : K)).symm
      | succ r ih =>
        rw [pow_succ', Module.End.mul_apply]
        change (B ^ r) _ n - (mode (index i) : K) * (T ^ step) ((B ^ r) _) n = _
        rw [shift, ih, ih]
        have exponent : (mode (index i) : K) * ((rho i ^ (n - step) : Kˣ) : K) =
            ((rho i ^ n : Kˣ) : K) := by
          rw [← mode_power i, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
          congr 2
          omega
        rw [← mul_assoc, exponent, Function.iterate_succ_apply', fwdDiff]
        simp only [Nat.cast_add, Nat.cast_one, Int.cast_sub, Int.cast_natCast]
        have location : (n : K) / (step : K) - ((r : K) + 1) + 1 =
            (n : K) / (step : K) - r := by ring
        have previous_location : ((n : K) - step) / (step : K) - r =
            (n : K) / (step : K) - ((r : K) + 1) := by
          field_simp
          ring
        rw [location, previous_location]
        ring
    have polynomial_action : aeval T (1 - C (mode (index i) : K) * X ^ step) = B := by
      simp [B, Algebra.smul_def]
    rw [map_pow, polynomial_action]
    apply _root_.funext
    intro n
    rw [action, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt degree_scaled]
    simp
  have total : (aeval T Q) (∑ i, V i) = 0 := by
    rw [map_sum]
    apply sum_eq_zero
    intro i _
    have divisor : (1 - C (mode (index i) : K) * X ^ step) ^ e (index i) ∣ Q :=
      dvd_prod_of_mem _ (mem_univ (index i))
    obtain ⟨rest, factor⟩ := divisor
    rw [factor, mul_comm, map_mul, Module.End.mul_apply, single, map_zero]
  intro n
  have at_n := congrFun total n
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply] at at_n
  simp only [Pi.zero_apply] at at_n
  convert at_n using 1
  apply sum_congr rfl
  intro k _
  change _ = Q.coeff k * ((T ^ k) (∑ i, V i) n)
  rw [shift, Finset.sum_apply]

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnBranches
