/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnSequence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnSequence
   mirror-E: none(waiver:generic-mixed-column-sequence)
   anchors: [mathlib/module/Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed]
   utility: none
   digest: Generic mixed branches obey the prescribed Motzkin-column denominator recurrence. -/

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDenominator
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnBranches
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnNegative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnSequence

open Polynomial Finset CiglerMotzkinHankelDefs CiglerMotzkinColumnDefs
open CiglerMotzkinHankelOrthogonal CiglerMotzkinHankelNegative

set_option maxRecDepth 3000 in
/-- Degree induction at zero keeps every fixed node nonzero in the generic scalar field. -/
theorem scalar_model (k m : ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (phi : ℤ[X] →+* K)
      (alpha : Kˣ) (zeta : K),
      Function.Injective phi ∧
      phi X = (alpha : K) + ((alpha⁻¹ : Kˣ) : K) ∧
      (alpha : K) - ((alpha⁻¹ : Kˣ) : K) ≠ 0 ∧
      IsPrimitiveRoot zeta (2 * (k + 1)) ∧
      (∀ i : Fin k, phi X + zeta ^ (i.val + 1) + (zeta ^ (i.val + 1))⁻¹ ≠ 0) ∧
      ∃ (w : Fin k → Kˣ) (a b : Fin k → K),
        (∀ i, (w i : K) = -zeta ^ (i.val + 1)) ∧
        (∀ i n, (-1 : K) ^ n *
          (Polynomial.map (phi.comp specialize.toRingHom) (orthogonal n)).eval
            (phi X + zeta ^ (i.val + 1) + (zeta ^ (i.val + 1))⁻¹) =
            a i * ((w i ^ n : Kˣ) : K) + b i * ((w i ^ (-(n : ℤ)) : Kˣ) : K)) ∧
        (∀ i n, (-1 : K) ^ (n + 1) *
          (Polynomial.map (phi.comp specialize.toRingHom) (backward n)).eval
            (phi X + zeta ^ (i.val + 1) + (zeta ^ (i.val + 1))⁻¹) =
            a i * ((w i ^ (-((n + 1 : ℕ) : ℤ)) : Kˣ) : K) +
              b i * ((w i ^ (n + 1) : Kˣ) : K)) ∧
        ∃ (z : (PowerSeries K)ˣ) (A B : PowerSeries K),
          PowerSeries.constantCoeff (z : PowerSeries K) = alpha ∧
          (∀ n : ℕ, (-1 : PowerSeries K) ^ n *
            (Polynomial.map (phi.comp specialize.toRingHom) (orthogonal n) : PowerSeries K) =
            A * ((z ^ n : (PowerSeries K)ˣ) : PowerSeries K) +
              B * ((z ^ (-(n : ℤ)) : (PowerSeries K)ˣ) : PowerSeries K)) ∧
          (∀ n : ℕ, (-1 : PowerSeries K) ^ (n + 1) *
            (Polynomial.map (phi.comp specialize.toRingHom) (backward n) : PowerSeries K) =
            A * ((z ^ (-((n + 1 : ℕ) : ℤ)) : (PowerSeries K)ˣ) : PowerSeries K) +
              B * ((z ^ (n + 1) : (PowerSeries K)ˣ) : PowerSeries K)) ∧
          let u (j : Fin (m + k)) : (PowerSeries K)ˣ :=
            if hj : j.val < m then
              Units.map (PowerSeries.rescale (j.val : K)).toMonoidHom z
            else Units.map PowerSeries.C.toMonoidHom (w ⟨j.val - m, by omega⟩)
          let aa (j : Fin (m + k)) : PowerSeries K :=
            if hj : j.val < m then PowerSeries.rescale (j.val : K) A
            else PowerSeries.C (a ⟨j.val - m, by omega⟩)
          let bb (j : Fin (m + k)) : PowerSeries K :=
            if hj : j.val < m then PowerSeries.rescale (j.val : K) B
            else PowerSeries.C (b ⟨j.val - m, by omega⟩)
          let v (n : ℤ) : K := PowerSeries.coeff (m.choose 2)
            (Matrix.of fun i j : Fin (m + k) =>
              aa j * ((u j ^ (n + i.val) : (PowerSeries K)ˣ) : PowerSeries K) +
                bb j * ((u j ^ (-(n + i.val)) : (PowerSeries K)ˣ) : PowerSeries K)).det
          let Q := Polynomial.map phi (columnDenominator k m)
          ∀ n : ℤ, ∑ d ∈ range (Q.natDegree + 1), Q.coeff d * v (n - d) = 0 := by
  classical
  let F := FractionRing ℤ[X]
  let K := AlgebraicClosure F
  let phi : ℤ[X] →+* K := (algebraMap F K).comp (algebraMap ℤ[X] F)
  have injective : Function.Injective phi :=
    (RingHom.injective (algebraMap F K)).comp (IsFractionRing.injective ℤ[X] F)
  let quadratic : K[X] := X ^ 2 - C (phi X) * X + 1
  have degree : 2 ≤ quadratic.natDegree :=
    le_natDegree_of_ne_zero (by simp [quadratic, coeff_one])
  obtain ⟨alpha, root⟩ := IsAlgClosed.exists_root quadratic
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp (by omega)))
  have equation : alpha ^ 2 - phi X * alpha + 1 = 0 := by
    simpa [quadratic, IsRoot] using root
  have nonzero : alpha ≠ 0 := by
    intro equal
    simp [equal] at equation
  have parameter : phi X = alpha + alpha⁻¹ := by
    apply (mul_right_inj' nonzero).mp
    rw [mul_add, mul_inv_cancel₀ nonzero]
    linear_combination -equation
  have separated : alpha - alpha⁻¹ ≠ 0 := by
    intro equal
    have inverse : alpha = alpha⁻¹ := sub_eq_zero.mp equal
    have square : alpha ^ 2 = 1 := by
      calc
        alpha ^ 2 = alpha * alpha := pow_two _
        _ = alpha * alpha⁻¹ := congrArg (alpha * ·) inverse
        _ = 1 := mul_inv_cancel₀ nonzero
    have parameter_square : (phi X) ^ 2 = 4 := by
      rw [parameter, ← inverse]
      calc
        (alpha + alpha) ^ 2 = 4 * alpha ^ 2 := by ring
        _ = 4 := by rw [square]; ring
    have impossible : (X : ℤ[X]) ^ 2 = 4 :=
      injective (by simpa only [map_pow, map_ofNat] using parameter_square)
    have coefficient := congrArg (fun p : ℤ[X] => p.coeff 2) impossible
    norm_num at coefficient
  let : NeZero (2 * (k + 1)) := ⟨by omega⟩
  let : NeZero ((2 * (k + 1) : ℕ) : F) := ⟨by exact_mod_cast (by omega :
    2 * (k + 1) ≠ 0)⟩
  obtain ⟨zeta, primitive⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (2 * (k + 1))
  let p (n : ℕ) : (ℤ[X])[X] := Polynomial.map specialize.toRingHom (orthogonal n)
  let v (n : ℕ) : ℤ[X] := (-1) ^ n * (p n).eval 0
  have t_image : specialize tVar = (X : ℤ[X]) := by simp [specialize, tVar]
  have s_image : specialize sVar = (X : ℤ[X]) := by simp [specialize, sVar]
  have at_zero : ∀ n : ℕ, (v n).IsMonicOfDegree n := by
    apply Nat.twoStepInduction
    · simp [v, p, orthogonal]
    · simpa [v, p, orthogonal, s_image] using (isMonicOfDegree_X (R := ℤ))
    · intro n previous current
      have recurrence : v (n + 2) = X * v (n + 1) - v n := by
        dsimp only [v, p]
        rw [orthogonal]
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
          Polynomial.map_C, eval_sub, eval_mul, eval_X, eval_C,
          show specialize.toRingHom tVar = (X : ℤ[X]) from t_image, pow_succ]
        ring
      rw [recurrence]
      have product := (isMonicOfDegree_X (R := ℤ)).mul current
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        product.sub (by rw [previous.natDegree_eq]; omega)
  have evaluation_ne : (p k).eval 0 ≠ 0 := by
    intro equal
    have zero : v k = 0 := by simp [v, equal]
    exact (at_zero k).monic.ne_zero zero
  have mapped_ne : (Polynomial.map phi (p k)).eval 0 ≠ 0 := by
    rw [← map_zero phi, eval_map_apply]
    exact fun equal => evaluation_ne (injective equal)
  have roots := (CiglerMotzkinColumnDenominator.fixed_roots phi k zeta primitive).2.2.2.1
  have root_product : Polynomial.map phi (p k) =
      ∏ i : Fin k, (X - C (phi X + zeta ^ (i.val + 1) +
        (zeta ^ (i.val + 1))⁻¹)) := by
    simpa only [p, Polynomial.map_map] using roots
  have nodes_ne (i : Fin k) :
      phi X + zeta ^ (i.val + 1) + (zeta ^ (i.val + 1))⁻¹ ≠ 0 := by
    intro equal
    apply mapped_ne
    rw [root_product, eval_prod]
    apply prod_eq_zero (mem_univ i)
    simp [equal]
  let psi : Base →+* K := phi.comp specialize.toRingHom
  let r (i : Fin k) : K := phi X + zeta ^ (i.val + 1) + (zeta ^ (i.val + 1))⁻¹
  have psi_t : psi tVar = phi X := by simp [psi, t_image]
  have psi_s : psi sVar = phi X := by simp [psi, s_image]
  have fixed_branch (i : Fin k) : ∃ (w : Kˣ) (a b : K),
      (w : K) = -zeta ^ (i.val + 1) ∧
      (∀ n : ℕ, (-1 : K) ^ n * (Polynomial.map psi (orthogonal n)).eval (r i) =
        a * ((w ^ n : Kˣ) : K) + b * ((w ^ (-(n : ℤ)) : Kˣ) : K)) ∧
      (∀ n : ℕ, (-1 : K) ^ (n + 1) * (Polynomial.map psi (backward n)).eval (r i) =
        a * ((w ^ (-((n + 1 : ℕ) : ℤ)) : Kˣ) : K) +
          b * ((w ^ (n + 1) : Kˣ) : K)) := by
    let beta : K := -zeta ^ (i.val + 1)
    have beta_ne : beta ≠ 0 := neg_ne_zero.mpr
      (pow_ne_zero _ (primitive.ne_zero (by omega)))
    have beta_separated : beta - beta⁻¹ ≠ 0 := by
      intro equal
      have inverse : beta = beta⁻¹ := sub_eq_zero.mp equal
      have square : beta ^ 2 = 1 := by
        calc
          beta ^ 2 = beta * beta := pow_two _
          _ = beta * beta⁻¹ := congrArg (beta * ·) inverse
          _ = 1 := mul_inv_cancel₀ beta_ne
      have impossible : zeta ^ (2 * (i.val + 1)) = 1 := by
        simpa [beta, neg_sq, pow_mul, Nat.mul_comm] using square
      exact primitive.pow_ne_one_of_pos_of_lt (by omega) (by omega) impossible
    let shift : Base →+* K :=
      MvPolynomial.eval₂Hom (Int.castRingHom K) (fun _ : Fin 2 => phi X - r i)
    have shift_t : shift tVar = phi X - r i := by simp [shift, tVar]
    have shift_s : shift sVar = phi X - r i := by simp [shift, sVar]
    have shifted_parameter : shift tVar = beta + beta⁻¹ := by
      rw [shift_t]
      dsimp only [beta, r]
      rw [inv_neg]
      ring
    have forward_translation : ∀ n : ℕ,
        (Polynomial.map shift (orthogonal n)).eval 0 =
          (Polynomial.map psi (orthogonal n)).eval (r i) := by
      apply Nat.twoStepInduction
      · simp [orthogonal]
      · simp only [orthogonal, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.map_C, eval_sub, eval_X, eval_C, shift_s, psi_s]
        ring
      · intro n previous current
        rw [orthogonal]
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
          Polynomial.map_C, eval_sub, eval_mul, eval_X, eval_C,
          shift_t, psi_t, current, previous]
        ring
    have backward_translation : ∀ n : ℕ,
        (Polynomial.map shift (backward n)).eval 0 =
          (Polynomial.map psi (backward n)).eval (r i) := by
      apply Nat.twoStepInduction
      · simp [backward, shift_s, shift_t, psi_s, psi_t]
      · simp only [backward, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
          Polynomial.map_C, Polynomial.map_one, eval_sub, eval_mul, eval_X, eval_C,
          eval_one, map_sub, shift_s, shift_t, psi_s, psi_t]
        ring
      · intro n previous current
        rw [backward]
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
          Polynomial.map_C, eval_sub, eval_mul, eval_X, eval_C,
          shift_t, psi_t, current, previous]
        ring
    obtain ⟨z, constant, relation, difference, unique, forward, back⟩ :=
      CiglerMotzkinHankelBranches.formal_branches shift beta beta_ne beta_separated
        shifted_parameter
    let a : PowerSeries K :=
      (PowerSeries.C (shift sVar) - PowerSeries.X - z⁻¹) * (z - z⁻¹)⁻¹
    let b : PowerSeries K :=
      (z - PowerSeries.C (shift sVar) + PowerSeries.X) * (z - z⁻¹)⁻¹
    have inverse_constant : PowerSeries.constantCoeff z⁻¹ = beta⁻¹ := by
      rw [PowerSeries.constantCoeff_inv, constant]
    let w : Kˣ := Units.mk0 beta beta_ne
    refine ⟨w, PowerSeries.constantCoeff a, PowerSeries.constantCoeff b, rfl, ?_, ?_⟩
    · intro n
      have evaluated := congrArg PowerSeries.constantCoeff (forward n)
      change PowerSeries.constantCoeff
        ((-1 : PowerSeries K) ^ n *
          (Polynomial.map shift (orthogonal n) : PowerSeries K)) =
          PowerSeries.constantCoeff (a * z ^ n + b * (z⁻¹) ^ n) at evaluated
      simp only [map_add, map_mul, map_pow, map_neg, map_one, constant,
        inverse_constant, Polynomial.constantCoeff_coe] at evaluated
      rw [coeff_zero_eq_eval_zero, forward_translation] at evaluated
      simpa only [w, Units.val_pow_eq_pow_val, Units.val_mk0,
        zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, inv_pow] using evaluated
    · intro n
      have evaluated := congrArg PowerSeries.constantCoeff (back n)
      change PowerSeries.constantCoeff
        ((-1 : PowerSeries K) ^ (n + 1) *
          (Polynomial.map shift (backward n) : PowerSeries K)) =
          PowerSeries.constantCoeff (a * (z⁻¹) ^ (n + 1) + b * z ^ (n + 1)) at evaluated
      simp only [map_add, map_mul, map_pow, map_neg, map_one, constant,
        inverse_constant, Polynomial.constantCoeff_coe] at evaluated
      rw [coeff_zero_eq_eval_zero, backward_translation] at evaluated
      simpa only [w, Units.val_pow_eq_pow_val, Units.val_mk0,
        zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, inv_pow] using evaluated
  choose w a b mode forward back using fixed_branch
  refine ⟨K, inferInstance, inferInstance, phi, Units.mk0 alpha nonzero, zeta,
    injective, by simpa using parameter, by simpa using separated, primitive, nodes_ne,
    w, a, b, mode, forward, back, ?_⟩
  obtain ⟨z, constant, relation, difference, unique, zero_forward, zero_back⟩ :=
    CiglerMotzkinHankelBranches.formal_branches psi alpha nonzero separated
      (psi_t.trans parameter)
  obtain ⟨zU, z_value⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr
    (constant ▸ isUnit_iff_ne_zero.mpr nonzero)
  have z_inverse : ((zU⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) = z⁻¹ := by
    symm
    apply (PowerSeries.inv_eq_iff_mul_eq_one (by simpa [constant] using nonzero)).mpr
    rw [← z_value]
    simp
  let A : PowerSeries K :=
    (PowerSeries.C (psi sVar) - PowerSeries.X - z⁻¹) * (z - z⁻¹)⁻¹
  let B : PowerSeries K :=
    (z - PowerSeries.C (psi sVar) + PowerSeries.X) * (z - z⁻¹)⁻¹
  refine ⟨zU, A, B, by simpa [z_value] using constant, ?_, ?_, ?_⟩
  · intro n
    simpa only [A, B, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val,
      z_inverse, z_value] using zero_forward n
  · intro n
    simpa only [A, B, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val,
      z_inverse, z_value] using zero_back n
  · dsimp only
    let alphaU : Kˣ := Units.mk0 alpha nonzero
    let u (j : Fin (m + k)) : (PowerSeries K)ˣ :=
      if hj : j.val < m then Units.map (PowerSeries.rescale (j.val : K)).toMonoidHom zU
      else Units.map PowerSeries.C.toMonoidHom (w ⟨j.val - m, by omega⟩)
    let aa (j : Fin (m + k)) : PowerSeries K :=
      if hj : j.val < m then PowerSeries.rescale (j.val : K) A
      else PowerSeries.C (a ⟨j.val - m, by omega⟩)
    let bb (j : Fin (m + k)) : PowerSeries K :=
      if hj : j.val < m then PowerSeries.rescale (j.val : K) B
      else PowerSeries.C (b ⟨j.val - m, by omega⟩)
    let Z : Finset (Fin (m + k)) := univ.filter (fun j => j.val < m)
    have constants (j : Fin (m + k)) (hj : j ∈ Z) :
        PowerSeries.constantCoeff (u j : PowerSeries K) = (alphaU : K) := by
      have below := (mem_filter.mp hj).2
      simp only [u, dif_pos below]
      change PowerSeries.constantCoeff (PowerSeries.rescale (j.val : K)
        (zU : PowerSeries K)) = alpha
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale]
      simpa [z_value] using constant
    have Z_map : Z = (univ : Finset (Fin m)).map (Fin.castAddEmb k) := by
      ext j
      constructor
      · intro member
        have below := (mem_filter.mp member).2
        exact mem_map.mpr ⟨⟨j.val, below⟩, mem_univ _, Fin.ext rfl⟩
      · intro member
        obtain ⟨i, _, equal⟩ := mem_map.mp member
        subst j
        simp [Z]
    have Z_card : Z.card = m := by rw [Z_map, card_map, card_univ, Fintype.card_fin]
    obtain ⟨P, bounds, expansion⟩ :=
      CiglerMotzkinColumnBranches.mixed_branch_coefficients (m + k) Z u alphaU
        constants aa bb
    let rho (S : Finset (Fin (m + k))) : Kˣ :=
      Units.map PowerSeries.constantCoeff.toMonoidHom
        (∏ j, if j ∈ S then (u j)⁻¹ else u j)
    let index (S : Finset (Fin (m + k))) : Fin (m + 1) :=
      ⟨(Z ∩ S).card, by
        have bound := card_le_card (inter_subset_left (s₂ := S) (s₁ := Z))
        rw [Z_card] at bound
        omega⟩
    let eps : Kˣ := (-1) ^ (k + 1).choose 2
    let modeU (j : Fin (m + 1)) : Kˣ :=
      eps * alphaU ^ ((k + 1 : ℕ) * ((m : ℤ) - 2 * j.val))
    have mapped (j : Fin (m + k)) :
        Units.map PowerSeries.constantCoeff.toMonoidHom (u j) =
          if hj : j.val < m then alphaU else w ⟨j.val - m, by omega⟩ := by
      apply Units.ext
      by_cases below : j.val < m
      · simp only [dif_pos below]
        change PowerSeries.constantCoeff (u j : PowerSeries K) = (alphaU : K)
        exact constants j (by simp [Z, below])
      · simp [u, below]
    have mode_power (S : Finset (Fin (m + k))) : rho S ^ (k + 1) = modeU (index S) := by
      have count : (Z ∩ S).card =
          (univ.filter (fun i : Fin m => Fin.castAdd k i ∈ S)).card := by
        rw [← filter_mem_eq_inter, Z_map, filter_map, card_map]
        rfl
      have fixed_power (i : Fin k) : (w i) ^ (k + 1) =
          (-1 : Kˣ) ^ (k + 1 + (i.val + 1)) := by
        apply Units.ext
        change (w i : K) ^ (k + 1) = (-1 : K) ^ (k + 1 + (i.val + 1))
        rw [mode i, neg_pow,
          (CiglerMotzkinColumnDenominator.fixed_roots phi k zeta primitive).2.1 i]
        exact (pow_add (-1 : K) (k + 1) (i.val + 1)).symm
      have fixed_inverse (i : Fin k) : ((w i)⁻¹) ^ (k + 1) =
          (-1 : Kˣ) ^ (k + 1 + (i.val + 1)) := by
        rw [inv_pow, fixed_power, ← inv_pow]
        simp
      have zero_product :
          (∏ i : Fin m, (if Fin.castAdd k i ∈ S then alphaU⁻¹ else alphaU) ^ (k + 1)) =
            alphaU ^ ((k + 1 : ℕ) * ((m : ℤ) - 2 * (Z ∩ S).card)) := by
        rw [prod_pow, prod_ite]
        simp only [prod_const]
        have complement :
            (univ.filter (fun i : Fin m => Fin.castAdd k i ∉ S)).card =
              m - (univ.filter (fun i : Fin m => Fin.castAdd k i ∈ S)).card := by
          have total := card_filter_add_card_filter_not
            (s := (univ : Finset (Fin m))) (p := fun i => Fin.castAdd k i ∈ S)
          simp only [card_univ, Fintype.card_fin] at total
          omega
        rw [complement, inv_pow]
        simp only [← zpow_natCast]
        rw [← zpow_neg, ← zpow_add, ← zpow_mul]
        congr 1
        rw [count]
        have bound : (univ.filter (fun i : Fin m => Fin.castAdd k i ∈ S)).card ≤ m := by
          simpa only [card_univ, Fintype.card_fin] using
            card_le_card (filter_subset (fun i : Fin m => Fin.castAdd k i ∈ S) univ)
        rw [Nat.cast_sub bound]
        push_cast
        ring
      have fixed_product :
          (∏ i : Fin k, (if Fin.natAdd m i ∈ S then (w i)⁻¹ else w i) ^ (k + 1)) = eps := by
        have summand (i : Fin k) :
            (if Fin.natAdd m i ∈ S then (w i)⁻¹ else w i) ^ (k + 1) =
              (-1 : Kˣ) ^ (k + 1 + (i.val + 1)) := by
          split_ifs <;> [exact fixed_inverse i; exact fixed_power i]
        rw [prod_congr rfl (fun i _ => summand i), prod_pow_eq_pow_sum, sum_add_distrib,
          sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        have triangular (l : ℕ) : (∑ i : Fin l, (i.val + 1)) = (l + 1).choose 2 := by
          induction l with
          | zero => simp
          | succ l ih =>
            rw [Fin.sum_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last]
            rw [ih]
            have step : (l + 1 + 1).choose 2 = (l + 1) + (l + 1).choose 2 := by
              simpa only [Nat.choose_one_right] using Nat.choose_succ_succ (l + 1) 1
            omega
        rw [triangular k, pow_add]
        have even : Even (k * (k + 1)) := by
          exact Nat.even_mul_succ_self k
        rw [even.neg_one_pow, one_mul]
      dsimp only [rho]
      rw [map_prod]
      simp only [apply_ite, map_inv, mapped]
      rw [← prod_pow, Fin.prod_univ_add]
      simp only [Fin.val_castAdd, Fin.isLt, dif_pos, Fin.val_natAdd,
        show ∀ i : Fin k, ¬ m + i.val < m from by omega, Nat.add_sub_cancel_left]
      change (∏ i : Fin m,
        (if Fin.castAdd k i ∈ S then alphaU⁻¹ else alphaU) ^ (k + 1)) *
          (∏ i : Fin k,
            (if Fin.natAdd m i ∈ S then (w i)⁻¹ else w i) ^ (k + 1)) = _
      rw [zero_product, fixed_product]
      exact mul_comm _ _
    let e (j : Fin (m + 1)) : ℕ := 1 + j.val * (m - j.val)
    let Q : K[X] := ∏ j, (1 - C (modeU j : K) * X ^ (k + 1)) ^ e j
    have Q_eq : Q = Polynomial.map phi (columnDenominator k m) := by
      rw [(CiglerMotzkinColumnDenominator.mode_denominator phi alphaU
        (by simpa [alphaU] using parameter) k m).1]
      dsimp only [Q, e, modeU, eps]
      simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
        Units.val_zpow_eq_zpow_val] using
        Fin.prod_univ_eq_prod_range (fun j : ℕ =>
          (1 - C ((((-1 : Kˣ) ^ (k + 1).choose 2 *
            alphaU ^ ((k + 1 : ℕ) * ((m : ℤ) - 2 * j))) : K)) * X ^ (k + 1)) ^
              (1 + j * (m - j))) (m + 1)
    have recurrent := CiglerMotzkinColumnBranches.grouped_recurrence (k + 1) (by omega)
      index rho modeU mode_power P e (fun S => by
        have bound := bounds S
        rw [Z_card] at bound
        change (P S).natDegree < 1 + (Z ∩ S).card * (m - (Z ∩ S).card)
        omega)
    intro n
    rw [← Q_eq]
    convert recurrent n using 1
    apply sum_congr rfl
    intro d _
    rw [← expansion (n - d), Z_card]

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnSequence
