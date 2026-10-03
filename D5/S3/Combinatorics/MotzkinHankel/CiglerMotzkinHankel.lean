/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankel
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Tactic, mathlib/module/Mathlib.Algebra.Group.ForwardDiff]
   utility: none
   digest: Proves Cigler's boundary-weighted Motzkin Hankel generating-function conjecture. -/
import Mathlib.Tactic
import Mathlib.Algebra.Group.ForwardDiff
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelConfluence
open Polynomial Finset
open scoped fwdDiff
open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs
open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelOrthogonal
open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelNegative
open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelBranches
open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelConfluence
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankel
set_option maxRecDepth 3000 in
set_option maxHeartbeats 4000000 in
theorem result : CiglerMotzkinHankelDefs.claim := by
  classical
  have scalar : ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (φ : Base →+* K) (α : K), Function.Injective φ ∧ α ≠ 0 ∧
      α - α⁻¹ ≠ 0 ∧ φ tVar = α + α⁻¹ := by
    classical
    let F := FractionRing Base
    let K := AlgebraicClosure F
    let φ : Base →+* K := (algebraMap F K).comp (algebraMap Base F)
    have injective : Function.Injective φ :=
      (RingHom.injective (algebraMap F K)).comp (IsFractionRing.injective Base F)
    let p : K[X] := X ^ 2 - C (φ tVar) * X + 1
    have degree : 2 ≤ p.natDegree := le_natDegree_of_ne_zero (by simp [p, coeff_one])
    obtain ⟨α, root⟩ := IsAlgClosed.exists_root p
      (ne_of_gt (natDegree_pos_iff_degree_pos.mp (by omega)))
    have equation : α ^ 2 - φ tVar * α + 1 = 0 := by simpa [p, IsRoot] using root
    have nonzero : α ≠ 0 := by intro h; simp [h] at equation
    have parameter : φ tVar = α + α⁻¹ := by
      apply (mul_right_inj' nonzero).mp
      rw [mul_add, mul_inv_cancel₀ nonzero]
      linear_combination -equation
    have separated : α - α⁻¹ ≠ 0 := by
      intro h
      have equal : α = α⁻¹ := sub_eq_zero.mp h
      have square : α ^ 2 = 1 := by
        calc α ^ 2 = α * α := pow_two α
             _ = α * α⁻¹ := congrArg (α * ·) equal
             _ = 1 := mul_inv_cancel₀ nonzero
      have tsquare : (φ tVar) ^ 2 = 4 := by
        rw [parameter, ← equal]
        calc (α + α) ^ 2 = 4 * α ^ 2 := by ring
             _ = 4 := by rw [square]; ring
      have original : tVar ^ 2 = (4 : Base) :=
        injective (by simpa only [map_pow, map_ofNat] using tsquare)
      have evaluated := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℤ))) original
      norm_num [tVar, map_ofNat] at evaluated
    exact ⟨K, inferInstance, inferInstance, φ, α, injective, nonzero, separated, parameter⟩
  obtain ⟨K, field, characteristic, phi, alpha, injective, nonzero, separated, parameter⟩ := scalar
  let : Field K := field
  let : CharZero K := characteristic
  have branches (phi : Base →+* K) (alpha : K)
      (nonzero : alpha ≠ 0) (separated : alpha - alpha⁻¹ ≠ 0)
      (parameter : phi tVar = alpha + alpha⁻¹) :
      ∃ (z : (PowerSeries K)ˣ) (a b : PowerSeries K),
        PowerSeries.constantCoeff (z : PowerSeries K) = alpha ∧
        let q (n : ℤ) := a * ((z ^ n : (PowerSeries K)ˣ) : PowerSeries K) +
          b * ((z ^ (-n) : (PowerSeries K)ˣ) : PowerSeries K)
        (∀ r : ℕ, q r = (-1 : PowerSeries K) ^ r * Polynomial.map phi (orthogonal r)) ∧
        (∀ r : ℕ, q (-(r + 1 : ℕ)) =
          (-1 : PowerSeries K) ^ (r + 1) * Polynomial.map phi (backward r)) := by
    obtain ⟨z, constant, relation, difference, unique, forward, back⟩ :=
      formal_branches phi alpha nonzero separated parameter
    have unit : IsUnit z := PowerSeries.isUnit_iff_constantCoeff.mpr
      (constant ▸ isUnit_iff_ne_zero.mpr nonzero)
    obtain ⟨u, value⟩ := unit
    have inverse : ((u⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) = z⁻¹ := by
      symm
      apply (PowerSeries.inv_eq_iff_mul_eq_one (by simpa [constant] using nonzero)).mpr
      rw [← value]
      simp
    let a := (PowerSeries.C (phi sVar) - PowerSeries.X - z⁻¹) * (z - z⁻¹)⁻¹
    let b := (z - PowerSeries.C (phi sVar) + PowerSeries.X) * (z - z⁻¹)⁻¹
    refine ⟨u, a, b, by simpa [value] using constant, ?_, ?_⟩
    · intro r
      simpa only [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val,
        inverse, value, a, b] using (forward r).symm
    · intro r
      simp only [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val,
        inv_inv, inverse, value]
      simpa only [a, b] using (back r).symm
  have confluence (size : ℕ)
      (z : (PowerSeries K)ˣ) (alpha : Kˣ)
      (constant : PowerSeries.constantCoeff (z : PowerSeries K) = alpha)
      (a b : PowerSeries K) :
      ∃ P : Finset (Fin size) → K[X],
        (∀ S, (P S).natDegree ≤ S.card * (size - S.card)) ∧
        ∀ n : ℤ,
          (Matrix.of fun row column : Fin size => PowerSeries.coeff column.val
            (a * ((z ^ (n + row.val) : (PowerSeries K)ˣ) : PowerSeries K) +
              b * ((z ^ (-(n + row.val)) : (PowerSeries K)ˣ) : PowerSeries K))).det =
            ∑ S : Finset (Fin size),
              ((alpha ^ (((size : ℤ) - 2 * S.card) * n) : Kˣ) : K) *
                (P S).eval (n : K) := by
    classical
    have grouping (size : ℕ)
        (u : Fin size → (PowerSeries K)ˣ) (α : Kˣ)
        (constant : ∀ i, PowerSeries.constantCoeff (u i : PowerSeries K) = α)
        (a b : Fin size → PowerSeries K) :
        ∃ P : Finset (Fin size) → K[X],
          (∀ S, (P S).natDegree ≤ S.card * (size - S.card)) ∧
          ∀ n : ℤ, PowerSeries.coeff (size.choose 2)
            (Matrix.of fun row column : Fin size =>
              a column * ((u column ^ (n + row.val) : (PowerSeries K)ˣ) : PowerSeries K) +
              b column * ((u column ^ (-(n + row.val)) : (PowerSeries K)ˣ) : PowerSeries K)).det =
            ∑ S : Finset (Fin size),
              ((α ^ (((size : ℤ) - 2 * S.card) * n) : Kˣ) : K) * (P S).eval (n : K) := by
      classical
      let w (S : Finset (Fin size)) (i : Fin size) := if i ∈ S then (u i)⁻¹ else u i
      let h (S : Finset (Fin size)) (i : Fin size) := if i ∈ S then b i else a i
      let v (S : Finset (Fin size)) : (PowerSeries K)ˣ := ∏ i, w S i
      let β (S : Finset (Fin size)) : Kˣ := α ^ ((size : ℤ) - 2 * S.card)
      let pairs : Finset (Fin size × Fin size) :=
        (univ ×ˢ univ).filter (fun p => p.1 < p.2)
      let same (S : Finset (Fin size)) := pairs.filter (fun p => (p.1 ∈ S ↔ p.2 ∈ S))
      have constant_unit (i : Fin size) :
          Units.map PowerSeries.constantCoeff.toMonoidHom (u i) = α :=
        Units.ext (constant i)
      have branch_constant (S : Finset (Fin size)) (i : Fin size) :
          PowerSeries.constantCoeff (w S i : PowerSeries K) =
            (if i ∈ S then ((α⁻¹ : Kˣ) : K) else (α : K)) := by
        by_cases inside : i ∈ S
        · have inverse := congrArg Units.val
            (show Units.map PowerSeries.constantCoeff.toMonoidHom ((u i)⁻¹) = α⁻¹ by
              rw [map_inv, constant_unit])
          change PowerSeries.constantCoeff (((u i)⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) =
            ((α⁻¹ : Kˣ) : K) at inverse
          simpa only [w, inside, if_true] using inverse
        · simpa only [w, inside, if_false] using constant i
      have product_constant (S : Finset (Fin size)) :
          PowerSeries.constantCoeff (v S : PowerSeries K) = β S := by
        have mapped : Units.map PowerSeries.constantCoeff.toMonoidHom (v S) = β S := by
          dsimp only [v, w]; simp only [map_prod, apply_ite, map_inv, constant_unit]
          rw [prod_ite]
          have complement : univ.filter (fun i => i ∉ S) = Sᶜ := by ext i; simp
          rw [filter_mem_eq_inter, univ_inter, complement]
          simp only [prod_const, card_compl, Fintype.card_fin]
          dsimp only [β]; rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
          congr 1
          have bound : S.card ≤ size := by simpa using S.card_le_univ
          omega
        exact congrArg Units.val mapped
      have pair_count (S : Finset (Fin size)) :
          (same S).card = S.card.choose 2 + (size - S.card).choose 2 := by
        have partition : same S =
            ((S ×ˢ S).filter (fun p => p.1 < p.2)) ∪
              ((Sᶜ ×ˢ Sᶜ).filter (fun p => p.1 < p.2)) := by
          ext p
          simp only [same, pairs, mem_filter, mem_product, mem_univ, true_and,
            mem_union, mem_compl]
          tauto
        have disjoint : Disjoint
            ((S ×ˢ S).filter (fun p => p.1 < p.2))
            ((Sᶜ ×ˢ Sᶜ).filter (fun p => p.1 < p.2)) := by
          rw [Finset.disjoint_left]
          intro p left right
          have positive := (mem_product.mp (mem_filter.mp left).1).1
          have negative := (mem_product.mp (mem_filter.mp right).1).1
          exact (mem_compl.mp negative) positive
        rw [partition, card_union_of_disjoint disjoint, card_product_filter_lt,
          card_product_filter_lt, card_compl, Fintype.card_fin]
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
          (same S).card + S.card * (size - S.card) = size.choose 2 := by
        rw [pair_count, ← triangle_add]
        congr 1
        have bound : S.card ≤ size := by simpa using S.card_le_univ
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
                rw [map_sub, branch_constant, branch_constant]
                have matching := (mem_filter.mp hp).2
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
          ∃ Q : K[X], Q.natDegree ≤ S.card * (size - S.card) ∧ ∀ n : ℤ,
            PowerSeries.coeff (size.choose 2)
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
          unit_power_coefficients normalized normalized_constant H (S.card * (size - S.card))
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
          show size.choose 2 = (same S).card + S.card * (size - S.card) from (order_split S).symm,
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
      dsimp only [β]; rw [← zpow_mul]
    let c (i : Fin size) : K := i.val
    let u (i : Fin size) : (PowerSeries K)ˣ :=
      Units.map (PowerSeries.rescale (c i)).toMonoidHom z
    have constants (i : Fin size) : PowerSeries.constantCoeff (u i : PowerSeries K) =
        (alpha : K) := by
      change PowerSeries.constantCoeff (PowerSeries.rescale (c i) (z : PowerSeries K)) = _
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale]
      simpa using constant
    obtain ⟨P, bounds, expansion⟩ := grouping size u alpha constants
      (fun i => PowerSeries.rescale (c i) a) (fun i => PowerSeries.rescale (c i) b)
    let delta : K := (Matrix.vandermonde c).det
    have delta_ne : delta ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr (by
      intro i j h; apply Fin.ext
      exact Nat.cast_injective h)
    refine ⟨fun S => C delta⁻¹ * P S, ?_, ?_⟩
    · intro S
      exact (natDegree_C_mul_le _ _).trans (bounds S)
    · intro n
      have confluent := (alternant_coefficients size
        (fun row : Fin size => a * ((z ^ (n + row.val) : (PowerSeries K)ˣ) :
          PowerSeries K) + b * ((z ^ (-(n + row.val)) : (PowerSeries K)ˣ) :
            PowerSeries K)) c).2
      have rescaled (r : ℤ) (i : Fin size) :
          PowerSeries.rescale (c i) ((z ^ r : (PowerSeries K)ˣ) : PowerSeries K) =
            ((u i ^ r : (PowerSeries K)ˣ) : PowerSeries K) := by
        exact congrArg Units.val (map_zpow
          (Units.map (PowerSeries.rescale (c i)).toMonoidHom) z r)
      simp_rw [map_add, map_mul, rescaled] at confluent
      rw [expansion] at confluent
      have scaled := congrArg (delta⁻¹ * ·) confluent
      rw [← mul_assoc, inv_mul_cancel₀ delta_ne, one_mul] at scaled; simp only [map_add]
      rw [← scaled, mul_sum]; apply sum_congr rfl
      intro S _; simp only [eval_mul, eval_C]
      ring
  have identification (phi : Base →+* K) (injective : Function.Injective phi)
      (m : ℕ) (q : ℤ → PowerSeries K)
      (forward : ∀ r : ℕ, q r = (-1 : PowerSeries K) ^ r * Polynomial.map phi (orthogonal r))
      (back : ∀ r : ℕ, q (-(r + 1 : ℕ)) =
        (-1 : PowerSeries K) ^ (r + 1) * Polynomial.map phi (backward r)) :
      let U (n : ℤ) := (-1 : K) ^ m.choose 2 *
        (Matrix.of fun row column : Fin m => PowerSeries.coeff column.val (q (n + row.val))).det
      (∀ n : ℕ, U n = phi (hankelDet m n)) ∧
      (∀ a : ℕ, 1 ≤ a → a < m → U (-(a : ℤ)) = 0) ∧ U (-(m : ℤ)) ≠ 0 := by
    classical
    dsimp only
    have index_sum : (∑ i : Fin m, i.val) = m.choose 2 := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih, Nat.choose_succ_succ, Nat.choose_one_right]
        change m.choose 2 + m = m + m.choose 2
        omega
    have signs (a : ℕ) (M : Fin m → Fin m → K) :
        (-1 : K) ^ m.choose 2 *
          (Matrix.of fun i j => (-1 : K) ^ (a + i.val) * M i j).det =
            (-1 : K) ^ (a * m) * (Matrix.of M).det := by
      have scaled := Matrix.det_mul_column (fun i : Fin m => (-1 : K) ^ (a + i.val))
        (Matrix.of M)
      simp only [Matrix.of_apply] at scaled
      rw [scaled, prod_pow_eq_pow_sum, sum_add_distrib,
        sum_const, card_univ, Fintype.card_fin, smul_eq_mul, index_sum,
        ← mul_assoc, ← pow_add]
      have exponent : m.choose 2 + (m * a + m.choose 2) = a * m + 2 * m.choose 2 := by ring
      rw [exponent, pow_add, pow_mul]
      simp
    have coefficient (P : Base[X]) (r h : ℕ) : PowerSeries.coeff h
        ((-1 : PowerSeries K) ^ r * (Polynomial.map phi P : PowerSeries K)) =
          (-1 : K) ^ r * phi (P.coeff h) := by
      rw [show (-1 : PowerSeries K) ^ r = PowerSeries.C ((-1 : K) ^ r) by simp]
      rw [PowerSeries.coeff_C_mul, Polynomial.coeff_coe, coeff_map]
    constructor
    · intro n
      have matrix : (Matrix.of fun row column : Fin m =>
          PowerSeries.coeff column.val (q ((n : ℤ) + row.val))) =
        Matrix.of (fun row column : Fin m =>
          (-1 : K) ^ (n + row.val) * phi ((orthogonal (n + row.val)).coeff column)) := by
        ext row column; simp only [Matrix.of_apply]
        rw [show ((n : ℤ) + row.val) = ((n + row.val : ℕ) : ℤ) by omega,
          forward, coefficient]
      rw [matrix, signs n (fun row column : Fin m =>
        phi ((orthogonal (n + row.val)).coeff column))]
      rw [hankelDet_coefficients, map_mul, map_pow, map_neg, map_one, phi.map_det]; rfl
    · have negative_matrix (a : ℕ) : (Matrix.of fun row column : Fin m =>
          PowerSeries.coeff column.val (q (-(a : ℤ) + row.val))) =
        Matrix.of (fun row column : Fin m => (-1 : K) ^ (a + row.val) *
          phi ((if row.val < a then backward (a - 1 - row.val)
            else orthogonal (row.val - a)).coeff column)) := by
        ext row column; simp only [Matrix.of_apply]
        by_cases negative : row.val < a
        · rw [if_pos negative]
          have index : -(a : ℤ) + row.val = -((a - 1 - row.val + 1 : ℕ) : ℤ) := by omega
          rw [index, back, coefficient]
          congr 1
          apply neg_one_pow_congr
          rw [even_iff_two_dvd, even_iff_two_dvd]
          omega
        · rw [if_neg negative]
          have index : -(a : ℤ) + row.val = ((row.val - a : ℕ) : ℤ) := by omega
          rw [index, forward, coefficient]
          congr 1
          apply neg_one_pow_congr
          rw [even_iff_two_dvd, even_iff_two_dvd]
          omega
      constructor
      · intro a ha hm
        rw [negative_matrix, signs a (fun row column : Fin m =>
          phi ((if row.val < a then backward (a - 1 - row.val)
            else orthogonal (row.val - a)).coeff column))]
        have zero := (negative_determinants m).1 a ha hm
        have mapped := congrArg phi zero
        rw [phi.map_det, map_zero] at mapped
        rw [show (Matrix.of fun row column : Fin m =>
            phi ((if row.val < a then backward (a - 1 - row.val)
              else orthogonal (row.val - a)).coeff column)).det = 0 from mapped, mul_zero]
      · rw [negative_matrix, signs m (fun row column : Fin m =>
          phi ((if row.val < m then backward (m - 1 - row.val)
            else orthogonal (row.val - m)).coeff column))]
        have unmixed : (Matrix.of fun row column : Fin m =>
            phi ((if row.val < m then backward (m - 1 - row.val)
              else orthogonal (row.val - m)).coeff column)).det =
          (Matrix.of fun row column : Fin m =>
            phi ((backward (m - 1 - row.val)).coeff column)).det := by
          congr 1
          ext row column; simp only [Matrix.of_apply, if_pos row.isLt]
        rw [unmixed, show (-1 : K) ^ (m * m) = (-1 : K) ^ m by
          apply neg_one_pow_congr; simp [Nat.even_mul]]
        have nonzero := (negative_determinants m).2.2
        have identity := congrArg phi (negative_determinants m).2.1
        rw [map_mul, map_pow, map_neg, map_one, phi.map_det] at identity
        change (-1 : K) ^ m * (Matrix.of fun row column : Fin m =>
          phi ((backward (m - 1 - row.val)).coeff column)).det = _ at identity
        rw [identity]; exact fun h => nonzero (injective (by simpa using h))
  have annihilator {I J : Type} [Fintype I] [Fintype J]
      (index : I → J) (rho : J → Kˣ)
      (P : I → K[X]) (e : J → ℕ) (degree : ∀ i, (P i).natDegree < e (index i)) :
      let Q := ∏ j, (1 - C (rho j : K) * X) ^ e j
      ∀ n : ℤ, ∑ k ∈ range (Q.natDegree + 1), Q.coeff k *
        (∑ i, (rho (index i) ^ (n - k) : Kˣ) * (P i).eval ((n - k : ℤ) : K)) = 0 := by
    classical
    dsimp only
    let T : Module.End K (ℤ → K) :=
      { toFun := fun u n => u (n - 1)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    let Q : K[X] := ∏ j, (1 - C (rho j : K) * X) ^ e j
    let V (i : I) (n : ℤ) : K := (rho (index i) ^ n : Kˣ) * (P i).eval (n : K)
    have single (i : I) : (aeval T ((1 - C (rho (index i) : K) * X) ^ e (index i))) (V i) = 0 := by
      let B : Module.End K (ℤ → K) := 1 - (rho (index i) : K) • T
      have action (r : ℕ) (n : ℤ) : (B ^ r) (V i) n =
          (rho (index i) ^ n : Kˣ) * (fwdDiff 1)^[r] (P i).eval ((n : K) - r) := by
        induction r generalizing n with
        | zero => simp [V]
        | succ r ih =>
          rw [pow_succ', Module.End.mul_apply]
          change (B ^ r) _ n - (rho (index i) : K) * (B ^ r) _ (n - 1) = _; rw [ih, ih]
          have exponent : (rho (index i) : K) * ((rho (index i) ^ (n - 1) : Kˣ) : K) =
              (rho (index i) ^ n : Kˣ) := by
            simpa using congrArg Units.val (zpow_add (rho (index i)) (1 : ℤ) (n - 1)).symm
          rw [← mul_assoc, exponent, Function.iterate_succ_apply', fwdDiff]
          simp only [Nat.cast_add, Nat.cast_one, Int.cast_sub, Int.cast_one]
          have location : (n : K) - ((r : K) + 1) + 1 = (n : K) - r := by ring
          rw [location]; ring
      have polynomial_action : aeval T (1 - C (rho (index i) : K) * X) = B := by
        simp [B, Algebra.smul_def]
      rw [map_pow, polynomial_action]; apply _root_.funext
      intro n; rw [action, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (degree i)]
      simp
    have total : (aeval T Q) (∑ i, V i) = 0 := by
      rw [map_sum]; apply sum_eq_zero
      intro i _
      have divisor : (1 - C (rho (index i) : K) * X) ^ e (index i) ∣ Q :=
        dvd_prod_of_mem _ (mem_univ (index i))
      obtain ⟨rest, factor⟩ := divisor
      rw [factor, mul_comm, map_mul, Module.End.mul_apply, single, map_zero]
    have shift (k : ℕ) (u : ℤ → K) (n : ℤ) : (T ^ k) u n = u (n - k) := by
      induction k generalizing n with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        change (T ^ k) u (n - 1) = _; rw [ih]
        congr 1
        push_cast
        ring
    intro n
    have at_n := congrFun total n
    rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply] at at_n
    simp only [Pi.zero_apply] at at_n
    convert at_n using 1
    apply sum_congr rfl
    intro k _
    change _ = (Q.coeff k) * ((T ^ k) (∑ i, V i) n); rw [shift, Finset.sum_apply]
  have split_denominator (phi : Base →+* K) (alpha : Kˣ)
      (parameter : phi tVar = (alpha : K) + ((alpha⁻¹ : Kˣ) : K)) (m : ℕ) :
      Polynomial.map phi (denominator m) = ∏ j ∈ range (m + 1),
        (1 - C ((alpha ^ ((m : ℤ) - 2 * j) : Kˣ) : K) * X) ^ (1 + j * (m - j)) := by
    classical
    have lucas_formula (r : ℕ) : phi (lucas r) =
        ((alpha ^ r : Kˣ) : K) + ((alpha⁻¹ ^ r : Kˣ) : K) := by
      induction r using Nat.twoStepInduction with
      | zero => norm_num [lucas, map_ofNat]
      | one => simpa [lucas] using parameter
      | more r previous current =>
        rw [lucas, map_sub, map_mul, parameter, current, previous]
        simp only [pow_succ, Units.val_mul]
        have inverse : (alpha : K) * ((alpha⁻¹ : Kˣ) : K) = 1 := by simp
        linear_combination ((alpha ^ r : Kˣ) + (alpha⁻¹ ^ r : Kˣ)) * inverse
    let f (j : ℕ) : K[X] :=
      (1 - C ((alpha ^ ((m : ℤ) - 2 * j) : Kˣ) : K) * X) ^ (1 + j * (m - j))
    have pair (j : ℕ) (hj : j < m / 2 + 1) :
        Polynomial.map phi (factorA (m - 2 * j) ^ (1 + j * (m - j))) =
          f j * (if m = 2 * j then 1 else f (m - j)) := by
      have bounded : 2 * j ≤ m := by omega
      rw [Polynomial.map_pow]
      by_cases central : m = 2 * j
      · simp only [central, Nat.sub_self, factorA]
        dsimp only [f]; rw [show ((m : ℤ) - 2 * j) = 0 by omega]
        simp [central]
      · have positive : m - 2 * j ≠ 0 := by omega
        rw [factorA, if_neg positive, Polynomial.map_add, Polynomial.map_sub,
          Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
          Polynomial.map_pow, Polynomial.map_X, lucas_formula]
        have exponent : (alpha ^ ((m : ℤ) - 2 * j) : Kˣ) = alpha ^ (m - 2 * j) := by
          rw [← zpow_natCast]
          congr 1
          omega
        have opposite : (alpha ^ ((m : ℤ) - 2 * ((m - j : ℕ) : ℤ)) : Kˣ) =
            alpha⁻¹ ^ (m - 2 * j) := by
          rw [inv_pow, ← zpow_natCast, ← zpow_neg]
          congr 1
          omega
        have weights : 1 + (m - j) * (m - (m - j)) = 1 + j * (m - j) := by
          rw [Nat.sub_sub_self (by omega), Nat.mul_comm]
        dsimp only [f]; rw [if_neg central, exponent, opposite, weights, ← mul_pow]
        congr 1
        have inverse : ((alpha ^ (m - 2 * j) : Kˣ) : K) *
            ((alpha⁻¹ ^ (m - 2 * j) : Kˣ) : K) = 1 := by
          rw [← Units.val_mul, ← mul_pow]
          simp
        rw [C_add]
        have constant_product :
            C ((alpha ^ (m - 2 * j) : Kˣ) : K) *
              C ((alpha⁻¹ ^ (m - 2 * j) : Kˣ) : K) = (1 : K[X]) := by
          rw [← C_mul, inverse, C_1]
        linear_combination -X ^ 2 * constant_product
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
    rw [denominator, Polynomial.map_prod]
    have paired : (∏ j ∈ range (m / 2 + 1),
        Polynomial.map phi (factorA (m - 2 * j) ^ (1 + j * (m - j)))) =
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
  have degree_denominator (alpha : Kˣ) (m : ℕ) :
      let Q : K[X] := ∏ j ∈ range (m + 1),
        (1 - C ((alpha ^ ((m : ℤ) - 2 * j) : Kˣ) : K) * X) ^ (1 + j * (m - j))
      Q.natDegree = m + 1 + (m + 1).choose 3 ∧ Q.leadingCoeff ≠ 0 := by
    classical
    dsimp only
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
    have linear_degree (w : Kˣ) : (1 - C (w : K) * X).natDegree = 1 := by
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · apply natDegree_le_iff_coeff_eq_zero.mpr
        intro h hh
        simp [coeff_sub, coeff_one, coeff_X, show h ≠ 0 by omega,
          show 1 ≠ h by omega]
      · simp [coeff_sub, coeff_one, Units.ne_zero]
    have linear_nonzero (w : Kˣ) : (1 - C (w : K) * X) ≠ 0 := by
      intro h
      have equality := congrArg (fun P : K[X] => P.coeff 0) h
      simp [coeff_sub, coeff_one] at equality
    constructor
    · rw [natDegree_prod _ _ (fun j _ => pow_ne_zero _ (linear_nonzero _))]
      simp_rw [natDegree_pow, linear_degree, mul_one]
      rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one, total]
    · apply leadingCoeff_ne_zero.mpr
      apply prod_ne_zero_iff.mpr
      intro j _; exact pow_ne_zero _ (linear_nonzero _)
  have boundary_numerator (Q : K[X]) (u : ℤ → K)
      (gap : ℕ) (gap_positive : 1 ≤ gap) (gap_bound : gap ≤ Q.natDegree)
      (recurrence : ∀ n : ℤ,
        ∑ k ∈ range (Q.natDegree + 1), Q.coeff k * u (n - k) = 0)
      (negative_gap : ∀ a : ℕ, 1 ≤ a → a < gap → u (-(a : ℤ)) = 0)
      (first_nonzero : Q.leadingCoeff * u (-(gap : ℤ)) ≠ 0) :
      ∃ P : K[X],
        (P : PowerSeries K) = (Q : PowerSeries K) * PowerSeries.mk (fun n => u n) ∧
        P.natDegree = Q.natDegree - gap ∧
        P.coeff (Q.natDegree - gap) = -Q.leadingCoeff * u (-(gap : ℤ)) := by
    classical
    let F : PowerSeries K := (Q : PowerSeries K) * PowerSeries.mk (fun n => u n)
    have convolution (n : ℕ) : PowerSeries.coeff n F =
        ∑ k ∈ range (Q.natDegree + 1),
          if k ≤ n then Q.coeff k * u ((n : ℤ) - k) else 0 := by
      dsimp only [F]
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk]
      by_cases h : n ≤ Q.natDegree
      · apply sum_subset_zero_on_sdiff (range_mono (by omega))
        · intro k hk
          simp only [mem_sdiff, mem_range] at hk
          rw [if_neg (by omega)]
        · intro k hk
          have kn : k ≤ n := by simp only [mem_range] at hk; omega
          rw [if_pos kn, Nat.cast_sub kn]
      · symm
        apply sum_subset_zero_on_sdiff (range_mono (by omega))
        · intro k hk
          simp only [mem_sdiff, mem_range] at hk
          rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        · intro k hk
          have kn : k ≤ n := by simp only [mem_range] at hk; omega
          rw [if_pos kn, Nat.cast_sub kn]
    have boundary (n : ℕ) : PowerSeries.coeff n F =
        -(∑ k ∈ range (Q.natDegree + 1),
          if n < k then Q.coeff k * u ((n : ℤ) - k) else 0) := by
      have split : (∑ k ∈ range (Q.natDegree + 1), Q.coeff k * u ((n : ℤ) - k)) =
          (∑ k ∈ range (Q.natDegree + 1),
            if k ≤ n then Q.coeff k * u ((n : ℤ) - k) else 0) +
          (∑ k ∈ range (Q.natDegree + 1),
            if n < k then Q.coeff k * u ((n : ℤ) - k) else 0) := by
        rw [← sum_add_distrib]; apply sum_congr rfl
        intro k _
        by_cases h : k ≤ n <;> simp [h, show (n < k) ↔ ¬k ≤ n by omega]
      rw [recurrence, ← convolution] at split; exact eq_neg_of_add_eq_zero_left split.symm
    have tail_zero (n : ℕ) (hn : Q.natDegree - gap < n) :
        PowerSeries.coeff n F = 0 := by
      rw [boundary, neg_eq_zero]; apply sum_eq_zero
      intro k hk
      split_ifs with h
      · have kb : k ≤ Q.natDegree := by simp only [mem_range] at hk; omega
        have index : (n : ℤ) - k = -((k - n : ℕ) : ℤ) := by
          rw [Nat.cast_sub (by omega)]; ring
        rw [index, negative_gap (k - n) (by omega) (by omega), mul_zero]
      · rfl
    have top : PowerSeries.coeff (Q.natDegree - gap) F =
        -Q.leadingCoeff * u (-(gap : ℤ)) := by
      rw [boundary, sum_eq_single Q.natDegree]
      · rw [if_pos (by omega), coeff_natDegree]
        have index : ((Q.natDegree - gap : ℕ) : ℤ) - Q.natDegree = -(gap : ℤ) := by
          rw [Nat.cast_sub gap_bound]; ring
        rw [index, neg_mul]
      · intro k hk kne
        split_ifs with h
        · have kb : k < Q.natDegree := by simp only [mem_range] at hk; omega
          have index : ((Q.natDegree - gap : ℕ) : ℤ) - k =
              -((k - (Q.natDegree - gap) : ℕ) : ℤ) := by
            rw [Nat.cast_sub (show Q.natDegree - gap ≤ k by omega),
              Nat.cast_sub gap_bound]
            ring
          rw [index, negative_gap _ (by omega) (by omega), mul_zero]
        · rfl
      · simp
    let P : K[X] := ∑ n ∈ range (Q.natDegree - gap + 1),
      Polynomial.monomial n (PowerSeries.coeff n F)
    have coefficients (n : ℕ) : P.coeff n =
        if n < Q.natDegree - gap + 1 then PowerSeries.coeff n F else 0 := by
      simp [P, finsetSum_coeff, coeff_monomial]
    have coefficient : P.coeff (Q.natDegree - gap) =
        -Q.leadingCoeff * u (-(gap : ℤ)) := by
      rw [coefficients, if_pos (by omega), top]
    refine ⟨P, ?_, ?_, coefficient⟩
    · apply PowerSeries.ext
      intro n; rw [Polynomial.coeff_coe, coefficients]
      split_ifs with h
      · rfl
      · exact (tail_zero n (by omega)).symm
    · apply natDegree_eq_of_le_of_coeff_ne_zero
      · apply natDegree_le_iff_coeff_eq_zero.mpr
        intro n hn; rw [coefficients, if_neg (by omega)]
      · rw [coefficient, neg_mul, neg_ne_zero]
        exact first_nonzero
  intro m hm
  let alphaU : Kˣ := Units.mk0 alpha nonzero
  obtain ⟨z, a, b, constant, forward, back⟩ := branches phi alpha nonzero separated parameter
  let q (n : ℤ) : PowerSeries K :=
    a * ((z ^ n : (PowerSeries K)ˣ) : PowerSeries K) +
      b * ((z ^ (-n) : (PowerSeries K)ˣ) : PowerSeries K)
  let U (n : ℤ) : K := (-1 : K) ^ m.choose 2 *
    (Matrix.of fun row column : Fin m => PowerSeries.coeff column.val (q (n + row.val))).det
  obtain ⟨positive, negative_gap, negative_nonzero⟩ :=
    identification phi injective m q forward back
  obtain ⟨P, bounds, expansion⟩ := confluence m z alphaU constant a b
  let PP (S : Finset (Fin m)) : K[X] := C ((-1 : K) ^ m.choose 2) * P S
  have formula (n : ℤ) : U n = ∑ S : Finset (Fin m),
      (((alphaU ^ ((m : ℤ) - 2 * S.card) : Kˣ) ^ n : Kˣ) : K) * (PP S).eval (n : K) := by
    dsimp only [U, q]; rw [expansion, mul_sum]
    apply sum_congr rfl
    intro S _; dsimp only [PP]
    rw [eval_mul, eval_C, zpow_mul]; ring
  let index (S : Finset (Fin m)) : Fin (m + 1) :=
    ⟨S.card, by
      have bound : S.card ≤ m := by simpa using S.card_le_univ
      omega⟩
  let rho (j : Fin (m + 1)) : Kˣ := alphaU ^ ((m : ℤ) - 2 * j.val)
  let e (j : Fin (m + 1)) : ℕ := 1 + j.val * (m - j.val)
  let Q : K[X] := ∏ j, (1 - C (rho j : K) * X) ^ e j
  have Q_eq : Q = Polynomial.map phi (denominator m) := by
    rw [split_denominator phi alphaU (by simpa [alphaU] using parameter)]
    dsimp only [Q, rho, e]; exact Fin.prod_univ_eq_prod_range (fun j : ℕ =>
      (1 - C ((alphaU ^ ((m : ℤ) - 2 * j) : Kˣ) : K) * X) ^ (1 + j * (m - j)))
        (m + 1)
  have degree_info : Q.natDegree = m + 1 + (m + 1).choose 3 ∧ Q.leadingCoeff ≠ 0 := by
    rw [Q_eq, split_denominator phi alphaU (by simpa [alphaU] using parameter)]
    exact degree_denominator alphaU m
  have recurrent : ∀ n : ℤ,
      ∑ k ∈ range (Q.natDegree + 1), Q.coeff k * U (n - k) = 0 := by
    have recurrent := annihilator index rho PP e (fun S => by
      change (C ((-1 : K) ^ m.choose 2) * P S).natDegree < 1 + S.card * (m - S.card)
      have bound := (natDegree_C_mul_le ((-1 : K) ^ m.choose 2) (P S)).trans (bounds S)
      omega)
    intro n
    convert recurrent n using 1
    apply sum_congr rfl
    intro k _; rw [formula]
  obtain ⟨Pk, polynomial, degree, top⟩ := boundary_numerator Q U m hm
    (by rw [degree_info.1]; omega) recurrent negative_gap
    (mul_ne_zero degree_info.2 negative_nonzero)
  let F : PowerSeries Base :=
    (denominator m : PowerSeries Base) * PowerSeries.mk (hankelDet m)
  have map_series : PowerSeries.map phi F =
      (Q : PowerSeries K) * PowerSeries.mk (fun n => U n) := by
    dsimp only [F]; rw [map_mul, Q_eq, Polynomial.polynomial_map_coe]
    congr 1
    apply PowerSeries.ext
    intro n; simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (positive n).symm
  have coefficient_map (n : ℕ) : phi (PowerSeries.coeff n F) = Pk.coeff n := by
    rw [← PowerSeries.coeff_map, map_series, ← polynomial, Polynomial.coeff_coe]
  let N := (m + 1).choose 3 + 1
  have field_degree : Pk.natDegree = N := by rw [degree, degree_info.1]; dsimp [N]; omega
  have tail_zero (n : ℕ) (hn : N < n) : PowerSeries.coeff n F = 0 := by
    apply injective
    rw [map_zero, coefficient_map, coeff_eq_zero_of_natDegree_lt (by omega)]
  have top_nonzero : PowerSeries.coeff N F ≠ 0 := by
    intro zero
    have zeroK : Pk.coeff N = 0 := by rw [← coefficient_map, zero, map_zero]
    have top_index : Q.natDegree - m = N := by rw [degree_info.1]; dsimp [N]; omega
    rw [top_index] at top; rw [top, neg_mul] at zeroK
    exact (neg_ne_zero.mpr (mul_ne_zero degree_info.2 negative_nonzero)) zeroK
  let R : Base[X] := ∑ n ∈ range (N + 1), Polynomial.monomial n (PowerSeries.coeff n F)
  have coefficients (n : ℕ) : R.coeff n =
      if n < N + 1 then PowerSeries.coeff n F else 0 := by
    simp [R, finsetSum_coeff, coeff_monomial]
  refine ⟨R, ?_, ?_⟩
  · apply PowerSeries.ext
    intro n; rw [Polynomial.coeff_coe, coefficients]
    split_ifs with h
    · rfl
    · exact (tail_zero n (by omega)).symm
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn; rw [coefficients, if_neg (by omega)]
    · rw [coefficients, if_pos (by omega)]
      exact top_nonzero
end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankel
