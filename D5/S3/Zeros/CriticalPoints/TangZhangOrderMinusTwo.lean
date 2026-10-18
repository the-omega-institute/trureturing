/- GID: D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Charpoly.Basic]
   utility: none
   digest: The inverse-square critical-point inequality and its collinearity equality case. -/

import D5.S3.Quantum.GNSMatrix
import D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Polynomial, matrix and collinearity identities for the inverse-square conjecture. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo

open Polynomial Matrix Complex
open scoped ComplexConjugate

noncomputable def P {n : ℕ} (z : Fin n → ℂ) : Polynomial ℂ :=
  Polynomial.X * ∏ j, (Polynomial.X - Polynomial.C (z j))

def claim : Prop := ∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) →
    (((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖⁻¹ ^ 2)).sum ≤
      3 * ∑ j, ‖z j‖⁻¹ ^ 2 + ‖∑ j, (z j)⁻¹‖ ^ 2) ∧
    ((((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖⁻¹ ^ 2)).sum =
      3 * ∑ j, ‖z j‖⁻¹ ^ 2 + ‖∑ j, (z j)⁻¹‖ ^ 2) ↔
        ∀ j, ∃ r : ℝ, z j = (r : ℂ) * z ⟨0, hn⟩)

def J (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun _ _ => 1

theorem J_sq (n : ℕ) : J n * J n = (n : ℂ) • J n := by
  rw [show J n = Matrix.vecMulVec (1 : Fin n → ℂ) (1 : Fin n → ℂ) by
    ext i j
    simp [J, Matrix.vecMulVec]]
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  congr 1
  simp [dotProduct]

theorem J_conjTranspose (n : ℕ) : (J n)ᴴ = J n := by
  rw [show J n = Matrix.vecMulVec (1 : Fin n → ℂ) (1 : Fin n → ℂ) by
    ext i j
    simp [J, Matrix.vecMulVec]]
  rw [Matrix.conjTranspose_vecMulVec]
  simp

private theorem square_root_matrix (n : ℕ) (c : ℂ) (hc : 2 * c + (n : ℂ) * c ^ 2 = 1) :
    (1 + c • J n) * (1 + c • J n) = 1 + J n := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    Matrix.smul_mul, Matrix.mul_smul, J_sq, smul_smul, smul_smul]
  have he : c • J n + (c • J n + (c * c * n) • J n) = J n := by
    rw [← add_smul, ← add_smul]
    convert one_smul ℂ (J n) using 1
    congr 1
    linear_combination hc
  calc
    1 + c • J n + (c • J n + (c * c * n) • J n) =
        1 + (c • J n + (c • J n + (c * c * n) • J n)) := add_assoc _ _ _
    _ = 1 + J n := by rw [he]

private theorem inverse_matrix (n : ℕ) (c d : ℂ) (hcd : c + d + (n : ℂ) * c * d = 0) :
    (1 + c • J n) * (1 + d • J n) = 1 := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    Matrix.smul_mul, Matrix.mul_smul, J_sq, smul_smul, smul_smul]
  have he : d • J n + (c • J n + (c * d * n) • J n) = 0 := by
    rw [← add_smul, ← add_smul]
    convert zero_smul ℂ (J n) using 1
    congr 1
    linear_combination hcd
  calc
    1 + d • J n + (c • J n + (c * d * n) • J n) =
        1 + (d • J n + (c • J n + (c * d * n) • J n)) := add_assoc _ _ _
    _ = 1 := by rw [he, add_zero]

private theorem real_line_iff {n : ℕ} (v : Fin n → ℂ) (i₀ : Fin n) (hv : v i₀ ≠ 0) :
    (∀ i j, conj (v i) * v j = v i * conj (v j)) ↔
      ∀ j, ∃ r : ℝ, v j = (r : ℂ) * v i₀ := by
  constructor
  · intro h j
    have hq : conj (v j / v i₀) = v j / v i₀ := by
      rw [map_div₀]
      apply (div_eq_div_iff ((_root_.map_ne_zero (starRingEnd ℂ)).mpr hv) hv).mpr
      simpa [mul_comm] using (h i₀ j).symm
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hq
    exact ⟨r, (div_eq_iff hv).mp hr⟩
  · intro h i j
    obtain ⟨r, hr⟩ := h i
    obtain ⟨s, hs⟩ := h j
    rw [hr, hs, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    ring

private theorem inverse_real_line_iff {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, z j ≠ 0)
    (i₀ : Fin n) :
    (∀ j, ∃ r : ℝ, (z j)⁻¹ = (r : ℂ) * (z i₀)⁻¹) ↔
      ∀ j, ∃ r : ℝ, z j = (r : ℂ) * z i₀ := by
  constructor <;> intro h j <;> obtain ⟨r, hr⟩ := h j
  · have h := congrArg Inv.inv hr
    refine ⟨r⁻¹, ?_⟩
    simpa [_root_.mul_inv_rev, mul_comm] using h
  · refine ⟨r⁻¹, ?_⟩
    simpa [_root_.mul_inv_rev, mul_comm] using congrArg Inv.inv hr

private theorem core_normal_iff (n : ℕ) (b : Fin n → ℂ) :
    (diagonal b)ᴴ * (1 + J n) * diagonal b =
      diagonal b * (1 + J n) * (diagonal b)ᴴ ↔
        ∀ i j, conj (b i) * b j = b i * conj (b j) := by
  have hd : (diagonal b)ᴴ = diagonal (fun i => conj (b i)) := by
    simp [Matrix.diagonal_conjTranspose, Complex.star_def]
  have hcomm : (diagonal b)ᴴ * diagonal b = diagonal b * (diagonal b)ᴴ := by
    rw [hd]
    exact (Matrix.commute_diagonal _ _).eq
  simp only [mul_add, add_mul, Matrix.mul_one, hcomm, add_left_cancel_iff]
  rw [hd]
  constructor
  · intro h i j
    simpa [J, Matrix.diagonal_mul, Matrix.mul_diagonal] using
      congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h
  · intro h
    ext i j
    simpa [J, Matrix.diagonal_mul, Matrix.mul_diagonal] using h i j

private theorem core_trace (n : ℕ) (b : Fin n → ℂ) :
    Matrix.trace ((diagonal b)ᴴ * (1 + J n) * diagonal b * (1 + J n)) =
      ((3 * ∑ j, ‖b j‖ ^ 2 + ‖∑ j, b j‖ ^ 2 : ℝ) : ℂ) := by
  have hd : (diagonal b)ᴴ = diagonal (fun i => conj (b i)) := by
    simp [Matrix.diagonal_conjTranspose, Complex.star_def]
  have hnorm : ∑ j, conj (b j) * b j = ((∑ j, ‖b j‖ ^ 2 : ℝ) : ℂ) := by
    simp [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_sum]
  have hnorm' : (∑ j, conj (b j)) * (∑ j, b j) = ((‖∑ j, b j‖ ^ 2 : ℝ) : ℂ) := by
    rw [← map_sum, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [show J n = Matrix.vecMulVec (1 : Fin n → ℂ) (1 : Fin n → ℂ) by
    ext i j
    simp [J, Matrix.vecMulVec]]
  simp only [mul_add, add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.trace_add, hd]
  simp only [Matrix.diagonal_mul_diagonal, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.trace_diagonal, Matrix.trace_vecMulVec]
  simp only [Matrix.vecMulVec_mulVec, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, dotProduct, Matrix.mulVec_diagonal, Matrix.vecMul_diagonal,
    Pi.one_apply, mul_one, one_mul, Pi.mul_apply, Finset.sum_mul]
  rw [← Finset.sum_mul, hnorm, hnorm']
  push_cast
  ring

def B {n : ℕ} (b : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal b * (1 + J n)

private theorem eval_charpoly_B {n : ℕ} (b : Fin n → ℂ) (t : ℂ)
    (ht : ∀ i, t ≠ b i) :
    (B b).charpoly.eval t = (∏ j, (t - b j)) -
      ∑ i, b i * ∏ j ∈ Finset.univ.erase i, (t - b j) := by
  let a := fun i => t - b i
  have ha (i) : a i ≠ 0 := sub_ne_zero.mpr (ht i)
  have hdet : IsUnit (Matrix.det (diagonal a)) := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)
  have hm : Matrix.scalar (Fin n) t - B b = diagonal a +
      Matrix.replicateCol Unit (fun i => -b i) *
        Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℂ)) := by
    ext i j
    simp [B, J, a, Matrix.scalar, Matrix.diagonal_mul, Matrix.diagonal_apply,
      Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow]
    split_ifs with hij <;> simp [Matrix.one_apply, hij] <;> ring
  rw [Matrix.eval_charpoly, hm,
    Matrix.det_add_replicateCol_mul_replicateRow hdet, Matrix.det_diagonal]
  have hinv : (diagonal a)⁻¹ = diagonal (fun i => (a i)⁻¹) := by
    rw [Matrix.inv_diagonal]
    congr 1
    have hau : IsUnit a := Pi.isUnit_iff.mpr (fun i => (ha i).isUnit)
    funext i
    exact (hau.map_ringInverse (Pi.evalMonoidHom _ i)).trans (Ring.inverse_eq_inv _)
  rw [hinv]
  have hsmall : (1 + Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℂ)) *
      diagonal (fun i => (a i)⁻¹) * Matrix.replicateCol Unit (fun i => -b i)).det =
      1 - ∑ i, b i / a i := by
    rw [← Matrix.replicateRow_vecMul, Matrix.replicateRow_mul_replicateCol]
    simp [Matrix.det_unique, Matrix.vecMul_diagonal, dotProduct, div_eq_mul_inv,
      Finset.sum_neg_distrib, mul_comm, sub_eq_add_neg]
  rw [hsmall, mul_sub, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
  dsimp only [a]
  field_simp [sub_ne_zero.mpr (ht i)]

private theorem reverse_linear (w : ℂ) :
    (X - C w : ℂ[X]).reverse = 1 - C w * X := by
  rw [sub_eq_add_neg, ← C_neg, Polynomial.reverse_add_C]
  simp [Polynomial.reverse, sub_eq_add_neg]

private theorem roots_reverse (q : ℂ[X]) (hq0 : q.eval 0 ≠ 0) :
    q.reverse.roots = q.roots.map (fun w => w⁻¹) := by
  have hw (w : ℂ) (hw : w ∈ q.roots) : w ≠ 0 := by
    intro h
    have hh := Polynomial.isRoot_of_mem_roots hw
    subst w
    exact hq0 hh
  have hrevprod (s : Multiset ℂ) :
      ((s.map (fun w => X - C w : ℂ → ℂ[X])).prod).reverse =
        (s.map (fun w => (X - C w : ℂ[X]).reverse)).prod := by
    let rev : ℂ[X] →* ℂ[X] :=
      { toFun := Polynomial.reverse
        map_one' := by simp [Polynomial.reverse]
        map_mul' := Polynomial.reverse_mul_of_domain }
    exact (s.prod_hom' rev (fun w => X - C w)).symm
  conv_lhs => rw [(IsAlgClosed.splits q).eq_prod_roots]
  rw [Polynomial.reverse_mul_of_domain, Polynomial.reverse_C, hrevprod,
    Polynomial.roots_C_mul _ (Polynomial.leadingCoeff_ne_zero.mpr
      (by intro h; simp [h] at hq0))]
  have hnonzero : (0 : ℂ[X]) ∉ q.roots.map (fun w => (X - C w : ℂ[X]).reverse) := by
    simp only [Multiset.mem_map, not_exists, not_and]
    intro w _ he
    exact (Polynomial.X_sub_C_ne_zero w)
      (Polynomial.reverse_eq_zero.mp he)
  rw [Polynomial.roots_multiset_prod _ hnonzero, Multiset.bind_map]
  have hl (w : ℂ) (hw' : w ∈ q.roots) :
      (X - C w : ℂ[X]).reverse.roots = {w⁻¹} := by
    rw [reverse_linear]
    rw [show (1 - C w * X : ℂ[X]) = C (-w) * X + C 1 by simp; ring]
    simpa using
      (Polynomial.roots_C_mul_X_add_C_of_IsUnit (1 : ℂ)
        (Units.mk0 (-w) (neg_ne_zero.mpr (hw w hw'))))
  rw [Multiset.bind_congr hl]
  simp

private theorem factor_degree {ι : Type*} (b : ι → ℂ) (i : ι) :
    (1 - C (b i) * X : ℂ[X]).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le (by simp)
  exact (Polynomial.natDegree_mul_le).trans (by simp)

private theorem product_degree {ι : Type*} (b : ι → ℂ) (s : Finset ι) :
    (∏ i ∈ s, (1 - C (b i) * X : ℂ[X])).natDegree ≤ s.card := by
  calc
    _ ≤ ∑ i ∈ s, (1 - C (b i) * X : ℂ[X]).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum (fun i _ => factor_degree b i)
    _ = s.card := by simp

private theorem reflect_product {ι : Type*} [DecidableEq ι] (b : ι → ℂ) (s : Finset ι) :
    Polynomial.reflect s.card (∏ i ∈ s, (1 - C (b i) * X : ℂ[X])) =
      ∏ i ∈ s, (X - C (b i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_comm s.card 1,
      Polynomial.reflect_mul _ _ (factor_degree b i) (product_degree b s), ih,
      Finset.prod_insert hi]
    congr 1
    rw [Polynomial.reflect_sub, Polynomial.reflect_one, Polynomial.reflect_C_mul,
      Polynomial.reflect_one_X]
    simp

private theorem normalized_derivative {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, z j ≠ 0) :
    (P z).derivative = C (∏ j, -z j) *
      ((∏ j, (1 - C ((z j)⁻¹) * X)) -
        ∑ i, C ((z i)⁻¹) * X * ∏ j ∈ Finset.univ.erase i, (1 - C ((z j)⁻¹) * X)) := by
  have hf (j) : X - C (z j) = C (-z j) * (1 - C ((z j)⁻¹) * X) := by
    rw [mul_sub, mul_one, ← mul_assoc, ← C_mul]
    simp [hz j] <;> ring
  have hp : P z = C (∏ j, -z j) *
      (X * ∏ j, (1 - C ((z j)⁻¹) * X)) := by
    dsimp only [P]
    simp_rw [hf]
    rw [Finset.prod_mul_distrib, ← map_prod]
    ring
  rw [hp, Polynomial.derivative_C_mul, Polynomial.derivative_mul, Polynomial.derivative_X,
    one_mul, Polynomial.derivative_prod_finset]
  congr 1
  simp only [Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_C_mul,
    Polynomial.derivative_X, mul_one, zero_sub]
  simp only [Finset.mul_sum, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 1
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem derivative_degree {n : ℕ} (z : Fin n → ℂ) :
    (P z).derivative.natDegree = n := by
  rw [Polynomial.natDegree_derivative]
  have hp : (P z).natDegree = n + 1 := by
    dsimp only [P]
    rw [Polynomial.natDegree_mul (Polynomial.X_ne_zero)
      (Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _)]
    simp [Polynomial.natDegree_prod, Polynomial.X_sub_C_ne_zero, Nat.add_comm]
  rw [hp, Nat.add_sub_cancel]

private theorem charpoly_B {n : ℕ} (b : Fin n → ℂ) :
    (B b).charpoly = (∏ j, (X - C (b j))) -
      ∑ i, C (b i) * ∏ j ∈ Finset.univ.erase i, (X - C (b j)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_univ.sdiff (Set.finite_range b)).mono
  intro t ht
  have h := eval_charpoly_B b t (fun i hi => ht.2 ⟨i, hi.symm⟩)
  simpa [Polynomial.eval_prod, Polynomial.eval_finsetSum] using h

private theorem reversed_derivative {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, z j ≠ 0) :
    (P z).derivative.reverse = C (∏ j, -z j) * (B (fun j => (z j)⁻¹)).charpoly := by
  have hprod := reflect_product (fun j => (z j)⁻¹) (Finset.univ : Finset (Fin n))
  simp only [Finset.card_univ, Fintype.card_fin] at hprod
  rw [Polynomial.reverse, derivative_degree, normalized_derivative z hz,
    Polynomial.reflect_C_mul, Polynomial.reflect_sub, hprod, charpoly_B]
  congr 1
  have hsum (s : Finset (Fin n)) (p : Fin n → ℂ[X]) :
      Polynomial.reflect n (∑ i ∈ s, p i) = ∑ i ∈ s, Polynomial.reflect n (p i) := by
    exact map_sum (show ℂ[X] →+ ℂ[X] from
      { toFun := Polynomial.reflect n
        map_zero' := Polynomial.reflect_zero
        map_add' := fun f g => Polynomial.reflect_add f g n }) p s
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, Polynomial.reflect_C_mul]
  congr 1
  have hc : n = 1 + (Finset.univ.erase i).card := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have := i.isLt
    omega
  conv_lhs => arg 1; rw [hc]
  rw [Polynomial.reflect_mul _ _ (by simp : (X : ℂ[X]).natDegree ≤ 1)
    (product_degree _ _), Polynomial.reflect_one_X, one_mul, reflect_product]

theorem roots_derivative {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, z j ≠ 0) :
    (P z).derivative.roots.map (fun w => w⁻¹) = (B (fun j => (z j)⁻¹)).charpoly.roots := by
  have hc : (∏ j, -z j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => neg_ne_zero.mpr (hz j))
  have hq0 : (P z).derivative.eval 0 ≠ 0 := by
    rw [normalized_derivative z hz]
    simpa [Polynomial.eval_prod, Polynomial.eval_finsetSum] using hc
  rw [← roots_reverse _ hq0, reversed_derivative z hz, Polynomial.roots_C_mul _ hc]

private theorem sandwich_reduction {n : ℕ} (b : Fin n → ℂ)
    (R S : Matrix (Fin n) (Fin n) ℂ) (hR : Rᴴ = R) (hRR : R * R = 1 + J n)
    (hRS : R * S = 1) (hSR : S * R = 1) :
    (((B b).charpoly.roots.map (fun μ => ‖μ‖ ^ 2)).sum ≤
      3 * ∑ j, ‖b j‖ ^ 2 + ‖∑ j, b j‖ ^ 2) ∧
    ((((B b).charpoly.roots.map (fun μ => ‖μ‖ ^ 2)).sum =
      3 * ∑ j, ‖b j‖ ^ 2 + ‖∑ j, b j‖ ^ 2) ↔
        ∀ i j, conj (b i) * b j = b i * conj (b j)) := by
  let D := diagonal b
  let A := R * D * R
  have hp : A.charpoly = (B b).charpoly := by
    dsimp [A, B]
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hRR, Matrix.charpoly_mul_comm]
  have hm (E F : Matrix (Fin n) (Fin n) ℂ) :
      (R * E * R) * (R * F * R) = R * (E * (1 + J n) * F) * R := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R R, hRR]
  have hstar : Aᴴ = R * Dᴴ * R := by
    simp only [A, Matrix.conjTranspose_mul, hR, Matrix.mul_assoc]
  have hf : ∑ i, ∑ j, ‖A i j‖ ^ 2 = 3 * ∑ j, ‖b j‖ ^ 2 + ‖∑ j, b j‖ ^ 2 := by
    apply Complex.ofReal_injective
    have htrace : ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (Aᴴ * A) := by
      have h := D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace A
      change ((‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))‖ ^ 2 : ℝ) : ℂ) = _ at h
      simpa only [PiLp.norm_sq_eq_of_L2] using h
    rw [htrace, hstar]
    change Matrix.trace ((R * Dᴴ * R) * (R * D * R)) = _
    rw [hm, Matrix.trace_mul_cycle, hRR, Matrix.trace_mul_comm]
    exact core_trace n b
  have hn : A * Aᴴ = Aᴴ * A ↔ ∀ i j, conj (b i) * b j = b i * conj (b j) := by
    rw [hstar]
    change (R * D * R) * (R * Dᴴ * R) = (R * Dᴴ * R) * (R * D * R) ↔ _
    rw [hm, hm]
    have hcancel (E F : Matrix (Fin n) (Fin n) ℂ) :
        R * E * R = R * F * R ↔ E = F := by
      have hRu : IsUnit R := ⟨⟨R, S, hRS, hSR⟩, rfl⟩
      rw [hRu.mul_left_inj, hRu.mul_right_inj]
    rw [hcancel, eq_comm, core_normal_iff]
  have h := SchurFrobeniusInequality.schur_frobenius n A
  rw [hp, hf, hn] at h
  exact h

private theorem spectral_inequality (n : ℕ) (b : Fin n → ℂ) :
    (((B b).charpoly.roots.map (fun μ => ‖μ‖ ^ 2)).sum ≤
      3 * ∑ j, ‖b j‖ ^ 2 + ‖∑ j, b j‖ ^ 2) ∧
    ((((B b).charpoly.roots.map (fun μ => ‖μ‖ ^ 2)).sum =
      3 * ∑ j, ‖b j‖ ^ 2 + ‖∑ j, b j‖ ^ 2) ↔
        ∀ i j, conj (b i) * b j = b i * conj (b j)) := by
  let s : ℝ := Real.sqrt ((n : ℝ) + 1)
  have hs : s ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs0 : s ≠ 0 := ne_of_gt hspos
  have hs1 : s + 1 ≠ 0 := ne_of_gt (add_pos hspos zero_lt_one)
  let c : ℂ := ((s + 1)⁻¹ : ℝ)
  let d : ℂ := (-(s * (s + 1))⁻¹ : ℝ)
  have hcr : 2 * (s + 1)⁻¹ + (n : ℝ) * ((s + 1)⁻¹) ^ 2 = 1 := by
    field_simp
    nlinarith [hs]
  have hdr : (s + 1)⁻¹ + (-(s * (s + 1))⁻¹) +
      (n : ℝ) * (s + 1)⁻¹ * (-(s * (s + 1))⁻¹) = 0 := by
    field_simp
    nlinarith [hs]
  have hc : 2 * c + (n : ℂ) * c ^ 2 = 1 := by
    dsimp only [c]
    exact_mod_cast hcr
  have hd : c + d + (n : ℂ) * c * d = 0 := by
    dsimp only [c, d]
    exact_mod_cast hdr
  let R : Matrix (Fin n) (Fin n) ℂ := 1 + c • J n
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + d • J n
  have hR : Rᴴ = R := by simp [R, Matrix.conjTranspose_smul, J_conjTranspose, c]
  have hRR : R * R = 1 + J n := square_root_matrix n c hc
  have hRS : R * S = 1 := inverse_matrix n c d hd
  have hSR : S * R = 1 := inverse_matrix n d c (by linear_combination hd)
  exact sandwich_reduction b R S hR hRR hRS hSR

/-- Tang–Zhang Conjecture 6.3, including the exact equality criterion. -/
theorem result : claim := by
  intro n hn z hz
  have hr := roots_derivative z hz
  have h := spectral_inequality n (fun j => (z j)⁻¹)
  rw [← hr, Multiset.map_map] at h
  simp only [Function.comp_apply, norm_inv] at h
  refine ⟨h.1, h.2.trans ?_⟩
  exact (real_line_iff (fun j => (z j)⁻¹) ⟨0, hn⟩ (inv_ne_zero (hz _))).trans
    (inverse_real_line_iff z hz ⟨0, hn⟩)

end D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
