/- GID: D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct
   mirror-E: none(waiver:direct-Lean-proof)
   anchors: []
   utility: none
   digest: A weighted cyclic determinant gives the literal geodesic permanent. -/

/- Mathematical classification:
   q_midpoint: proof_shape: bind-only; escape_witness: none; consumer: midpoint_rate_of_product, midpoint_even_of_product, midpoint_ratio_of_product
   exp_two_pi_noninteger: proof_shape: bind-only; escape_witness: none; consumer: q_ne_one
   q_ne_one: proof_shape: bind-only; escape_witness: none; consumer: product_formula
   permanent_row_factors: proof_shape: bind-only; escape_witness: none; consumer: primitive_scaled_permanent
   nodal_primitive_powers: proof_shape: bind-only; escape_witness: none; consumer: primitive_poles_sum, primitive_neg_nodes_prod
   primitive_nodes_injective: proof_shape: bind-only; escape_witness: none; consumer: gaudin_primitive_column, gaudin_primitive_det, primitive_scaled_permanent
   primitive_node_power: proof_shape: bind-only; escape_witness: none; consumer: primitive_nodes_cross_ne, primitive_poles_sum, gaudin_primitive_column
   primitive_nodes_cross_ne: proof_shape: bind-only; escape_witness: none; consumer: primitive_poles_sum, primitive_scaled_permanent
   primitive_poles_sum: proof_shape: bind-only; escape_witness: none; consumer: gaudin_primitive_column
   primitive_neg_nodes_prod: proof_shape: bind-only; escape_witness: none; consumer: primitive_scaled_permanent
   zeta_primitive: proof_shape: bind-only; escape_witness: none; consumer: product_formula
   phaseRoot_power: proof_shape: bind-only; escape_witness: none; consumer: product_formula
   literal_phase: proof_shape: bind-only; escape_witness: none; consumer: gamma_cauchy_rows
   gamma_cauchy_rows: proof_shape: bind-only; escape_witness: none; consumer: product_formula
   root_shift_power: proof_shape: bind-only; escape_witness: none; consumer: gaudin_primitive_column
   gaudin_primitive_column: proof_shape: bind-only; escape_witness: none; consumer: gaudin_primitive_det
   weightedVandermonde_apply: proof_shape: bind-only; escape_witness: none; consumer: gaudin_primitive_det
   weightedVandermonde_det_ne_zero: proof_shape: bind-only; escape_witness: none; consumer: gaudin_primitive_det
   mul_permMatrix_apply: proof_shape: bind-only; escape_witness: none; consumer: gaudin_primitive_det
   gaudin_primitive_det: proof_shape: bind-only; escape_witness: none; consumer: primitive_scaled_permanent
   primitive_scaled_permanent: proof_shape: content; escape_witness: CycleGeodesic.gaudin_permanent; consumer: product_formula
   product_formula: proof_shape: content; escape_witness: CycleGeodesic.gaudin_permanent; consumer: result3, result2
   escape_witness: CycleGeodesic.gaudin_permanent: ∀ n : ℕ, ∀ x y : Fin n → ℂ, Function.Injective x → (∀ i j, x i ≠ y j) → (gaudin x y).det = (cauchy x y).permanent
   admission_basis: escape-witness
   Direct frozen dependencies: none at the immutable origin/dev baseline.
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.CycleGeodesic.GaudinPermanent
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Matrix.Permutation

noncomputable section
open scoped BigOperators Topology
open Filter Finset Polynomial Matrix Equiv Real
namespace CycleGeodesic

def gamma (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ := fun j l =>
  (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) - 1) /
    ((n : ℂ) * (Complex.exp (((2 * Real.pi * ((l : ℝ) - (j : ℝ) + t)) / n : ℝ) *
      Complex.I) - 1))

def productValue (n : ℕ) (z : ℂ) : ℂ :=
  (n : ℂ)⁻¹ ^ n * ∏ k : Fin n, ((n : ℂ) - k + (k : ℂ) * z)

def ProductFormula : Prop := ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t → t < 1 →
  (gamma n t).permanent = productValue n ((Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)))

lemma q_midpoint : (Complex.exp ((2 * Real.pi * (1 / 2) : ℝ) * Complex.I)) = -1 := by
  rw [show (2 * Real.pi * (1 / 2) : ℝ) = Real.pi by ring]
  exact Complex.exp_pi_mul_I

private lemma exp_two_pi_noninteger {x : ℝ} (hx : ∀ k : ℤ, x ≠ k) :
    Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have him := congrArg Complex.im hk
  simp at him
  have hpi := Real.pi_pos
  exact hx k (by nlinarith)

private lemma q_ne_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) ≠ 1 := by
  apply exp_two_pi_noninteger
  intro k hk
  have hk0 : (0 : ℤ) < k := by exact_mod_cast (show (0 : ℝ) < (k : ℝ) by simpa [hk] using ht0)
  have hk1 : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < (1 : ℝ) by simpa [hk] using ht1)
  omega

private lemma permanent_row_factors {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    Matrix.permanent (fun i j => w i * M i j : Matrix (Fin n) (Fin n) ℂ) =
      (∏ i, w i) * M.permanent := by
  unfold Matrix.permanent
  simp only [Finset.prod_mul_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  exact Fintype.prod_equiv σ (fun i => w (σ i)) w (by intro i; rfl)

private lemma nodal_primitive_powers {n : ℕ} {ζ : ℂ} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (a : ℂ) :
    Lagrange.nodal Finset.univ (fun i : Fin n => ζ ^ (i : ℕ) * a) = (X : ℂ[X]) ^ n - C (a ^ n) := by
  rw [Lagrange.nodal]
  rw [show (∏ i : Fin n, (X - C (ζ ^ (i : ℕ) * a))) =
      ∏ i ∈ Finset.range n, (X - C (ζ ^ i * a)) from
    Fin.prod_univ_eq_prod_range (fun i => (X - C (ζ ^ i * a) : ℂ[X])) n]
  exact (X_pow_sub_C_eq_prod hζ hn rfl).symm

private lemma primitive_nodes_injective {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (fun i : Fin n => ζ ^ (i : ℕ)) := by
  intro i j h
  exact Fin.ext (hζ.pow_inj i.isLt j.isLt h)

private lemma primitive_node_power {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (i : Fin n) :
    (ζ ^ (i : ℕ)) ^ n = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

private lemma primitive_nodes_cross_ne {n : ℕ} {ζ a : ℂ} (hζ : IsPrimitiveRoot ζ n) (ha : a ^ n ≠ 1)
    (i j : Fin n) : ζ ^ (i : ℕ) ≠ ζ ^ (j : ℕ) * a := by
  intro h
  have hp := congrArg (fun z : ℂ => z ^ n) h
  rw [primitive_node_power hζ i, mul_pow, primitive_node_power hζ j, one_mul] at hp
  exact ha hp.symm

private lemma primitive_poles_sum {n : ℕ} {ζ a : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (ha : a ^ n ≠ 1) (i : Fin n) :
    (∑ j : Fin n, (ζ ^ (i : ℕ) - ζ ^ (j : ℕ) * a)⁻¹) =
      (n : ℂ) * (ζ ^ (i : ℕ)) ^ (n - 1) / (1 - a ^ n) := by
  have h := nodal_derivative_nonroot (fun j : Fin n => ζ ^ (j : ℕ) * a)
    (primitive_nodes_cross_ne hζ ha i)
  rw [nodal_primitive_powers hn hζ a] at h
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
    Polynomial.derivative_C, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
    primitive_node_power hζ i] at h
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm ha))).2
  simpa only [mul_comm] using h.symm

private lemma primitive_neg_nodes_prod {n : ℕ} {ζ : ℂ} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    (∏ i : Fin n, -(ζ ^ (i : ℕ))) = -1 := by
  have h := congrArg (fun p : ℂ[X] => p.eval 0) (nodal_primitive_powers hn hζ 1)
  simpa [Lagrange.eval_nodal, zero_pow hn.ne'] using h

private lemma zeta_primitive {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ)))) n :=
  Complex.isPrimitiveRoot_exp n hn

private lemma phaseRoot_power {n : ℕ} (hn : n ≠ 0) (t : ℝ) : (Complex.exp (((2 * Real.pi * t) / (n : ℕ) : ℝ) * Complex.I)) ^ n = (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp

private lemma literal_phase {n : ℕ} (hn : n ≠ 0) (t : ℝ) (j l : Fin n) :
    Complex.exp (((2 * Real.pi * ((l : ℝ) - (j : ℝ) + t)) / n : ℝ) * Complex.I) =
      (Complex.exp (((2 * Real.pi * t) / (n : ℕ) : ℝ) * Complex.I)) * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (l : ℕ) / (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (j : ℕ) := by

  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

private lemma gamma_cauchy_rows {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    gamma n t = (fun j l : Fin n => (((Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) - 1) / (n : ℂ)) * (-((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (j : ℕ))) *
      cauchy (fun i : Fin n => (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (i : ℕ))
        (fun i : Fin n => (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (i : ℕ) * (Complex.exp (((2 * Real.pi * t) / (n : ℕ) : ℝ) * Complex.I))) j l) := by
  ext j l
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hζ := zeta_primitive hn0
  have hx : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (hζ.ne_zero hn0)
  have ha : (Complex.exp (((2 * Real.pi * t) / (n : ℕ) : ℝ) * Complex.I)) ^ n ≠ 1 := by rw [phaseRoot_power hn0]; exact q_ne_one ht0 ht1
  have hcross := primitive_nodes_cross_ne hζ ha j l
  have hsub : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (j : ℕ) - (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (l : ℕ) * (Complex.exp (((2 * Real.pi * t) / (n : ℕ) : ℝ) * Complex.I)) ≠ 0 := sub_ne_zero.mpr hcross
  have hphase : (Complex.exp (((2 * Real.pi * t) / (n : ℕ) : ℝ) * Complex.I)) * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (l : ℕ) / (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (j : ℕ) - 1 =
      -((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (j : ℕ) - (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (l : ℕ) * (Complex.exp (((2 * Real.pi * t) / (n : ℕ) : ℝ) * Complex.I))) / (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (j : ℕ) := by
    field_simp
    ring
  simp only [gamma, literal_phase hn0, cauchy]
  change ((Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) - 1) / ((n : ℂ) * ((Complex.exp (((2 * Real.pi * t) / (n : ℕ) : ℝ) * Complex.I)) * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (l : ℕ) / (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℕ))) ^ (j : ℕ) - 1)) = _
  rw [hphase]
  field_simp

private lemma root_shift_power {n : ℕ} {z : ℂ} (hz : z ^ (n + 1) = 1) (k : Fin (n + 1)) :
    z ^ n * z ^ (k : ℕ) = z ^ ((finRotate (n + 1)).symm k : ℕ) := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [coe_finRotate_symm_of_ne_zero hk, ← pow_add,
      show n + (k : ℕ) = (n + 1) + ((k : ℕ) - 1) by
        have hk0 : (k : ℕ) ≠ 0 := Fin.val_ne_zero_iff.mpr hk
        omega, pow_add, hz, one_mul]

private lemma gaudin_primitive_column {n : ℕ} {ζ a : ℂ} (hζ : IsPrimitiveRoot ζ (n + 1))
    (ha : a ^ (n + 1) ≠ 1) (k : Fin (n + 1)) :
    gaudin (fun i : Fin (n + 1) => ζ ^ (i : ℕ)) (fun j : Fin (n + 1) => ζ ^ (j : ℕ) * a) *ᵥ
      (fun i => Lagrange.nodalWeight Finset.univ (fun j : Fin (n + 1) => ζ ^ (j : ℕ)) i *
        (ζ ^ (i : ℕ)) ^ (k : ℕ)) =
      fun i => ((n + 1 : ℂ) / (1 - a ^ (n + 1)) - (k : ℂ)) *
        Lagrange.nodalWeight Finset.univ (fun j : Fin (n + 1) => ζ ^ (j : ℕ)) i *
        (ζ ^ (i : ℕ)) ^ ((finRotate (n + 1)).symm k : ℕ) := by
  let x : Fin (n + 1) → ℂ := fun i => ζ ^ (i : ℕ)
  have hdeg : ((X : ℂ[X]) ^ (k : ℕ)).degree < Fintype.card (Fin (n + 1)) := by
    simp only [degree_X_pow, Fintype.card_fin]
    exact_mod_cast k.isLt
  have h := gaudin_mulVec x (primitive_nodes_injective hζ) (fun j : Fin (n + 1) => ζ ^ (j : ℕ) * a)
    ((X : ℂ[X]) ^ (k : ℕ)) hdeg
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [h]
  funext i
  have hp := root_shift_power (primitive_node_power hζ i) k
  have hS : (∑ j : Fin (n + 1), (x i - ζ ^ (j : ℕ) * a)⁻¹) * (x i) ^ (k : ℕ) =
      ((n + 1 : ℂ) / (1 - a ^ (n + 1))) *
        (x i) ^ ((finRotate (n + 1)).symm k : ℕ) := by
    rw [primitive_poles_sum (by omega : 0 < n + 1) hζ ha i]
    simp only [Nat.add_sub_cancel]
    calc
      _ = ((n + 1 : ℂ) / (1 - a ^ (n + 1))) * ((x i) ^ n * (x i) ^ (k : ℕ)) := by
        simp [x]
        ring
      _ = _ := by rw [hp]
  have hD : (((X : ℂ[X]) ^ (k : ℕ)).derivative).eval (x i) =
      (k : ℂ) * (x i) ^ ((finRotate (n + 1)).symm k : ℕ) := by
    simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    by_cases hk : k = 0
    · subst k; simp
    · rw [coe_finRotate_symm_of_ne_zero hk]
  rw [hS, hD]
  ring

private def weightedVandermonde {n : ℕ} (x : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (Lagrange.nodalWeight Finset.univ x) * Matrix.vandermonde x

private lemma weightedVandermonde_apply {n : ℕ} (x : Fin n → ℂ) (i k : Fin n) :
    weightedVandermonde x i k = Lagrange.nodalWeight Finset.univ x i * x i ^ (k : ℕ) := by
  simp [weightedVandermonde, Matrix.diagonal_mul, Matrix.vandermonde_apply]

private lemma weightedVandermonde_det_ne_zero {n : ℕ} (x : Fin n → ℂ) (hx : Function.Injective x) :
    (weightedVandermonde x).det ≠ 0 := by
  rw [weightedVandermonde, Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Lagrange.nodalWeight_ne_zero hx.injOn (Finset.mem_univ i))
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hx

private lemma mul_permMatrix_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (σ : Equiv.Perm ι) (i j : ι) :
    (A * σ.permMatrix ℂ) i j = A i (σ.symm j) := by
  have h := congrFun (Matrix.vecMul_permMatrix σ (v := A i)) j
  simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Function.comp_def] using h

private lemma gaudin_primitive_det {n : ℕ} {ζ a : ℂ} (hζ : IsPrimitiveRoot ζ (n + 1))
    (ha : a ^ (n + 1) ≠ 1) :
    (gaudin (fun i : Fin (n + 1) => ζ ^ (i : ℕ)) (fun j : Fin (n + 1) => ζ ^ (j : ℕ) * a)).det =
      (-1 : ℂ) ^ n * ∏ k : Fin (n + 1), ((n + 1 : ℂ) / (1 - a ^ (n + 1)) - (k : ℂ)) := by
  let x : Fin (n + 1) → ℂ := fun i => ζ ^ (i : ℕ)
  let y : Fin (n + 1) → ℂ := fun j => ζ ^ (j : ℕ) * a
  let V := weightedVandermonde x
  let σ := finRotate (n + 1)
  let d : Fin (n + 1) → ℂ := fun k => (n + 1 : ℂ) / (1 - a ^ (n + 1)) - k
  have hM : gaudin x y * V = V * σ.permMatrix ℂ * Matrix.diagonal d := by
    ext i k
    rw [Matrix.mul_diagonal, mul_permMatrix_apply]
    simp only [V, Matrix.mul_apply, weightedVandermonde_apply]
    have h := congrFun (gaudin_primitive_column hζ ha k) i
    simpa only [Matrix.mulVec, dotProduct, x, y, d, σ, mul_comm, mul_left_comm, mul_assoc] using h
  have hdet := congrArg Matrix.det hM
  have hV : V.det ≠ 0 := weightedVandermonde_det_ne_zero x (primitive_nodes_injective hζ)
  simp only [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation] at hdet
  have hsign : (Equiv.Perm.sign σ : ℂ) = (-1 : ℂ) ^ n := by
    simp [σ, sign_finRotate]
  rw [hsign] at hdet
  apply mul_right_cancel₀ hV
  dsimp [x, y, d] at hdet ⊢
  linear_combination hdet

private lemma primitive_scaled_permanent {n : ℕ} {ζ a : ℂ} (hζ : IsPrimitiveRoot ζ (n + 1))
    (ha : a ^ (n + 1) ≠ 1) :
    Matrix.permanent (fun i j : Fin (n + 1) =>
      ((a ^ (n + 1) - 1) / (n + 1 : ℂ)) * (-(ζ ^ (i : ℕ))) *
        cauchy (fun i : Fin (n + 1) => ζ ^ (i : ℕ)) (fun j => ζ ^ (j : ℕ) * a) i j) =
      productValue (n + 1) (a ^ (n + 1)) := by
  let c : ℂ := (a ^ (n + 1) - 1) / (n + 1 : ℂ)
  let d : Fin (n + 1) → ℂ := fun k => (n + 1 : ℂ) / (1 - a ^ (n + 1)) - (k : ℂ)
  have hq : 1 - a ^ (n + 1) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hp := gaudin_permanent (n + 1) (fun i : Fin (n + 1) => ζ ^ (i : ℕ))
    (fun j : Fin (n + 1) => ζ ^ (j : ℕ) * a) (primitive_nodes_injective hζ)
    (primitive_nodes_cross_ne hζ ha)
  rw [gaudin_primitive_det hζ ha] at hp
  rw [permanent_row_factors, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, primitive_neg_nodes_prod (by omega : 0 < n + 1) hζ, ← hp]
  change c ^ (n + 1) * (-1) * ((-1 : ℂ) ^ n * ∏ k, d k) = _
  calc
    _ = ∏ k : Fin (n + 1), (-c) * d k := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, neg_pow, pow_succ]
      ring
    _ = productValue (n + 1) (a ^ (n + 1)) := by
      unfold productValue
      rw [show (((n + 1 : ℕ) : ℂ)⁻¹ ^ (n + 1)) = ∏ _ : Fin (n + 1), ((n + 1 : ℕ) : ℂ)⁻¹ by simp,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro k hk
      dsimp [c, d]
      push_cast
      field_simp
      ring

lemma product_formula : ProductFormula := by
  intro n hn t ht0 ht1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : m + 1 ≠ 0 := by omega
  have ha : (Complex.exp (((2 * Real.pi * t) / ((m + 1) : ℕ) : ℝ) * Complex.I)) ^ (m + 1) ≠ 1 := by
    rw [phaseRoot_power hm]
    exact q_ne_one ht0 ht1
  have h := primitive_scaled_permanent (zeta_primitive hm) ha
  rw [phaseRoot_power hm] at h
  rw [gamma_cauchy_rows (by omega) ht0 ht1]
  simpa only [Nat.cast_succ] using h

#print axioms q_midpoint
#print axioms product_formula
end CycleGeodesic
