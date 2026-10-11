/- GID: D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent
   mirror-E: none(waiver:direct-Lean-proof)
   anchors: []
   utility: none
   digest: Lagrange interpolation proves the Cauchy permanent as a Gaudin determinant. -/

/- Mathematical classification:
   permanent_succ_column_zero: proof_shape: bind-only; escape_witness: none; consumer: gaudin_permanent
   inverse_prod_mul_erase: proof_shape: bind-only; escape_witness: none; consumer: derivative_lagrange_basis_diagonal
   lagrange_basis_nodal_erase: proof_shape: bind-only; escape_witness: none; consumer: derivative_lagrange_basis_diagonal, derivative_lagrange_basis_off_diagonal
   derivative_lagrange_basis_diagonal: proof_shape: bind-only; escape_witness: none; consumer: derivative_interpolation_formula
   derivative_lagrange_basis_off_diagonal: proof_shape: bind-only; escape_witness: none; consumer: derivative_interpolation_formula
   derivative_interpolation_formula: proof_shape: bind-only; escape_witness: none; consumer: baryDerivative_mulVec
   baryDerivative_mulVec: proof_shape: bind-only; escape_witness: none; consumer: gaudin_mulVec
   gaudin_mulVec: proof_shape: bind-only; escape_witness: none; consumer: gaudin_primitive_column, gaudin_zero_eigenvector
   nodal_derivative_nonroot: proof_shape: bind-only; escape_witness: none; consumer: primitive_poles_sum, gaudin_zero_eigenvector
   gaudin_zero_eigenvector: proof_shape: bind-only; escape_witness: none; consumer: gaudin_rectangular_det_zero
   gaudin_kernel_entry_ne_zero: proof_shape: bind-only; escape_witness: none; consumer: gaudin_rectangular_det_zero
   gaudin_apply: proof_shape: bind-only; escape_witness: none; consumer: gaudinDetPolynomial_node_minor, gaudin_append
   gaudin_rectangular_det_zero: proof_shape: bind-only; escape_witness: none; consumer: gaudinDetPolynomial_degree
   gaudinDetPolynomial_degree: proof_shape: bind-only; escape_witness: none; consumer: gaudin_permanent
   gaudinDetPolynomial_eval: proof_shape: bind-only; escape_witness: none; consumer: gaudinDetPolynomial_node_minor, gaudinDetPolynomial_last
   det_single_unit_row: proof_shape: bind-only; escape_witness: none; consumer: gaudinDetPolynomial_node_minor
   gaudinDetPolynomial_node_minor: proof_shape: bind-only; escape_witness: none; consumer: gaudin_permanent
   prod_swap_succ_eq_erase: proof_shape: bind-only; escape_witness: none; consumer: gaudin_permanent
   lagrange_coefficient_cancellation: proof_shape: bind-only; escape_witness: none; consumer: gaudin_permanent
   prod_erase_mul_inverse: proof_shape: bind-only; escape_witness: none; consumer: gaudin_permanent
   gaudin_append: proof_shape: bind-only; escape_witness: none; consumer: gaudinDetPolynomial_last
   gaudinDetPolynomial_last: proof_shape: bind-only; escape_witness: none; consumer: gaudin_permanent
   gaudin_permanent: proof_shape: content; escape_witness: CycleGeodesic.gaudin_permanent; consumer: primitive_scaled_permanent
   escape_witness: CycleGeodesic.gaudin_permanent: ∀ n : ℕ, ∀ x y : Fin n → ℂ, Function.Injective x → (∀ i j, x i ≠ y j) → (gaudin x y).det = (cauchy x y).permanent
   admission_basis: escape-witness
   Direct frozen dependencies: none at the immutable origin/dev baseline.
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Complex.Basic

noncomputable section
open scoped BigOperators
open Finset Polynomial Matrix Equiv
namespace CycleGeodesic

def cauchy {n : ℕ} (x y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (x i - y j)⁻¹

private lemma permanent_succ_column_zero {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.permanent = ∑ i : Fin (n + 1), A i 0 *
      (A.submatrix (fun j => Equiv.swap 0 i j.succ) Fin.succ).permanent := by
  unfold Matrix.permanent
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Matrix.submatrix_apply, Finset.mul_sum]

private lemma inverse_prod_mul_erase {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (f : ι → F) {i : ι} (hi : i ∈ s) (hf : ∀ j ∈ s, f j ≠ 0) :
    (∏ j ∈ s, f j)⁻¹ * (∏ j ∈ s.erase i, f j) = (f i)⁻¹ := by
  have hp : (∏ j ∈ s.erase i, f j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_of_mem_erase hj))
  rw [← Finset.mul_prod_erase s f hi, mul_inv]
  field_simp

private lemma lagrange_basis_nodal_erase {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (x : ι → F) {i : ι} (hi : i ∈ s) :
    Lagrange.basis s x i = C (Lagrange.nodalWeight s x i) * Lagrange.nodal (s.erase i) x := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi, Lagrange.nodal_erase_eq_nodal_div hi]

private lemma derivative_lagrange_basis_diagonal {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (x : ι → F) (hx : Set.InjOn x s) {i : ι} (hi : i ∈ s) :
    (derivative (Lagrange.basis s x i)).eval (x i) = ∑ j ∈ s.erase i, (x i - x j)⁻¹ := by
  rw [lagrange_basis_nodal_erase s x hi, derivative_mul]
  simp only [derivative_C, zero_mul, zero_add, eval_mul, eval_C,
    Lagrange.derivative_nodal, eval_finsetSum, mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Lagrange.nodalWeight_eq_eval_nodal_erase_inv, Lagrange.eval_nodal, Lagrange.eval_nodal]
  exact inverse_prod_mul_erase (s.erase i) (fun k => x i - x k) hj (by
    intro k hk
    exact sub_ne_zero.mpr (fun heq => (Finset.mem_erase.mp hk).1 (hx (Finset.mem_of_mem_erase hk) hi heq.symm)))

private lemma derivative_lagrange_basis_off_diagonal {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (x : ι → F) (hx : Set.InjOn x s) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) :
    (derivative (Lagrange.basis s x j)).eval (x i) =
      Lagrange.nodalWeight s x j / (Lagrange.nodalWeight s x i * (x i - x j)) := by
  have hxij : x i - x j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hx hi hj h))
  have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hi' : i ∈ s.erase j := Finset.mem_erase.mpr ⟨hij, hi⟩
  rw [lagrange_basis_nodal_erase s x hj, derivative_mul]
  simp only [derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  rw [Lagrange.eval_nodal_derivative_eval_node_eq hi', Lagrange.eval_nodal, Finset.erase_right_comm]
  have hprod : (∏ k ∈ (s.erase i).erase j, (x i - x k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have hki := Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)
    exact sub_ne_zero.mpr (fun heq => hki.1 (hx hki.2 hi heq.symm))
  simp only [Lagrange.nodalWeight_eq_eval_nodal_erase_inv, Lagrange.eval_nodal]
  rw [← Finset.mul_prod_erase (s.erase i) (fun k => x i - x k) hj']
  field_simp

private lemma derivative_interpolation_formula {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (x : ι → F) (hx : Function.Injective x) (p : F[X]) (hp : p.degree < Fintype.card ι) (i : ι) :
    p.derivative.eval (x i) =
      (∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹) * p.eval (x i) +
      ∑ j ∈ Finset.univ.erase i,
        (Lagrange.nodalWeight Finset.univ x j /
          (Lagrange.nodalWeight Finset.univ x i * (x i - x j))) * p.eval (x j) := by
  have hp' : p.degree < (Finset.univ : Finset ι).card := by simpa using hp
  have hx' : Set.InjOn x (Finset.univ : Finset ι) := hx.injOn
  conv_lhs => rw [Lagrange.eq_interpolate hx' hp']
  simp only [Lagrange.interpolate_apply, derivative_sum, derivative_mul, derivative_C,
    zero_mul, zero_add, eval_finsetSum, eval_mul, eval_C]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    derivative_lagrange_basis_diagonal Finset.univ x hx' (Finset.mem_univ i),
    mul_comm (p.eval (x i))]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [derivative_lagrange_basis_off_diagonal Finset.univ x hx'
    (Finset.mem_univ i) (Finset.mem_univ j) (Finset.mem_erase.mp hj).1.symm, mul_comm]

def baryDerivative {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => if i = j then ∑ k ∈ Finset.univ.erase i, (x i - x k)⁻¹ else (x i - x j)⁻¹

def gaudin {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (x : ι → ℂ) (y : κ → ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ∑ j, (x i - y j)⁻¹) - baryDerivative x

private lemma baryDerivative_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (p : ℂ[X]) (hp : p.degree < Fintype.card ι) :
    baryDerivative x *ᵥ (fun i => Lagrange.nodalWeight Finset.univ x i * p.eval (x i)) =
      fun i => Lagrange.nodalWeight Finset.univ x i * p.derivative.eval (x i) := by
  funext i
  have hwi := Lagrange.nodalWeight_ne_zero hx.injOn (Finset.mem_univ i)
  have hd := derivative_interpolation_formula x hx p hp i
  rw [hd, mul_add, mul_sum]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [baryDerivative, ite_true]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hxij : x i - x j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hx h))
    rw [if_neg hij]
    field_simp

lemma gaudin_mulVec {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (x : ι → ℂ) (hx : Function.Injective x) (y : κ → ℂ)
    (p : ℂ[X]) (hp : p.degree < Fintype.card ι) :
    gaudin x y *ᵥ (fun i => Lagrange.nodalWeight Finset.univ x i * p.eval (x i)) =
      fun i => Lagrange.nodalWeight Finset.univ x i *
        ((∑ j, (x i - y j)⁻¹) * p.eval (x i) - p.derivative.eval (x i)) := by
  rw [gaudin, Matrix.sub_mulVec, baryDerivative_mulVec x hx p hp]
  funext i
  simp only [Pi.sub_apply, Matrix.mulVec_diagonal]
  ring

lemma nodal_derivative_nonroot {ι : Type*} [Fintype ι]
    (y : ι → ℂ) {z : ℂ} (hz : ∀ j, z ≠ y j) :
    (Lagrange.nodal Finset.univ y).derivative.eval z =
      (Lagrange.nodal Finset.univ y).eval z * ∑ j, (z - y j)⁻¹ := by
  classical
  rw [Lagrange.derivative_nodal, eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Lagrange.eval_nodal]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => z - y k) (Finset.mem_univ j)]
  have hzj : z - y j ≠ 0 := sub_ne_zero.mpr (hz j)
  field_simp

private lemma gaudin_zero_eigenvector {n : ℕ} (x : Fin (n + 1) → ℂ)
    (hx : Function.Injective x) (y : Fin n → ℂ) (hxy : ∀ i j, x i ≠ y j) :
    gaudin x y *ᵥ (fun i => Lagrange.nodalWeight Finset.univ x i *
      (Lagrange.nodal Finset.univ y).eval (x i)) = 0 := by
  rw [gaudin_mulVec x hx y (Lagrange.nodal Finset.univ y) (by
    rw [Lagrange.degree_nodal]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_self n)]
  funext i
  rw [nodal_derivative_nonroot y (hxy i)]
  simp [mul_comm]

private lemma gaudin_kernel_entry_ne_zero {n : ℕ} (x : Fin (n + 1) → ℂ)
    (hx : Function.Injective x) (y : Fin n → ℂ) (hxy : ∀ i j, x i ≠ y j) (i : Fin (n + 1)) :
    Lagrange.nodalWeight Finset.univ x i * (Lagrange.nodal Finset.univ y).eval (x i) ≠ 0 := by
  apply mul_ne_zero (Lagrange.nodalWeight_ne_zero hx.injOn (Finset.mem_univ i))
  exact Lagrange.eval_nodal_not_at_node (fun j _ => hxy i j)

private lemma gaudin_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (x : ι → ℂ) (y : κ → ℂ) (i j : ι) :
    gaudin x y i j = if i = j then (∑ k, (x i - y k)⁻¹) - (∑ k, (x i - x k)⁻¹)
      else -(x i - x j)⁻¹ := by
  classical
  by_cases hij : i = j
  · subst j
    simp [gaudin, baryDerivative, Matrix.diagonal_apply, Finset.sum_erase_eq_sub]
  · simp [gaudin, baryDerivative, Matrix.diagonal_apply, hij]

private lemma gaudin_rectangular_det_zero {n : ℕ} (x : Fin (n + 1) → ℂ)
    (hx : Function.Injective x) (y : Fin n → ℂ) (hxy : ∀ i j, x i ≠ y j) :
    (gaudin x y).det = 0 := by
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (gaudin_zero_eigenvector x hx y hxy)
    (mem_nonZeroDivisors_of_ne_zero (gaudin_kernel_entry_ne_zero x hx y hxy 0))

private def gaudinDetPolynomial {n : ℕ} (x : Fin (n + 1) → ℂ) (y : Fin n → ℂ) : ℂ[X] :=
  (((X : ℂ[X]) • (-gaudin x y).map C) +
    (Matrix.diagonal x * gaudin x y + 1).map C).det

private lemma gaudinDetPolynomial_degree {n : ℕ} (x : Fin (n + 1) → ℂ)
    (hx : Function.Injective x) (y : Fin n → ℂ) (hxy : ∀ i j, x i ≠ y j) :
    (gaudinDetPolynomial x y).degree < (n + 1 : ℕ) := by
  have hle : (gaudinDetPolynomial x y).natDegree ≤ n + 1 := by
    simpa [gaudinDetPolynomial] using
      Polynomial.natDegree_det_X_add_C_le (-gaudin x y) (Matrix.diagonal x * gaudin x y + 1)
  have hcoeff : (gaudinDetPolynomial x y).coeff (n + 1) = 0 := by
    simpa [gaudinDetPolynomial, Matrix.det_neg, gaudin_rectangular_det_zero x hx y hxy] using
      Polynomial.coeff_det_X_add_C_card (-gaudin x y) (Matrix.diagonal x * gaudin x y + 1)
  have hlt : (gaudinDetPolynomial x y).natDegree < n + 1 := by
    apply lt_of_le_of_ne hle
    intro heq
    have hp : gaudinDetPolynomial x y ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at heq
      omega
    have hc := (Polynomial.leadingCoeff_ne_zero.mpr hp)
    rw [← Polynomial.coeff_natDegree, heq, hcoeff] at hc
    exact hc rfl
  exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hlt)

private lemma gaudinDetPolynomial_eval {n : ℕ} (x : Fin (n + 1) → ℂ) (y : Fin n → ℂ) (z : ℂ) :
    (gaudinDetPolynomial x y).eval z =
      (Matrix.diagonal (fun i => x i - z) * gaudin x y + 1).det := by
  unfold gaudinDetPolynomial
  change (Polynomial.evalRingHom z) ((X • (-gaudin x y).map C) +
    (Matrix.diagonal x * gaudin x y + 1).map C).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul,
    Polynomial.coe_evalRingHom]
  ring

private lemma det_single_unit_row {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (hrow : ∀ j, A i j = if i = j then 1 else 0) :
    A.det = (A.submatrix (fun j : Fin n => Equiv.swap 0 i j.succ) (fun j : Fin n => Equiv.swap 0 i j.succ)).det := by
  have h := Matrix.det_submatrix_equiv_self (Equiv.swap 0 i) A
  rw [← h, Matrix.det_succ_row_zero]
  have hrow' : ∀ j, A (Equiv.swap 0 i 0) (Equiv.swap 0 i j) = if j = 0 then 1 else 0 := by
    intro j
    rw [Equiv.swap_apply_left, hrow]
    have heq : i = Equiv.swap 0 i j ↔ j = 0 := by
      rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    simp only [heq]
  simp only [Matrix.submatrix_apply, hrow']
  rw [Finset.sum_eq_single 0]
  · simp [Matrix.submatrix_submatrix, Function.comp_def]
  · intro j hj hj0
    simp [hj0]
  · simp

private lemma gaudinDetPolynomial_node_minor {n : ℕ} (x : Fin (n + 1) → ℂ)
    (hx : Function.Injective x) (y : Fin n → ℂ) (i : Fin (n + 1)) :
    (gaudinDetPolynomial x y).eval (x i) =
      (∏ j : Fin n, (x (Equiv.swap 0 i j.succ) - x i)) *
        (gaudin (fun j : Fin n => x (Equiv.swap 0 i j.succ)) y).det := by
  let e := Equiv.swap (0 : Fin (n + 1)) i
  let f : Fin n → Fin (n + 1) := fun j => e j.succ
  have hf : Function.Injective f := e.injective.comp (Fin.succ_injective n)
  have hfi (j : Fin n) : f j ≠ i := by
    dsimp [f, e]
    intro heq
    have h := Equiv.swap_apply_eq_iff.mp heq
    rw [Equiv.swap_apply_right] at h
    exact Fin.succ_ne_zero j h
  have hsum (r : Fin n) : (∑ k : Fin (n + 1), (x (f r) - x k)⁻¹) =
      (x (f r) - x i)⁻¹ + ∑ k : Fin n, (x (f r) - x (f k))⁻¹ := by
    rw [← Equiv.sum_comp e (fun k => (x (f r) - x k)⁻¹), Fin.sum_univ_succ]
    simp only [e, Equiv.swap_apply_left]
    rfl
  rw [gaudinDetPolynomial_eval]
  rw [det_single_unit_row _ i (by intro j; simp [Matrix.diagonal_mul, Matrix.one_apply])]
  have hminor :
      (Matrix.diagonal (fun r => x r - x i) * gaudin x y + 1).submatrix f f =
      Matrix.diagonal (fun r => x (f r) - x i) * gaudin (fun r => x (f r)) y := by
    ext r c
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.diagonal_mul,
      gaudin_apply, Matrix.one_apply]
    by_cases hrc : r = c
    · subst c
      simp only [ite_true, hsum]
      have hn : x (f r) - x i ≠ 0 := sub_ne_zero.mpr (fun heq => hfi r (hx heq))
      field_simp
      ring
    · have hfc : f r ≠ f c := fun heq => hrc (hf heq)
      simp only [hfc, hrc, ite_false, add_zero]
  change ((Matrix.diagonal (fun r => x r - x i) * gaudin x y + 1).submatrix f f).det = _
  rw [hminor]
  rw [Matrix.det_mul, Matrix.det_diagonal]

private lemma prod_swap_succ_eq_erase {M : Type*} [CommMonoid M] {n : ℕ}
    (i : Fin (n + 1)) (h : Fin (n + 1) → M) :
    (∏ k : Fin n, h (Equiv.swap 0 i k.succ)) = ∏ k ∈ Finset.univ.erase i, h k := by
  let e := Equiv.swap (0 : Fin (n + 1)) i
  have he (k : Fin n) : e k.succ ≠ i := by
    intro hi
    have hh := Equiv.swap_apply_eq_iff.mp hi
    rw [Equiv.swap_apply_right] at hh
    exact Fin.succ_ne_zero k hh
  have hall : (∏ k : Fin (n + 1), if k = i then (1 : M) else h k) =
      ∏ k ∈ Finset.univ.erase i, h k := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => if k = i then (1 : M) else h k) (Finset.mem_univ i)]
    simp only [ite_true, one_mul]
    apply Finset.prod_congr rfl
    intro k hk
    simp only [if_neg (Finset.mem_erase.mp hk).1]
  rw [← Equiv.prod_comp e (fun k => if k = i then (1 : M) else h k), Fin.prod_univ_succ] at hall
  simpa [e, Equiv.swap_apply_left, he] using hall

private lemma lagrange_coefficient_cancellation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (i : ι) (z : ℂ) :
    (∏ k ∈ Finset.univ.erase i, (x k - x i)) * (Lagrange.basis Finset.univ x i).eval z =
      ∏ k ∈ Finset.univ.erase i, (x k - z) := by
  simp only [Lagrange.basis, Polynomial.eval_prod, Lagrange.basisDivisor,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [← Finset.prod_mul_distrib (s := Finset.univ.erase i)
    (f := fun k => x k - x i) (g := fun k => (x i - x k)⁻¹ * (z - x k))]
  apply Finset.prod_congr rfl
  intro k hk
  have hki : x i - x k ≠ 0 :=
    sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hk).1 (hx h.symm))
  field_simp
  ring

private lemma prod_erase_mul_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (z : ℂ) (hz : ∀ i, x i ≠ z) (i : ι) :
    (∏ k, (x k - z)) * (x i - z)⁻¹ = ∏ k ∈ Finset.univ.erase i, (x k - z) := by
  rw [show (∏ k, (x k - z)) = (x i - z) * (∏ k ∈ Finset.univ.erase i, (x k - z)) from
    (Finset.mul_prod_erase Finset.univ (fun k => x k - z) (Finset.mem_univ i)).symm]
  have hi : x i - z ≠ 0 := sub_ne_zero.mpr (hz i)
  field_simp

private lemma gaudin_append {n : ℕ} (x y : Fin (n + 1) → ℂ) :
    gaudin x y = gaudin x (fun j : Fin n => y j.succ) +
      Matrix.diagonal (fun i => (x i - y 0)⁻¹) := by
  ext i j
  simp only [gaudin_apply, Matrix.add_apply, Matrix.diagonal_apply, Fin.sum_univ_succ]
  by_cases hij : i = j
  · simp [hij]
    ring
  · simp [hij]

private lemma gaudinDetPolynomial_last {n : ℕ} (x y : Fin (n + 1) → ℂ)
    (hxy : ∀ i j, x i ≠ y j) :
    (gaudinDetPolynomial x (fun j : Fin n => y j.succ)).eval (y 0) =
      (∏ i, (x i - y 0)) * (gaudin x y).det := by
  rw [gaudinDetPolynomial_eval]
  have hM : Matrix.diagonal (fun i => x i - y 0) * gaudin x y =
      Matrix.diagonal (fun i => x i - y 0) * gaudin x (fun j : Fin n => y j.succ) + 1 := by
    rw [gaudin_append, Matrix.mul_add]
    congr 1
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      exact mul_inv_cancel₀ (sub_ne_zero.mpr (hxy i 0))
    · simp [hij]
  rw [← hM, Matrix.det_mul, Matrix.det_diagonal]

lemma gaudin_permanent : ∀ n : ℕ, ∀ x y : Fin n → ℂ,
    Function.Injective x → (∀ i j, x i ≠ y j) → (gaudin x y).det = (cauchy x y).permanent := by
  intro n
  induction n with
  | zero =>
    intro x y hx hxy
    simp [Matrix.det_isEmpty, Matrix.permanent_isEmpty]
  | succ n ih =>
    intro x y hx hxy
    let yt : Fin n → ℂ := fun j => y j.succ
    let F := gaudinDetPolynomial x yt
    have hxt : ∀ i j, x i ≠ yt j := fun i j => hxy i j.succ
    have hdeg : F.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
      simpa [F] using gaudinDetPolynomial_degree x hx yt hxt
    have hnodes (i : Fin (n + 1)) :
        F.eval (x i) = (∏ k ∈ Finset.univ.erase i, (x k - x i)) *
          (cauchy (fun j : Fin n => x (Equiv.swap 0 i j.succ)) yt).permanent := by
      rw [gaudinDetPolynomial_node_minor x hx yt i]
      rw [ih (fun j : Fin n => x (Equiv.swap 0 i j.succ)) yt
        (by simpa [Function.comp_def] using hx.comp ((Equiv.swap 0 i).injective.comp (Fin.succ_injective n)))
        (fun k j => hxy _ j.succ)]
      rw [prod_swap_succ_eq_erase i (fun k => x k - x i)]
    have hpoly : F = Lagrange.interpolate Finset.univ x (fun i => F.eval (x i)) :=
      Lagrange.eq_interpolate hx.injOn hdeg
    have hz := congrArg (fun p : ℂ[X] => p.eval (y 0)) hpoly
    rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at hz
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at hz
    have hprod : (∏ i, (x i - y 0)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hxy i 0))
    apply (mul_left_cancel₀ hprod)
    calc
      (∏ i, (x i - y 0)) * (gaudin x y).det = F.eval (y 0) :=
        (gaudinDetPolynomial_last x y hxy).symm
      _ = ∑ i, F.eval (x i) * (Lagrange.basis Finset.univ x i).eval (y 0) := hz
      _ = ∑ i, (cauchy (fun j : Fin n => x (Equiv.swap 0 i j.succ)) yt).permanent *
          (∏ k ∈ Finset.univ.erase i, (x k - y 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hnodes]
        rw [mul_assoc, mul_comm ((cauchy (fun j : Fin n => x (Equiv.swap 0 i j.succ)) yt).permanent),
          ← mul_assoc, lagrange_coefficient_cancellation x hx i (y 0), mul_comm]
      _ = (∏ i, (x i - y 0)) * (cauchy x y).permanent := by
        rw [permanent_succ_column_zero, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← prod_erase_mul_inverse x (y 0) (fun i => hxy i 0) i]
        have hminor : (cauchy x y).submatrix (fun j => Equiv.swap 0 i j.succ) Fin.succ =
            cauchy (fun j : Fin n => x (Equiv.swap 0 i j.succ)) yt := rfl
        rw [hminor]
        simp only [cauchy]
        ring

#print axioms gaudin_mulVec
#print axioms nodal_derivative_nonroot
#print axioms gaudin_permanent
end CycleGeodesic
