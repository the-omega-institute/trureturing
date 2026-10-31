/- GID: D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: No universal slope-one bound controls the Laplacian spread of digraphs. -/

/-
proof_shape: all theorem declarations: bind-only.
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22040
admission_basis: open-problem-resolution (#21874; Refuted)
The real adjacency entries are casts of FiniteGraphEntropy.adjacency; the directed degrees are their explicit row and column sums.
Direct frozen dependencies (declaration statement_id):
  D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.adjacency: sha256:333274b8af876930296e18e1a33684b7a225e27fb0b15298aee0f7a8ed138cd0
Declaration classification and consumers:
  outDegree: definition; consumers: BarrettBalancedLaplacianSpreadGap.degree_le_order_sub_one, BarrettBalancedLaplacianSpreadGap.degree_rayleigh_bounds, BarrettBalancedLaplacianSpreadGap.laplacian_col_sum, BarrettBalancedLaplacianSpreadGap.laplacian_diag, BarrettBalancedLaplacianSpreadGap.laplacian_symAdj_quad, BarrettBalancedLaplacianSpreadGap.outDegree_nat, BarrettBalancedLaplacianSpreadGap.regular_of_spread_le_one, BarrettBalancedLaplacianSpreadGap.result, BarrettBalancedLaplacianSpreadGap.symAdj_centered_bound, BarrettBalancedLaplacianSpreadGap.symAdj_entry_dichotomy, BarrettBalancedLaplacianSpreadGap.symAdj_pair_bounds, BarrettBalancedLaplacianSpreadGap.symAdj_rows, BarrettBalancedLaplacianSpreadGap.symAdj_scalar_implies_zero, Balanced, laplacian
  inDegree: definition; consumers: BarrettBalancedLaplacianSpreadGap.laplacian_col_sum, BarrettBalancedLaplacianSpreadGap.symAdj_rows, Balanced
  laplacian: definition; consumers: BarrettBalancedLaplacianSpreadGap.degree_rayleigh_bounds, BarrettBalancedLaplacianSpreadGap.laplacian_col_sum, BarrettBalancedLaplacianSpreadGap.laplacian_diag, BarrettBalancedLaplacianSpreadGap.laplacian_row_sum, BarrettBalancedLaplacianSpreadGap.laplacian_symAdj_quad, BarrettBalancedLaplacianSpreadGap.quadraticValues_nonempty, BarrettBalancedLaplacianSpreadGap.quadratic_bounds, BarrettBalancedLaplacianSpreadGap.spread_zero_of_scalar, BarrettBalancedLaplacianSpreadGap.symAdj_centered_bound, BarrettBalancedLaplacianSpreadGap.symAdj_pair_bounds, BarrettBalancedLaplacianSpreadGap.symAdj_scalar_implies_zero, normalized_mem, quadraticValues, quadraticValues_isCompact, rayleigh_mem
  Balanced: definition; consumers: BarrettBalancedLaplacianSpreadGap.claim, BarrettBalancedLaplacianSpreadGap.degree_rayleigh_bounds, BarrettBalancedLaplacianSpreadGap.laplacian_col_sum, BarrettBalancedLaplacianSpreadGap.regular_of_spread_le_one, BarrettBalancedLaplacianSpreadGap.result, BarrettBalancedLaplacianSpreadGap.symAdj_rows
  quadraticValues: definition; consumers: BarrettBalancedLaplacianSpreadGap.extrema_attained, BarrettBalancedLaplacianSpreadGap.quadraticValues_nonempty, BarrettBalancedLaplacianSpreadGap.quadratic_bounds, BarrettBalancedLaplacianSpreadGap.spread_zero_of_scalar, alpha, beta, blowup_spread, normalized_mem, quadraticValues_isCompact, rayleigh_mem, spread_ge_values
  alpha: definition; consumers: BarrettBalancedLaplacianSpreadGap.degree_rayleigh_bounds, BarrettBalancedLaplacianSpreadGap.extrema_attained, BarrettBalancedLaplacianSpreadGap.quadratic_bounds, BarrettBalancedLaplacianSpreadGap.regular_of_spread_le_one, BarrettBalancedLaplacianSpreadGap.result, BarrettBalancedLaplacianSpreadGap.spread_zero_of_scalar, BarrettBalancedLaplacianSpreadGap.symAdj_centered_bound, BarrettBalancedLaplacianSpreadGap.symAdj_entry_dichotomy, BarrettBalancedLaplacianSpreadGap.symAdj_pair_bounds, spread, spread_ge_values
  beta: definition; consumers: BarrettBalancedLaplacianSpreadGap.degree_rayleigh_bounds, BarrettBalancedLaplacianSpreadGap.extrema_attained, BarrettBalancedLaplacianSpreadGap.quadratic_bounds, BarrettBalancedLaplacianSpreadGap.regular_of_spread_le_one, BarrettBalancedLaplacianSpreadGap.result, BarrettBalancedLaplacianSpreadGap.spread_zero_of_scalar, BarrettBalancedLaplacianSpreadGap.symAdj_centered_bound, BarrettBalancedLaplacianSpreadGap.symAdj_entry_dichotomy, BarrettBalancedLaplacianSpreadGap.symAdj_pair_bounds, spread, spread_ge_values
  spread: definition; consumers: BarrettBalancedLaplacianSpreadGap.claim, BarrettBalancedLaplacianSpreadGap.regular_of_spread_le_one, BarrettBalancedLaplacianSpreadGap.result, BarrettBalancedLaplacianSpreadGap.spread_zero_of_scalar, BarrettBalancedLaplacianSpreadGap.symAdj_centered_bound, BarrettBalancedLaplacianSpreadGap.symAdj_entry_dichotomy, BarrettBalancedLaplacianSpreadGap.symAdj_scalar_implies_zero, blowup_spread, claim, result, spread_ge_values
  quadraticValues_isCompact: bind-only; consumers: BarrettBalancedLaplacianSpreadGap.extrema_attained, BarrettBalancedLaplacianSpreadGap.quadratic_bounds, spread_ge_values
  rayleigh_mem: bind-only; consumers: BarrettBalancedLaplacianSpreadGap.quadraticValues_nonempty, BarrettBalancedLaplacianSpreadGap.quadratic_bounds, normalized_mem
  energy: definition; consumers: base_x, base_y, blowup_spread, energy_expansion, lifted_energy, normalized_mem
  energy_expansion: bind-only; consumers: base_x, base_y, lifted_energy
  normalized_mem: bind-only; consumers: blowup_spread
  spread_ge_values: bind-only; consumers: blowup_spread
  base: definition; consumers: base_loopless, base_x, base_y, blowup, blowup_spread, lifted_energy
  vx: definition; consumers: base_x, blowup_spread
  vy: definition; consumers: base_y, blowup_spread
  base_loopless: bind-only; consumers: result
  base_x: bind-only; consumers: blowup_spread
  base_y: bind-only; consumers: blowup_spread
  blowup: definition; consumers: blowup_spread, lifted_energy, result
  sum_cluster: bind-only; consumers: blowup_spread, lifted_energy
  lifted_energy: bind-only; consumers: blowup_spread
  blowup_spread: bind-only; consumers: result
  claim: definition; consumers: result
  result: bind-only; consumers: settling result
-/

import D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
open Matrix
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.BarrettLaplacianSpreadSlopeRefutation
/-- The number of edges leaving i. -/
def outDegree {n : ℕ} (Γ : Digraph (Fin n)) (i : Fin n) : ℝ :=
  ∑ j : Fin n, ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ)) i j

/-- The number of edges entering i. -/
def inDegree {n : ℕ} (Γ : Digraph (Fin n)) (i : Fin n) : ℝ :=
  ∑ j : Fin n, ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ)) j i

/-- Section 2: L = D - A, with D_ii = d⁺(i). -/
def laplacian {n : ℕ} (Γ : Digraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (outDegree Γ) - ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ))

/-- Section 4: d⁺(i) = d⁻(i) at every vertex. -/
def Balanced {n : ℕ} (Γ : Digraph (Fin n)) : Prop :=
  ∀ i : Fin n, outDegree Γ i = inDegree Γ i

/-- Real values xᵀ L x on the Euclidean unit sphere perpendicular to e. -/
def quadraticValues {n : ℕ} (Γ : Digraph (Fin n)) : Set ℝ :=
  {t : ℝ | ∃ x : EuclideanSpace ℝ (Fin n),
    (∑ i : Fin n, x i) = 0 ∧ ‖x‖ = 1 ∧
    t = dotProduct (fun i => x i) ((laplacian Γ).mulVec (fun i => x i))}

/-- Section 2: the minimum of xᵀ L x under the displayed constraints. -/
def alpha {n : ℕ} (Γ : Digraph (Fin n)) : ℝ := sInf (quadraticValues Γ)

/-- Section 2: the maximum of xᵀ L x under the displayed constraints. -/
def beta {n : ℕ} (Γ : Digraph (Fin n)) : ℝ := sSup (quadraticValues Γ)

/-- Section 3: sp(Γ) = β(Γ) - α(Γ). -/
def spread {n : ℕ} (Γ : Digraph (Fin n)) : ℝ := beta Γ - alpha Γ

lemma quadraticValues_isCompact {n : ℕ} (Γ : Digraph (Fin n)) :
  IsCompact (quadraticValues Γ) := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (x ⬝ᵥ ((laplacian Γ) *ᵥ x))
  have hf : Continuous f := by
    unfold f dotProduct Matrix.mulVec
    fun_prop
  have hg : Continuous (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, x i) := by
    fun_prop
  have hc : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩
      {x : EuclideanSpace ℝ (Fin n) | ∑ i, x i = 0}) :=
    (isCompact_sphere _ _).inter_right (isClosed_eq hg continuous_const)
  have heq : quadraticValues Γ = f ''
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩
        {x : EuclideanSpace ℝ (Fin n) | ∑ i, x i = 0}) := by
    ext t
    constructor
    · rintro ⟨x, hx, hn, rfl⟩
      exact ⟨x, ⟨by simpa using hn, hx⟩, rfl⟩
    · rintro ⟨x, ⟨hn, hx⟩, rfl⟩
      exact ⟨x, hx, by simpa using hn, rfl⟩
  rw [heq]
  exact hc.image hf

lemma rayleigh_mem {n : ℕ} (Γ : Digraph (Fin n)) (x : Fin n → ℝ)
    (hs : ∑ i, x i = 0) (hx : x ≠ 0) :
    (x ⬝ᵥ ((laplacian Γ) *ᵥ x)) / (x ⬝ᵥ x) ∈ quadraticValues Γ := by
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hv : v ≠ 0 := by
    intro h
    apply hx
    exact congrArg WithLp.ofLp h
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hsq : x ⬝ᵥ x = ‖v‖ ^ 2 := by
    simpa [dotProduct, v, pow_two] using (EuclideanSpace.real_norm_sq_eq v).symm
  refine ⟨‖v‖⁻¹ • v, ?_, ?_, ?_⟩
  · simp [Finset.sum_mul, ← Finset.mul_sum, hs, v]
  · simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), hn]
  · change (x ⬝ᵥ ((laplacian Γ) *ᵥ x)) / (x ⬝ᵥ x) =
        ((‖v‖⁻¹ • x) ⬝ᵥ ((laplacian Γ) *ᵥ (‖v‖⁻¹ • x)))
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    rw [hsq]
    field_simp

private def energy {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  dotProduct v ((Matrix.diagonal (fun i => ∑ j, A i j) - A).mulVec v)

private theorem energy_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    energy A v = ∑ i, ∑ j, A i j * (v i * v i - v i * v j) := by
  classical
  unfold energy
  rw [Matrix.sub_mulVec, dotProduct_sub]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  change (∑ i, v i * ((∑ j, A i j) * v i)) -
    (∑ i, v i * (∑ j, A i j * v j)) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.sum_mul, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> ring

private theorem normalized_mem {n : ℕ} (Γ : Digraph (Fin n)) (v : Fin n → ℝ)
    (hz : ∑ i, v i = 0) (hp : 0 < ∑ i, (v i) ^ 2) :
    energy (((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ))) v / (∑ i, (v i) ^ 2) ∈ quadraticValues Γ := by
  have hv : v ≠ 0 := by
    intro h
    simp [h] at hp
  change dotProduct v ((laplacian Γ).mulVec v) / (∑ i, (v i) ^ 2) ∈ quadraticValues Γ
  simpa only [dotProduct, pow_two] using rayleigh_mem Γ v hz hv

private theorem spread_ge_values {n : ℕ} (Γ : Digraph (Fin n)) {a b : ℝ}
    (ha : a ∈ quadraticValues Γ) (hb : b ∈ quadraticValues Γ) :
    a - b ≤ spread Γ := by
  exact sub_le_sub (le_csSup (quadraticValues_isCompact Γ).bddAbove ha) (csInf_le (quadraticValues_isCompact Γ).bddBelow hb)

private def base : Digraph (Fin 5) where
  Adj i j := if i = 0 then j = 2 else if i = 1 then j ≠ 1 else if i = 2 then j ≠ 2 else False

private def vx : Fin 5 → ℝ := ![2, 26, -26, -1, -1]
private def vy : Fin 5 → ℝ := ![0, 0, 0, 1, -1]

private theorem base_loopless : ∀ i, ¬ base.Adj i i := by
  intro i
  fin_cases i <;> norm_num [base]

private theorem base_x : (∑ i, vx i) = 0 ∧ (∑ i, (vx i)^2) = 1358 ∧
    energy (((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency base.Adj).map (Nat.cast : ℕ → ℝ))) vx = 6816 := by
  norm_num [vx, base, energy_expansion, D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency, Matrix.map_apply, Fin.sum_univ_succ]

private theorem base_y : (∑ i, vy i) = 0 ∧ (∑ i, (vy i)^2) = 2 ∧
    energy (((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency base.Adj).map (Nat.cast : ℕ → ℝ))) vy = 0 := by
  norm_num [vy, base, energy_expansion, D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency, Matrix.map_apply, Fin.sum_univ_succ]

private def blowup (m : ℕ) : Digraph (Fin (5*m)) where
  Adj i j := base.Adj ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm j).1))

private theorem sum_cluster (m : ℕ) (f : Fin 5 → ℝ) :
    (∑ i : Fin (5*m), f ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1))) = (m : ℝ) * ∑ i, f i := by
  calc
    _ = ∑ p : Fin 5 × Fin m, f p.1 := by
      simpa only [Equiv.symm_apply_apply] using
        ((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).sum_comp
          (fun i => f ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)))).symm
    _ = _ := by simp [Fintype.sum_prod_type, ← Finset.mul_sum]

private theorem lifted_energy (m : ℕ) (v : Fin 5 → ℝ) :
    energy (((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency (blowup m).Adj).map (Nat.cast : ℕ → ℝ))) (fun i => v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1))) =
      (m : ℝ)^2 * energy (((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency base.Adj).map (Nat.cast : ℕ → ℝ))) v := by
  simp only [energy_expansion]
  change (∑ i : Fin (5*m), ∑ j : Fin (5*m),
      ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency base.Adj).map (Nat.cast : ℕ → ℝ)) ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm j).1)) *
        (v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) * v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) - v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) * v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm j).1)))) = _
  have hinner (i : Fin (5*m)) :
      (∑ j : Fin (5*m), ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency base.Adj).map (Nat.cast : ℕ → ℝ)) ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm j).1)) *
        (v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) * v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) - v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) * v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm j).1)))) =
      (m : ℝ) * ∑ j : Fin 5, ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency base.Adj).map (Nat.cast : ℕ → ℝ)) ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) j *
        (v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) * v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) - v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) * v j) :=
    sum_cluster m (fun j => ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency base.Adj).map (Nat.cast : ℕ → ℝ)) ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) j *
      (v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) * v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) - v ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)) * v j))
  simp_rw [hinner]
  rw [← Finset.mul_sum, sum_cluster m (fun i : Fin 5 => ∑ j : Fin 5,
    ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency base.Adj).map (Nat.cast : ℕ → ℝ)) i j * (v i * v i - v i * v j))]
  ring

private theorem blowup_spread (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * (3408 / 679 : ℝ) ≤ spread (blowup m) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hx0 : (∑ i : Fin (5*m), vx ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1))) = 0 := by
    rw [sum_cluster, base_x.1, mul_zero]
  have hy0 : (∑ i : Fin (5*m), vy ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1))) = 0 := by
    rw [sum_cluster, base_y.1, mul_zero]
  have hx2 : (∑ i : Fin (5*m), (vx ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)))^2) = (m : ℝ)*1358 := by
    rw [sum_cluster m (fun i => (vx i)^2), base_x.2.1]
  have hy2 : (∑ i : Fin (5*m), (vy ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)))^2) = (m : ℝ)*2 := by
    rw [sum_cluster m (fun i => (vy i)^2), base_y.2.1]
  have hx := normalized_mem (blowup m) (fun i => vx ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1))) hx0 (by rw [hx2]; positivity)
  have hy := normalized_mem (blowup m) (fun i => vy ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1))) hy0 (by rw [hy2]; positivity)
  rw [lifted_energy, base_x.2.2, hx2] at hx
  rw [lifted_energy, base_y.2.2, hy2] at hy
  have hq : (m : ℝ)^2 * 6816 / ((m : ℝ)*1358) = (m : ℝ)*(3408/679) := by
    field_simp [ne_of_gt hmR]
    ring
  rw [hq] at hx
  norm_num at hy
  simpa using spread_ge_values (blowup m) hx hy

/-- Conjecture 20: one real intercept bounds every unweighted simple digraph. -/
def claim : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ), 2 ≤ n → ∀ (Γ : Digraph (Fin n)),
    (∀ i : Fin n, ¬ Γ.Adj i i) → spread Γ ≤ (n : ℝ) + C

theorem result : ¬ claim := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (679*C/13))
  have hm0 : 0 < m := by
    have h : (0 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact Nat.cast_pos.mp h
  have hn : 2 ≤ 5*m := by omega
  have hs := hC (5*m) hn (blowup m) (fun i => base_loopless ((((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5*m)).symm i).1)))
  have hl := blowup_spread m hm0
  have hnum : C < (m : ℝ)*13/679 := by
    have h := lt_of_le_of_lt (le_max_right 0 (679*C/13)) hm
    linarith
  push_cast at hs
  linarith


end D5.S3.Combinatorics.SpectralGraph.BarrettLaplacianSpreadSlopeRefutation
