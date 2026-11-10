/- GID: D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.result; claim=D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.claim
   digest: Independent clusters refute every universal slope-one Laplacian-spread bound. -/

/- Judgement form.
   admission_basis: open-problem-resolution (#21874; Refuted)
   Direct frozen dependencies: D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.adjacency.
   Declaration statement_id: unavailable in the existing report (owner source is frozen).
   Definitions: proof_shape: bind-only (definitional expressions); escape_witness: none.
   laplacian_owner: proof_shape: bind-only; escape_witness: none; consumer: normalized_mem.
   energy_expansion: proof_shape: bind-only; escape_witness: none; consumers: base_x, base_y,
     lifted_energy.
   energy_smul: proof_shape: bind-only; escape_witness: none; consumer: normalized_mem.
   quadratic_bounded: proof_shape: bind-only; escape_witness: none; consumer: spread_ge_values.
   normalized_mem: proof_shape: bind-only; escape_witness: none; consumer: blowup_spread.
   spread_ge_values: proof_shape: bind-only; escape_witness: none; consumer: blowup_spread.
   base_loopless: proof_shape: bind-only; escape_witness: none; consumer: result.
   base_x: proof_shape: bind-only; escape_witness: none; consumer: blowup_spread.
   base_y: proof_shape: bind-only; escape_witness: none; consumer: blowup_spread.
   sum_cluster: proof_shape: bind-only; escape_witness: none; consumers: lifted_energy,
     blowup_spread.
   lifted_energy: proof_shape: bind-only; escape_witness: none; consumer: blowup_spread.
   blowup_spread: proof_shape: bind-only; escape_witness: none; consumer: result.
   result: proof_shape: bind-only; escape_witness: none; consumer: settling result.
   The public result is the designated refutation result (`basis=refutes`) and is exempt from
     four-slot escape registration (CLAUDE.md §3.9).
   The literal 0/1 adjacency and row sum occur inside laplacian; proofs use the existing
     natural adjacency owner through laplacian_owner, with no duplicate adjacency or out-degree
     definition.
-/

import D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent-cluster counterexamples to a universal slope-one Laplacian-spread bound. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open D5.S1.Dynamics.Symbolic.FiniteGraphEntropy (adjacency)

namespace D5.S3.Combinatorics.SpectralGraph.BarrettLaplacianSpreadSlopeRefutation

/-- The out-degree Laplacian of a directed graph. -/
def laplacian {n : ℕ} (G : Digraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => ∑ j : Fin n,
    @ite ℝ (G.Adj i j) (Classical.propDecidable _) 1 0) -
    Matrix.of (fun i j => @ite ℝ (G.Adj i j) (Classical.propDecidable _) 1 0)

/-- Real quadratic values on zero-sum Euclidean unit vectors. -/
def quadraticValues {n : ℕ} (G : Digraph (Fin n)) : Set ℝ :=
  {t : ℝ | ∃ x : EuclideanSpace ℝ (Fin n),
    (∑ i : Fin n, x i) = 0 ∧ ‖x‖ = 1 ∧
    t = dotProduct (fun i => x i) ((laplacian G).mulVec (fun i => x i))}

/-- The lower restricted quadratic extremum. -/
def alpha {n : ℕ} (G : Digraph (Fin n)) : ℝ := sInf (quadraticValues G)

/-- The upper restricted quadratic extremum. -/
def beta {n : ℕ} (G : Digraph (Fin n)) : ℝ := sSup (quadraticValues G)

/-- The Laplacian spread. -/
def spread {n : ℕ} (G : Digraph (Fin n)) : ℝ := beta G - alpha G

private theorem laplacian_owner {n : ℕ} (G : Digraph (Fin n)) :
    laplacian G = Matrix.diagonal (fun i => ∑ j, (adjacency G.Adj i j : ℝ)) -
      Matrix.of (fun i j => (adjacency G.Adj i j : ℝ)) := by
  classical
  simp only [laplacian, adjacency, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

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

private theorem energy_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (c : ℝ) :
    energy A (fun i => c * v i) = c ^ 2 * energy A v := by
  classical
  change dotProduct (c • v)
      ((Matrix.diagonal (fun i => ∑ j, A i j) - A).mulVec (c • v)) = _
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  change c * (c * energy A v) = c ^ 2 * energy A v
  ring

private theorem quadratic_bounded {n : ℕ} (G : Digraph (Fin n)) :
    BddAbove (quadraticValues G) ∧ BddBelow (quadraticValues G) := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    dotProduct (fun i => x i) ((laplacian G).mulVec (fun i => x i))
  have hf : Continuous f := by
    unfold f dotProduct Matrix.mulVec
    fun_prop
  have hs : quadraticValues G ⊆ f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rintro t ⟨x, hx, hn, rfl⟩
    exact ⟨x, by simpa using hn, rfl⟩
  exact ⟨((isCompact_sphere _ _).bddAbove_image hf.continuousOn).mono hs,
    ((isCompact_sphere _ _).bddBelow_image hf.continuousOn).mono hs⟩

private theorem normalized_mem {n : ℕ} (G : Digraph (Fin n)) (v : Fin n → ℝ)
    (hz : ∑ i, v i = 0) (hp : 0 < ∑ i, (v i) ^ 2) :
    energy (Matrix.of (fun i j => (adjacency G.Adj i j : ℝ))) v /
      (∑ i, (v i) ^ 2) ∈ quadraticValues G := by
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hn2 : ‖w‖ ^ 2 = ∑ i, (v i) ^ 2 := EuclideanSpace.real_norm_sq_eq w
  have hn : ‖w‖ ≠ 0 := by
    intro h
    rw [h] at hn2
    norm_num at hn2
    linarith
  refine ⟨‖w‖⁻¹ • w, ?_, ?_, ?_⟩
  · change (∑ i, ‖w‖⁻¹ * v i) = 0
    rw [← Finset.mul_sum, hz, mul_zero]
  · exact norm_smul_inv_norm (norm_ne_zero_iff.mp hn)
  · simp only [laplacian_owner]
    change energy (Matrix.of (fun i j => (adjacency G.Adj i j : ℝ))) v / (∑ i, (v i) ^ 2) =
      energy (Matrix.of (fun i j => (adjacency G.Adj i j : ℝ))) (fun i => ‖w‖⁻¹ * v i)
    rw [energy_smul, ← hn2]
    field_simp [hn]

private theorem spread_ge_values {n : ℕ} (G : Digraph (Fin n)) {a b : ℝ}
    (ha : a ∈ quadraticValues G) (hb : b ∈ quadraticValues G) :
    a - b ≤ spread G := by
  have h := quadratic_bounded G
  exact sub_le_sub (le_csSup h.1 ha) (csInf_le h.2 hb)


private def base : Digraph (Fin 5) where
  Adj i j := if i = 0 then j = 2 else if i = 1 then j ≠ 1 else if i = 2 then j ≠ 2 else False

private def vx : Fin 5 → ℝ := ![2, 26, -26, -1, -1]
private def vy : Fin 5 → ℝ := ![0, 0, 0, 1, -1]

private theorem base_loopless : ∀ i, ¬ base.Adj i i := by
  intro i
  fin_cases i <;> norm_num [base]

private theorem base_x : (∑ i, vx i) = 0 ∧ (∑ i, (vx i)^2) = 1358 ∧
    energy (Matrix.of (fun i j => (adjacency base.Adj i j : ℝ))) vx = 6816 := by
  norm_num [energy_expansion, vx, base, adjacency, Matrix.of_apply, Fin.sum_univ_succ]

private theorem base_y : (∑ i, vy i) = 0 ∧ (∑ i, (vy i)^2) = 2 ∧
    energy (Matrix.of (fun i j => (adjacency base.Adj i j : ℝ))) vy = 0 := by
  norm_num [energy_expansion, vy, base, adjacency, Matrix.of_apply, Fin.sum_univ_succ]

private def blowup (m : ℕ) : Digraph (Fin (5 * m)) where
  Adj i j := base.Adj
    (((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5 * m)).symm i).1)
    (((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5 * m)).symm j).1)

private theorem sum_cluster (m : ℕ) (f : Fin 5 → ℝ) :
    (∑ i : Fin (5 * m),
      f (((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5 * m)).symm i).1)) =
        (m : ℝ) * ∑ i, f i := by
  calc
    _ = ∑ p : Fin 5 × Fin m, f p.1 := by
      simpa only [Equiv.symm_apply_apply] using
        ((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5 * m)).sum_comp
          (fun i => f (((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5 * m)).symm i).1))).symm
    _ = _ := by simp [Fintype.sum_prod_type, ← Finset.mul_sum]

private theorem lifted_energy (m : ℕ) (v : Fin 5 → ℝ) :
    energy (Matrix.of (fun i j => (adjacency (blowup m).Adj i j : ℝ)))
      (fun i => v (((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5 * m)).symm i).1)) =
        (m : ℝ) ^ 2 * energy (Matrix.of (fun i j => (adjacency base.Adj i j : ℝ))) v := by
  simp only [energy_expansion, Matrix.of_apply]
  let c : Fin (5 * m) → Fin 5 := fun i =>
    ((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5 * m)).symm i).1
  change (∑ i : Fin (5 * m), ∑ j : Fin (5 * m),
    (adjacency base.Adj (c i) (c j) : ℝ) * (v (c i) * v (c i) - v (c i) * v (c j))) = _
  have hinner (i : Fin (5 * m)) :
      (∑ j : Fin (5 * m), (adjacency base.Adj (c i) (c j) : ℝ) *
        (v (c i) * v (c i) - v (c i) * v (c j))) =
      (m : ℝ) * ∑ j : Fin 5, (adjacency base.Adj (c i) j : ℝ) *
        (v (c i) * v (c i) - v (c i) * v j) :=
    sum_cluster m (fun j => (adjacency base.Adj (c i) j : ℝ) *
      (v (c i) * v (c i) - v (c i) * v j))
  simp_rw [hinner]
  rw [← Finset.mul_sum, sum_cluster m (fun i : Fin 5 => ∑ j : Fin 5,
    (adjacency base.Adj i j : ℝ) * (v i * v i - v i * v j))]
  ring

private theorem blowup_spread (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * (3408 / 679 : ℝ) ≤ spread (blowup m) := by
  let c : Fin (5 * m) → Fin 5 := fun i =>
    ((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5 * m)).symm i).1
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hx0 : (∑ i : Fin (5 * m), vx (c i)) = 0 := by
    rw [sum_cluster, base_x.1, mul_zero]
  have hy0 : (∑ i : Fin (5 * m), vy (c i)) = 0 := by
    rw [sum_cluster, base_y.1, mul_zero]
  have hx2 : (∑ i : Fin (5 * m), (vx (c i)) ^ 2) = (m : ℝ) * 1358 := by
    rw [sum_cluster m (fun i => (vx i) ^ 2), base_x.2.1]
  have hy2 : (∑ i : Fin (5 * m), (vy (c i)) ^ 2) = (m : ℝ) * 2 := by
    rw [sum_cluster m (fun i => (vy i) ^ 2), base_y.2.1]
  have hx := normalized_mem (blowup m) (fun i => vx (c i)) hx0 (by rw [hx2]; positivity)
  have hy := normalized_mem (blowup m) (fun i => vy (c i)) hy0 (by rw [hy2]; positivity)
  rw [lifted_energy, base_x.2.2, hx2] at hx
  rw [lifted_energy, base_y.2.2, hy2] at hy
  have hq : (m : ℝ) ^ 2 * 6816 / ((m : ℝ) * 1358) = (m : ℝ) * (3408 / 679) := by
    field_simp [ne_of_gt hmR]
    ring
  rw [hq] at hx
  norm_num at hy
  simpa using spread_ge_values (blowup m) hx hy

/-- A single real intercept for every loopless unweighted digraph of order at least two. -/
def claim : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ), 2 ≤ n → ∀ (G : Digraph (Fin n)),
    (∀ i : Fin n, ¬ G.Adj i i) → spread G ≤ (n : ℝ) + C

theorem result : ¬ claim := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (679*C/13))
  have hm0 : 0 < m := by
    have h : (0 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact Nat.cast_pos.mp h
  have hn : 2 ≤ 5*m := by omega
  have hs := hC (5 * m) hn (blowup m) (fun i => base_loopless
    (((finProdFinEquiv : Fin 5 × Fin m ≃ Fin (5 * m)).symm i).1))
  have hl := blowup_spread m hm0
  have hnum : C < (m : ℝ)*13/679 := by
    have h := lt_of_le_of_lt (le_max_right 0 (679*C/13)) hm
    linarith
  push_cast at hs
  linarith

end D5.S3.Combinatorics.SpectralGraph.BarrettLaplacianSpreadSlopeRefutation
