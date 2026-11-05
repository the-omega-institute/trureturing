/- GID: D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.claim; result=D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.result; claim=D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.claim
   digest: Two strongly cospectral vertices in K_{2,3} exceed the multiplicity bound. -/

import D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation

/-! The multiplicity bound fails for the complete bipartite graph with parts of size 2 and 3. -/

set_option autoImplicit false

open Matrix Finset
open D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum (idempotent)
open D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
  (K23 K23_connected)

namespace D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation

/-- Strong cospectrality for the real symmetric adjacency matrix. -/
def StronglyCospectral {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : Prop :=
  ∀ θ : ℝ, ∃ c : ℝ, |c| = 1 ∧
    (idempotent G θ).mulVec (Pi.single u 1) =
      c • (idempotent G θ).mulVec (Pi.single v 1)

/-- The largest adjacency-eigenvalue multiplicity, as the supremum of eigenspace dimensions.
The dimensions are bounded by the number of vertices; non-eigenvalues contribute zero. -/
noncomputable def maxMultiplicity {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  sSup (Set.range fun θ : ℝ =>
    Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin θ))

/-- The proposed extension of the normal-Cayley-graph bound to connected simple graphs. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Connected →
    ∀ S : Finset (Fin n), (∀ u ∈ S, ∀ v ∈ S, StronglyCospectral G u v) →
      (S.card : ℝ) ≤ (n : ℝ) / (maxMultiplicity G : ℝ)

private lemma multiplicity_lower : 3 ≤ maxMultiplicity K23 := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) :=
    { toFun := fun x => ![x 0, -x 0, x 1 + x 2, -x 1, -x 2]
      map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
      map_smul' := by intro c x; ext i; fin_cases i <;> simp [mul_add] }
  have hf : ∀ x, f x ∈ Module.End.eigenspace (K23.adjMatrix ℝ).mulVecLin 0 := by
    intro x
    rw [Module.End.mem_eigenspace_iff]
    change K23.adjMatrix ℝ *ᵥ f x = (0 : ℝ) • f x
    unfold SimpleGraph.adjMatrix K23 SimpleGraph.comap completeBipartiteGraph
    ext i
    fin_cases i <;>
      simp [f, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, finSumFinEquiv, Fin.addCases] <;> ring
  let f0 := f.codRestrict (Module.End.eigenspace (K23.adjMatrix ℝ).mulVecLin 0) hf
  have hinj : Function.Injective f0 := by
    intro x y h
    have h' := congrArg Subtype.val h
    have h0 := congrFun h' 1
    have h1 := congrFun h' 3
    have h2 := congrFun h' 4
    change -x 0 = -y 0 at h0
    change -x 1 = -y 1 at h1
    change -x 2 = -y 2 at h2
    funext i
    fin_cases i
    · exact neg_injective h0
    · exact neg_injective h1
    · exact neg_injective h2
  have hd : 3 ≤ Module.finrank ℝ
      (Module.End.eigenspace (K23.adjMatrix ℝ).mulVecLin 0) := by
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  unfold maxMultiplicity
  refine hd.trans (le_csSup ?_ (Set.mem_range_self 0))
  refine ⟨5, ?_⟩
  rintro b ⟨θ, rfl⟩
  simpa using (Module.End.eigenspace (K23.adjMatrix ℝ).mulVecLin θ).finrank_le

private noncomputable def polynomial : Matrix (Fin 5) (Fin 5) ℝ :=
  (1 / 3 : ℝ) • (K23.adjMatrix ℝ * K23.adjMatrix ℝ) - 1

private lemma polynomial_swap : polynomial *ᵥ Pi.single 0 1 = Pi.single 1 1 := by
  unfold polynomial SimpleGraph.adjMatrix K23 SimpleGraph.comap completeBipartiteGraph
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ,
      Pi.single_apply, Matrix.one_apply, finSumFinEquiv, Fin.addCases]

private lemma adjacency_cubic :
    K23.adjMatrix ℝ * K23.adjMatrix ℝ * K23.adjMatrix ℝ =
      (6 : ℝ) • K23.adjMatrix ℝ := by
  unfold SimpleGraph.adjMatrix K23 SimpleGraph.comap completeBipartiteGraph
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, finSumFinEquiv, Fin.addCases]

private lemma eigenvalue_support (θ : ℝ) (v : Fin 5 → ℝ) (hne : v ≠ 0)
    (hv : K23.adjMatrix ℝ *ᵥ v = θ • v) : θ = 0 ∨ θ ^ 2 = 6 := by
  have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M *ᵥ v) adjacency_cubic
  simp only [← mulVec_mulVec, smul_mulVec, mulVec_smul, hv, smul_smul] at h
  have heq := smul_left_injective ℝ hne h
  have hz : θ * (θ ^ 2 - 6) = 0 := by nlinarith [heq]
  rcases mul_eq_zero.mp hz with hzero | hsix
  · exact Or.inl hzero
  · exact Or.inr (by linarith)

private lemma polynomial_eigenvector (θ : ℝ) (v : Fin 5 → ℝ)
    (hv : K23.adjMatrix ℝ *ᵥ v = θ • v) :
    polynomial *ᵥ v = (θ ^ 2 / 3 - 1) • v := by
  unfold polynomial
  have h := Module.End.aeval_apply_of_mem_apply_eq_smul
    (p := Polynomial.C (1 / 3 : ℝ) * Polynomial.X ^ 2 - 1)
    (f := (K23.adjMatrix ℝ).mulVecLin) hv
  simp only [map_sub, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    map_one, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at h
  change (1 / 3 : ℝ) • (K23.adjMatrix ℝ *ᵥ (K23.adjMatrix ℝ *ᵥ v)) - v =
    ((1 / 3 : ℝ) * θ ^ 2 - 1) • v at h
  simpa only [sub_mulVec, smul_mulVec, ← mulVec_mulVec, one_mulVec,
    div_eq_mul_inv, one_div, mul_comm, one_mul] using h

private lemma projector_columns (θ : ℝ) :
    (idempotent K23 θ).mulVec (Pi.single 1 1) =
      (θ ^ 2 / 3 - 1) • (idempotent K23 θ).mulVec (Pi.single 0 1) := by
  let hA : (K23.adjMatrix ℝ).IsHermitian :=
    isHermitian_iff_isSymm.mpr K23.isSymm_adjMatrix
  have hs : polynomial.IsSymm := by
    unfold polynomial
    rw [← pow_two]
    exact (K23.isSymm_adjMatrix.pow 2 |>.smul (1 / 3 : ℝ)).sub isSymm_one
  have hcoeff (i : Fin 5) (hi : hA.eigenvalues i = θ) :
      hA.eigenvectorBasis i 1 = (θ ^ 2 / 3 - 1) * hA.eigenvectorBasis i 0 := by
    have hev := polynomial_eigenvector θ ⇑(hA.eigenvectorBasis i)
      (by rw [← hi]; exact hA.mulVec_eigenvectorBasis i)
    have hd := hs.dotProduct_mulVec_comm
      (x := ⇑(hA.eigenvectorBasis i)) (y := Pi.single 0 1)
    rw [polynomial_swap, hev] at hd
    simpa only [dotProduct_single_one, dotProduct_smul, single_dotProduct, one_mul,
      smul_eq_mul] using hd
  unfold idempotent
  change (∑ i with hA.eigenvalues i = θ,
      vecMulVec ⇑(hA.eigenvectorBasis i) ⇑(hA.eigenvectorBasis i)) *ᵥ Pi.single 1 1 = _
  rw [sum_mulVec, sum_mulVec, smul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [mulVec_single_one, mulVec_single_one]
  ext a
  change hA.eigenvectorBasis i a * hA.eigenvectorBasis i 1 =
    (θ ^ 2 / 3 - 1) * (hA.eigenvectorBasis i a * hA.eigenvectorBasis i 0)
  rw [hcoeff i (mem_filter.mp hi).2]
  ring

private lemma strong_pair : StronglyCospectral K23 0 1 := by
  classical
  intro θ
  let hA : (K23.adjMatrix ℝ).IsHermitian :=
    isHermitian_iff_isSymm.mpr K23.isSymm_adjMatrix
  by_cases hex : ∃ i, hA.eigenvalues i = θ
  · obtain ⟨i, hi⟩ := hex
    have hs := eigenvalue_support θ ⇑(hA.eigenvectorBasis i)
      ((WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i))
      (by rw [← hi]; exact hA.mulVec_eigenvectorBasis i)
    have hc : θ ^ 2 / 3 - 1 = -1 ∨ θ ^ 2 / 3 - 1 = 1 := by
      rcases hs with hzero | hsix
      · left; rw [hzero]; norm_num
      · right; rw [hsix]; norm_num
    refine ⟨θ ^ 2 / 3 - 1, ?_, ?_⟩
    · rcases hc with hc | hc <;> rw [hc] <;> norm_num
    · rw [projector_columns, smul_smul]
      have hc2 : (θ ^ 2 / 3 - 1) * (θ ^ 2 / 3 - 1) = 1 :=
        mul_self_eq_one_iff.mpr hc.symm
      rw [hc2, one_smul]
  · have hz : idempotent K23 θ = 0 := by
      unfold idempotent
      apply sum_eq_zero
      intro i hi
      exact False.elim (hex ⟨i, (mem_filter.mp hi).2⟩)
    exact ⟨1, by norm_num, by rw [hz, zero_mulVec, zero_mulVec, smul_zero]⟩

private lemma pairwise_witness :
    ∀ u ∈ ({0, 1} : Finset (Fin 5)), ∀ v ∈ ({0, 1} : Finset (Fin 5)),
      StronglyCospectral K23 u v := by
  intro u hu v hv θ
  simp only [mem_insert, mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact ⟨1, by norm_num, by rw [one_smul]⟩
  · exact strong_pair θ
  · obtain ⟨c, hc, hp⟩ := strong_pair θ
    have hc2 : c * c = 1 := by
      simpa only [abs_one, mul_one] using
        (abs_eq_iff_mul_self_eq.mp (hc.trans abs_one.symm))
    refine ⟨c, hc, ?_⟩
    rw [hp, smul_smul, hc2, one_smul]
  · exact ⟨1, by norm_num, by rw [one_smul]⟩

private lemma bound_contradiction (m : ℕ) (hm : 3 ≤ m) (h : (2 : ℝ) ≤ 5 / m) :
    False := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < m := by linarith
  have hmul := (le_div_iff₀ hpos).mp h
  linarith

theorem result : ¬ claim := by
  intro h
  have hb := h 5 K23 K23_connected {0, 1} pairwise_witness
  have hc : ({0, 1} : Finset (Fin 5)).card = 2 := by decide
  rw [hc] at hb
  change (2 : ℝ) ≤ 5 / (maxMultiplicity K23 : ℝ) at hb
  exact bound_contradiction (maxMultiplicity K23) multiplicity_lower hb

end D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation
