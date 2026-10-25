/- GID: D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.claim; result=D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.result; claim=D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.claim
   digest: Two strongly cospectral vertices in K_{2,3} exceed the multiplicity bound. -/

import D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum

/-! The multiplicity bound fails for the complete bipartite graph with parts of size 2 and 3. -/

set_option autoImplicit false

open Matrix Finset
open D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum (idempotent)

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

private def graph : SimpleGraph (Fin 5) where
  Adj u v := (u.val < 2) ≠ (v.val < 2)
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

private instance graphDecidable : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable ((u.val < 2) ≠ (v.val < 2)))

private lemma graph_connected : graph.Connected := by
  refine graph.connected_iff_exists_forall_reachable.mpr ⟨0, fun v => ?_⟩
  by_cases hv : v.val < 2
  · exact (show graph.Adj 0 2 by decide).reachable.trans
      (show graph.Adj 2 v by change (2 < 2) ≠ (v.val < 2); simp [hv]).reachable
  · exact (show graph.Adj 0 v by change (0 < 2) ≠ (v.val < 2); simp [hv]).reachable

private lemma multiplicity_lower : 3 ≤ maxMultiplicity graph := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) :=
    { toFun := fun x => ![x 0, -x 0, x 1 + x 2, -x 1, -x 2]
      map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
      map_smul' := by intro c x; ext i; fin_cases i <;> simp [mul_add] }
  have hf : ∀ x, f x ∈ Module.End.eigenspace (graph.adjMatrix ℝ).mulVecLin 0 := by
    intro x
    rw [Module.End.mem_eigenspace_iff]
    change graph.adjMatrix ℝ *ᵥ f x = (0 : ℝ) • f x
    unfold SimpleGraph.adjMatrix
    ext i
    fin_cases i <;>
      simp [f, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, graph] <;> ring
  let f0 := f.codRestrict (Module.End.eigenspace (graph.adjMatrix ℝ).mulVecLin 0) hf
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
      (Module.End.eigenspace (graph.adjMatrix ℝ).mulVecLin 0) := by
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  unfold maxMultiplicity
  refine hd.trans (le_csSup ?_ (Set.mem_range_self 0))
  refine ⟨5, ?_⟩
  rintro b ⟨θ, rfl⟩
  simpa using (Module.End.eigenspace (graph.adjMatrix ℝ).mulVecLin θ).finrank_le

private noncomputable def polynomial : Matrix (Fin 5) (Fin 5) ℝ :=
  (1 / 3 : ℝ) • (graph.adjMatrix ℝ * graph.adjMatrix ℝ) - 1

private lemma polynomial_swap : polynomial *ᵥ Pi.single 0 1 = Pi.single 1 1 := by
  unfold polynomial SimpleGraph.adjMatrix
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ, graph,
      Pi.single_apply, Matrix.one_apply]

private lemma adjacency_cubic :
    graph.adjMatrix ℝ * graph.adjMatrix ℝ * graph.adjMatrix ℝ =
      (6 : ℝ) • graph.adjMatrix ℝ := by
  unfold SimpleGraph.adjMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, graph]

private lemma eigenvalue_support (θ : ℝ) (v : Fin 5 → ℝ) (hne : v ≠ 0)
    (hv : graph.adjMatrix ℝ *ᵥ v = θ • v) : θ = 0 ∨ θ ^ 2 = 6 := by
  have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M *ᵥ v) adjacency_cubic
  simp only [← mulVec_mulVec, smul_mulVec, mulVec_smul, hv, smul_smul] at h
  have heq := smul_left_injective ℝ hne h
  have hz : θ * (θ ^ 2 - 6) = 0 := by nlinarith [heq]
  rcases mul_eq_zero.mp hz with hzero | hsix
  · exact Or.inl hzero
  · exact Or.inr (by linarith)

private lemma polynomial_eigenvector (θ : ℝ) (v : Fin 5 → ℝ)
    (hv : graph.adjMatrix ℝ *ᵥ v = θ • v) :
    polynomial *ᵥ v = (θ ^ 2 / 3 - 1) • v := by
  unfold polynomial
  rw [sub_mulVec, smul_mulVec, ← mulVec_mulVec, hv, mulVec_smul, hv, one_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma projector_columns (θ : ℝ) :
    (idempotent graph θ).mulVec (Pi.single 1 1) =
      (θ ^ 2 / 3 - 1) • (idempotent graph θ).mulVec (Pi.single 0 1) := by
  let hA : (graph.adjMatrix ℝ).IsHermitian :=
    isHermitian_iff_isSymm.mpr graph.isSymm_adjMatrix
  have hs : polynomial.IsSymm := by
    unfold polynomial
    rw [← pow_two]
    exact (graph.isSymm_adjMatrix.pow 2 |>.smul (1 / 3 : ℝ)).sub isSymm_one
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

private lemma strong_pair : StronglyCospectral graph 0 1 := by
  classical
  intro θ
  let hA : (graph.adjMatrix ℝ).IsHermitian :=
    isHermitian_iff_isSymm.mpr graph.isSymm_adjMatrix
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
      have hc2 : (θ ^ 2 / 3 - 1) * (θ ^ 2 / 3 - 1) = 1 := by
        rcases hc with hc | hc <;> rw [hc] <;> norm_num
      rw [hc2, one_smul]
  · have hz : idempotent graph θ = 0 := by
      unfold idempotent
      apply sum_eq_zero
      intro i hi
      exact False.elim (hex ⟨i, (mem_filter.mp hi).2⟩)
    exact ⟨1, by norm_num, by rw [hz, zero_mulVec, zero_mulVec, smul_zero]⟩

private lemma pairwise_witness :
    ∀ u ∈ ({0, 1} : Finset (Fin 5)), ∀ v ∈ ({0, 1} : Finset (Fin 5)),
      StronglyCospectral graph u v := by
  intro u hu v hv θ
  simp only [mem_insert, mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact ⟨1, by norm_num, by simp⟩
  · exact strong_pair θ
  · obtain ⟨c, hc, hp⟩ := strong_pair θ
    have hc2 : c * c = 1 := by nlinarith [sq_abs c]
    refine ⟨c, hc, ?_⟩
    rw [hp, smul_smul, hc2, one_smul]
  · exact ⟨1, by norm_num, by simp⟩

private lemma bound_contradiction (m : ℕ) (hm : 3 ≤ m) (h : (2 : ℝ) ≤ 5 / m) :
    False := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < m := by linarith
  have hmul := (le_div_iff₀ hpos).mp h
  linarith

theorem result : ¬ claim := by
  intro h
  have hb := h 5 graph graph_connected {0, 1} pairwise_witness
  have hc : ({0, 1} : Finset (Fin 5)).card = 2 := by decide
  rw [hc] at hb
  exact bound_contradiction (maxMultiplicity graph) multiplicity_lower (by simpa using hb)

end D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation
