/- GID: D5/S3/Quantum/Information/MultiEntropy/TripartiteReplicaCoarseGraining
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/MultiEntropy/TripartiteReplicaCoarseGraining
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound every tripartite replica moment by the moments of all bipartite mergers. -/

import D5.S3.Quantum.Information.MultiEntropy.ReplicaTorusTransfer
import D5.S3.Quantum.Information.MultiEntropy.GramTracePowerBound

/-! Coarse graining of the finite tripartite replica contraction of Gadde,
Jain, Krishna, Kulkarni and Sharma (arXiv:2308.16247, Eq. (1.13)). -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Information.MultiEntropy.TripartiteReplicaCoarseGraining

open MultiEntropyPositivityRefutation (E)
open MultiEntropyPositivityRefutation.CQReplica (stateEquiv densityAB densityA densityB
  blocks mergeAB mergeBC mergeAC)
open MultiEntropyPositivityRefutation.ReplicaTorusTransfer
open MultiEntropyPositivityRefutation.CQReplica.GramTracePowerBound

open private densityAB_apply blocks_densityAB_posSemidef E_two_re_nonneg renyi_le_of_moment_le
  from D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining

variable {L : Fin 3 → Type*} [localFintype : ∀ i, Fintype (L i)]

private theorem densityB_posSemidef (ψ : ((i : Fin 3) → L i) → ℂ) :
    (densityB ψ).PosSemidef :=
  Matrix.posSemidef_sum _ (fun a _ => blocks_densityAB_posSemidef ψ a)

private theorem abs_moment_le_densityB [DecidableEq (L 1)] (n : ℕ) [NeZero n] (hn : 0 < n)
    (ψ : ((i : Fin 3) → L i) → ℂ) :
    ‖E n 3 ψ‖ ≤ ((densityB ψ ^ n).trace.re) ^ n := by
  classical
  have hP : (P (L := L) n)ᴴ * P n = 1 := by
    unfold P
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp
  rw [E_eq_trace_R_pow, R_eq_V_conjTranspose_mul_P_mul_V]
  exact norm_trace_compression_pow_le_tensor hn (V n ψ) (P n) hP
    (densityB ψ) (densityB_posSemidef ψ) (V_conjTranspose_mul_V_eq_tensorOp_densityB n ψ)

private theorem densityB_apply (ψ : ((i : Fin 3) → L i) → ℂ) (b d : L 1) :
    densityB ψ b d = ∑ a : L 0, ∑ c : L 2,
      ψ (stateEquiv.symm ((a, b), c)) * star (ψ (stateEquiv.symm ((a, d), c))) := by
  simp only [densityB, Matrix.sum_apply, blocks, densityAB_apply]

omit localFintype in
private theorem relabel_AB_apply (ψ : ((i : Fin 3) → L i) → ℂ)
    (a : L 0) (b : L 1) (c : L 2) :
    relabel (Equiv.swap 0 1) ψ (stateEquiv.symm ((b, a), c)) =
      ψ (stateEquiv.symm ((a, b), c)) := by
  unfold relabel
  apply congrArg ψ
  apply (Equiv.piCongrLeft L (Equiv.swap 0 1)).symm.injective
  rw [Equiv.symm_apply_apply]
  funext i
  rw [Equiv.piCongrLeft_symm_apply]
  fin_cases i <;> rfl

private theorem densityB_swapAB (ψ : ((i : Fin 3) → L i) → ℂ) :
    @densityB (fun i => L (Equiv.swap 0 1 i)) (localFintype _) (localFintype _)
      (relabel (Equiv.swap 0 1) ψ) = densityA ψ := by
  ext a d
  rw [densityB_apply]
  unfold densityA
  simp only [densityAB_apply]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg₂ (· * ·) (relabel_AB_apply ψ a b c)
    (congrArg star (relabel_AB_apply ψ d b c))

private def amplitudeMatrix (ψ : ((i : Fin 3) → L i) → ℂ) :
    Matrix (L 0 × L 1) (L 2) ℂ :=
  fun ab c => ψ (stateEquiv.symm (ab, c))

private theorem densityAB_eq_gram (ψ : ((i : Fin 3) → L i) → ℂ) :
    densityAB ψ = amplitudeMatrix ψ * (amplitudeMatrix ψ)ᴴ := by
  ext ab ab'
  simp [densityAB_apply, amplitudeMatrix, Matrix.mul_apply]

omit localFintype in
private theorem relabel_BC_apply (ψ : ((i : Fin 3) → L i) → ℂ)
    (a : L 0) (b : L 1) (c : L 2) :
    relabel (Equiv.swap 1 2) ψ (stateEquiv.symm ((a, c), b)) =
      ψ (stateEquiv.symm ((a, b), c)) := by
  unfold relabel
  apply congrArg ψ
  apply (Equiv.piCongrLeft L (Equiv.swap 1 2)).symm.injective
  rw [Equiv.symm_apply_apply]
  funext i
  rw [Equiv.piCongrLeft_symm_apply]
  fin_cases i <;> rfl

private theorem densityB_swapBC (ψ : ((i : Fin 3) → L i) → ℂ) :
    @densityB (fun i => L (Equiv.swap 1 2 i)) (localFintype _) (localFintype _)
      (relabel (Equiv.swap 1 2) ψ) =
      ((amplitudeMatrix ψ)ᴴ * amplitudeMatrix ψ).transpose := by
  ext c d
  change L 2 at c d
  calc
    densityB (relabel (Equiv.swap 1 2) ψ) c d =
        ∑ a : L 0, ∑ b : L 1, amplitudeMatrix ψ (a, b) c *
          star (amplitudeMatrix ψ (a, b) d) := by
      refine (densityB_apply (relabel (Equiv.swap 1 2) ψ) c d).trans ?_
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact congrArg₂ (· * ·) (relabel_BC_apply ψ a b c)
        (congrArg star (relabel_BC_apply ψ a b d))
    _ = ((amplitudeMatrix ψ)ᴴ * amplitudeMatrix ψ).transpose c d := by
      rw [Matrix.transpose_apply, Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [Matrix.conjTranspose_apply, mul_comm]

/-- For every finite tripartite pure-state amplitude and each pair merger,
the absolute value of the original replica moment is at most the grouped
bipartite moment raised to the replica order. -/
theorem E_abs_coarseGraining_all_mergers (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (ψ : ((i : Fin 3) → L i) → ℂ) :
    ‖E n 3 ψ‖ ≤ (E n 2 (mergeAB ψ)).re ^ n ∧
      ‖E n 3 ψ‖ ≤ (E n 2 (mergeBC ψ)).re ^ n ∧
      ‖E n 3 ψ‖ ≤ (E n 2 (mergeAC ψ)).re ^ n := by
  classical
  have hn' : 0 < n := by omega
  have hAB := @abs_moment_le_densityB (fun i => L (Equiv.swap 1 2 i))
    (fun i => localFintype _) (inferInstance) n _ hn' (relabel (Equiv.swap 1 2) ψ)
  rw [E_swap_BC, densityB_swapBC] at hAB
  have htraceAB : Matrix.trace
      (((amplitudeMatrix ψ)ᴴ * amplitudeMatrix ψ).transpose ^ n) =
      Matrix.trace (densityAB ψ ^ n) := by
    rw [← Matrix.transpose_pow, Matrix.trace_transpose,
      ← trace_rectangular_mul_pow (amplitudeMatrix ψ) (amplitudeMatrix ψ)ᴴ hn',
      ← densityAB_eq_gram]
  have hBC := @abs_moment_le_densityB (fun i => L (Equiv.swap 0 1 i))
    (fun i => localFintype _) (inferInstance) n _ hn' (relabel (Equiv.swap 0 1) ψ)
  rw [E_swap_AB, densityB_swapAB] at hBC
  have hAC := abs_moment_le_densityB n hn' ψ
  obtain ⟨hab, hbc, hac⟩ := E_merge_trace_moments n ψ
  rw [hab, hbc, hac]
  exact ⟨hAB.trans_eq (congrArg (fun x : ℂ => x.re ^ n) htraceAB), hBC, hAC⟩

/-- On the positive-moment domain, each bipartite Rényi entropy is bounded
above by the original tripartite Rényi multi-entropy. -/
theorem renyi_coarseGraining_all_mergers_of_positive (n : ℕ) [NeZero n]
    (hn : 2 ≤ n) (ψ : ((i : Fin 3) → L i) → ℂ)
    (hpos : 0 < (E n 3 ψ).re) :
    ∀ y ∈ [(E n 2 (mergeAB ψ)).re, (E n 2 (mergeBC ψ)).re, (E n 2 (mergeAC ψ)).re],
      0 < y ∧ -Real.log y / ((n : ℝ) - 1) ≤
        -Real.log (E n 3 ψ).re / ((n : ℝ) * ((n : ℝ) - 1)) := by
  obtain ⟨hab, hbc, hac⟩ := E_abs_coarseGraining_all_mergers n hn ψ
  have hreal := Complex.re_le_norm (E n 3 ψ)
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · exact renyi_le_of_moment_le n hn hpos (E_two_re_nonneg n (mergeAB ψ)) (hreal.trans hab)
  · exact renyi_le_of_moment_le n hn hpos (E_two_re_nonneg n (mergeBC ψ)) (hreal.trans hbc)
  · exact renyi_le_of_moment_le n hn hpos (E_two_re_nonneg n (mergeAC ψ)) (hreal.trans hac)

#print axioms E_abs_coarseGraining_all_mergers
#print axioms renyi_coarseGraining_all_mergers_of_positive

end D5.S3.Quantum.Information.MultiEntropy.TripartiteReplicaCoarseGraining
