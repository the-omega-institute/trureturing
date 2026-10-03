import D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
open _root_.D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := SimpleGraph (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := SimpleGraph (Fin n)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ G => G) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

/-- The complete claim; only the graph in `G.Connected` is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (O.readout () n G).Connected →
      (avgMixing G).trace ≤ (avgMixing (⊤ : SimpleGraph (Fin n))).trace

theorem trace_bot : (avgMixing (⊥ : SimpleGraph (Fin 2))).trace = 2 := by
  have hA : ((⊥ : SimpleGraph (Fin 2)).adjMatrix ℝ).IsHermitian :=
    isHermitian_iff_isSymm.mpr (⊥ : SimpleGraph (Fin 2)).isSymm_adjMatrix
  have h0 : hA.eigenvalues = 0 := hA.eigenvalues_eq_zero_iff.mpr SimpleGraph.adjMatrix_bot
  have himg : univ.image hA.eigenvalues = {0} := by
    rw [h0]
    exact image_const univ_nonempty 0
  have hrow : ∀ a, ∑ i with hA.eigenvalues i = 0,
      hA.eigenvectorBasis i a * hA.eigenvectorBasis i a = 1 := by
    intro a
    rw [filter_true_of_mem fun i _ => by rw [h0]; rfl]
    have h := congrFun (congrFun (mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2) a) a
    simpa [mul_apply, star_apply, one_apply] using h
  have htr : (avgMixing (⊥ : SimpleGraph (Fin 2))).trace = ∑ a, ∑ θ ∈ univ.image hA.eigenvalues,
      (∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 := by
    simp only [avgMixing, idempotent, trace, diag_apply, Matrix.sum_apply, hadamard_apply,
      vecMulVec_apply, sq]
  rw [htr, himg]
  simp only [sum_singleton, hrow]
  norm_num

theorem trace_top : (avgMixing (⊤ : SimpleGraph (Fin 2))).trace = 1 := by
  have hA : ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℝ).IsHermitian :=
    isHermitian_iff_isSymm.mpr (⊤ : SimpleGraph (Fin 2)).isSymm_adjMatrix
  -- every eigenbasis vector of `A(K_2)` has both squared coordinates `1/2` and eigenvalue `±1`
  have hvec : ∀ i, (hA.eigenvectorBasis i 0 ^ 2 = 1 / 2 ∧ hA.eigenvectorBasis i 1 ^ 2 = 1 / 2) ∧
      hA.eigenvalues i ^ 2 = 1 := by
    intro i
    have heq := hA.mulVec_eigenvectorBasis i
    have e0 : hA.eigenvectorBasis i 1 = hA.eigenvalues i * hA.eigenvectorBasis i 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, SimpleGraph.adjMatrix_apply]
        using congrFun heq 0
    have e1 : hA.eigenvectorBasis i 0 = hA.eigenvalues i * hA.eigenvectorBasis i 1 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, SimpleGraph.adjMatrix_apply]
        using congrFun heq 1
    have hn : ∑ c, hA.eigenvectorBasis i c * hA.eigenvectorBasis i c = 1 := by
      have h := congrFun (congrFun (mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2) i) i
      simpa [mul_apply, star_apply, one_apply] using h
    rw [Fin.sum_univ_two] at hn
    generalize hA.eigenvectorBasis i 0 = x at e0 e1 hn ⊢
    generalize hA.eigenvectorBasis i 1 = y at e0 e1 hn ⊢
    generalize hA.eigenvalues i = l at e0 e1 ⊢
    have hx : x ≠ 0 := by
      rintro rfl
      rw [mul_zero] at e0
      rw [e0] at hn
      norm_num at hn
    have hl : l ^ 2 = 1 := by
      have : x * (1 - l ^ 2) = 0 := by
        rw [e0] at e1
        linear_combination e1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hx
      · linarith
    rw [e0] at hn
    refine ⟨⟨?_, ?_⟩, hl⟩
    · linear_combination (1 / 2) * hn - (1 / 2) * x ^ 2 * hl
    · rw [e0]
      linear_combination (1 / 2) * hn + (1 / 2) * x ^ 2 * hl
  have hsum : hA.eigenvalues 0 + hA.eigenvalues 1 = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    rw [SimpleGraph.trace_adjMatrix, Fin.sum_univ_two] at h
    simpa using h.symm
  have hne : hA.eigenvalues 0 ≠ hA.eigenvalues 1 := by
    intro h
    have h0 : hA.eigenvalues 0 = 0 := by linarith [hsum]
    have := (hvec 0).2
    rw [h0] at this
    norm_num at this
  -- the two eigenvalues differ, so every eigenvalue has a one-element fibre
  have hinj : ∀ i j : Fin 2, hA.eigenvalues i = hA.eigenvalues j → i = j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hne
    · exact absurd hij.symm hne
    · rfl
  have hfib : ∀ a i : Fin 2, ∑ j with hA.eigenvalues j = hA.eigenvalues i,
      hA.eigenvectorBasis j a * hA.eigenvectorBasis j a = 1 / 2 := by
    intro a i
    have hS : (univ.filter fun j => hA.eigenvalues j = hA.eigenvalues i) = {i} := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨hinj j i, fun h => h ▸ rfl⟩
    rw [hS, sum_singleton, ← sq]
    fin_cases a
    · exact (hvec i).1.1
    · exact (hvec i).1.2
  have hdiag : ∀ a : Fin 2, ∑ θ ∈ univ.image hA.eigenvalues,
      (∑ j with hA.eigenvalues j = θ, hA.eigenvectorBasis j a * hA.eigenvectorBasis j a) ^ 2 =
        1 / 2 := by
    intro a
    rw [sum_image (by intro i _ j _ h; exact hinj i j h),
      sum_congr rfl fun i _ => by rw [hfib a i], Fin.sum_univ_two]
    norm_num
  have htr : (avgMixing (⊤ : SimpleGraph (Fin 2))).trace = ∑ a, ∑ θ ∈ univ.image hA.eigenvalues,
      (∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 := by
    simp only [avgMixing, idempotent, trace, diag_apply, Matrix.sum_apply, hadamard_apply,
      vecMulVec_apply, sq]
  rw [htr, sum_congr rfl fun a _ => hdiag a, Fin.sum_univ_two]
  norm_num

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hle := @h 2 ⊥ inferInstance
    (by change (⊤ : SimpleGraph (Fin 2)).Connected; exact SimpleGraph.connected_top)
  rw [trace_bot, trace_top] at hle
  norm_num at hle

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, ⊥, ⊤, fun h => ?_⟩
  change (⊥ : SimpleGraph (Fin 2)) = ⊤ at h
  have h01 := congrArg (fun G : SimpleGraph (Fin 2) => G.Adj 0 1) h
  simp at h01

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum.result in arena
  readout via (realize signature (fun _ _ G => G) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
    «definition» := some {
      owner := `D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
      name := `D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum.claim }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
