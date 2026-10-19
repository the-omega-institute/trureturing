/- GID: D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.claim; result=D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.result; claim=D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.claim
   digest: Gluing two stochastic matrices yields an eigenvalue outside their spectral hull. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#19143; Refuted).
Direct frozen dependencies: none (all declarations).
RootedChain, glue, claim: proof_shape: bind-only (source definitions); consumer: result.
B, chain, weights, v: proof_shape: bind-only (concrete data); consumer: result.
All definitions and data have escape_witness: none.
B_stochastic: proof_shape: bind-only; consumer: chain, then result; escape_witness: none.
glued_eigenvalue: proof_shape: bind-only; consumer: result; escape_witness: none.
input_halfplane: proof_shape: bind-only; consumer: result; escape_witness: none.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The source's state and spectrum expressions are expanded directly, without type or
spectrum aliases. The root is state 0 and transitions run from column to row.
The unfrozen MCMCSupplier Dominance owner is not imported; its spectrum bridge is
supplied directly by pinned Mathlib eigenspace and spectrum declarations.
-/

import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Complex.Convex

/-! Definitions for X. B. Han, S. Wang and C. Yu, "PageRank of Gluing Networks and Corresponding Markov
Chains", Mathematics 13(13) (2025) 2080, Definition 8 (θ-gluing) and Conjecture 1 (spectrum of a gluing). -/

namespace D5.S3.Quantum.Matrix.HanWangYuGluingSpectrumRefutation

open _root_.Matrix

/-- A Markov chain `M_i = (S_i, A_i)` with the fixed point `v_0^i`: states `Fin (n + 1)` with `v_0^i = 0`, and
`A v w` the transition probability from `w` to `v` (column stochastic, as in the source). -/
structure RootedChain where
  n : ℕ
  A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
  stochastic : A ∈ Matrix.colStochastic ℝ (Fin (n + 1))

/-- Definition 8, the `θ`-gluing: `a_vw = a^i_vw` for `v ∈ S_i`, `w ∈ S_i ∖ {v_0}`; `a_vw = θ_i a^i_vw` for
`v ∈ S_i ∖ {v_0}`, `w = v_0`; `a_{v_0 v_0} = Σ_i θ_i a^i_{v_0 v_0}`; and `0` otherwise. -/
def glue {k : ℕ} (M : Fin k → RootedChain) (θ : Fin k → ℝ) :
    Matrix (Option (Σ i, Fin (M i).n)) (Option (Σ i, Fin (M i).n)) ℝ :=
  fun x y => match x, y with
    | none, none => ∑ i, θ i * (M i).A 0 0
    | some ⟨i, v⟩, none => θ i * (M i).A v.succ 0
    | none, some ⟨j, w⟩ => (M j).A 0 w.succ
    | some ⟨i, v⟩, some ⟨j, w⟩ => if h : i = j then (M j).A (h ▸ v).succ w.succ else 0

/-- Conjecture 1: "Glue Markov chains `M_i = (S_i, A_i)` to a Markov chain `M = (S, A)`, then all the eigenvalues
of `A` lie in the convex hull of the eigenvalues of all `A_i` on the complex plane." -/
def claim : Prop :=
  ∀ (k : ℕ) (M : Fin k → RootedChain) (θ : Fin k → ℝ),
    (∀ i, 0 < θ i ∧ θ i < 1) → ∑ i, θ i = 1 →
      spectrum ℂ ((glue M θ).map (algebraMap ℝ ℂ)) ⊆
        convexHull ℝ (⋃ i, spectrum ℂ ((M i).A.map (algebraMap ℝ ℂ)))


noncomputable section

private def B : Matrix (Fin 3) (Fin 3) ℝ :=
  !![43 / 54, 9 / 54, 2 / 54;
      2 / 54, 36 / 54, 16 / 54;
      9 / 54, 9 / 54, 36 / 54]

private theorem B_stochastic : B ∈ Matrix.colStochastic ℝ (Fin 3) := by
  rw [Matrix.mem_colStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [B]
  · intro j
    fin_cases j <;> norm_num [B, Fin.sum_univ_three]

private abbrev chain : RootedChain := ⟨2, B, B_stochastic⟩
private def weights : Fin 2 → ℝ := fun _ => 1 / 2

private def v : Option (Σ _ : Fin 2, Fin chain.n) → ℂ
  | none => 0
  | some ⟨i, j⟩ => if i = 0 then ![-4, 3] j else ![4, -3] j

private theorem glued_eigenvalue : (4 / 9 : ℂ) ∈ spectrum ℂ
    ((glue (fun _ : Fin 2 => chain) weights).map (algebraMap ℝ ℂ)) := by
  let C := (glue (fun _ : Fin 2 => chain) weights).map (algebraMap ℝ ℂ)
  have hv : v ≠ 0 := by
    intro h
    have hh : (-4 : ℂ) = 0 := congrFun h (some ⟨0, 0⟩)
    norm_num [v] at hh
  have he : C *ᵥ v = (4 / 9 : ℂ) • v := by
    ext x
    rcases x with _ | ⟨i, j⟩
    · norm_num [C, Matrix.mulVec, dotProduct, Fintype.sum_option,
        Fintype.sum_sigma, chain, Fin.sum_univ_two, glue, weights, v, B]
      norm_num [chain, B, Fin.sum_univ_succ]
    · fin_cases i <;> fin_cases j <;>
        norm_num [C, Matrix.mulVec, dotProduct, Fintype.sum_option,
          Fintype.sum_sigma, chain, Fin.sum_univ_two, glue, weights, v, B] <;>
          norm_num [chain, B, Fin.sum_univ_succ]
  have hEig : Module.End.HasEigenvector C.toLin' (4 / 9 : ℂ) v := by
    exact ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩
  simpa only [Matrix.spectrum_toLin'] using
    (Module.End.hasEigenvalue_of_hasEigenvector hEig).mem_spectrum

private theorem input_halfplane {μ : ℂ} (hμ : μ ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ))) : 1 / 2 ≤ μ.re := by
  have hd : (μ • (1 : Matrix (Fin 3) (Fin 3) ℂ) - B.map (algebraMap ℝ ℂ)).det = 0 := by
    simpa only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
      Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] using hμ
  have hf : (μ • (1 : Matrix (Fin 3) (Fin 3) ℂ) - B.map (algebraMap ℝ ℂ)).det =
      (μ - 1) * (μ - 17 / 27) * (μ - 1 / 2) := by
    simp [Matrix.det_fin_three, B, Matrix.sub_apply, Matrix.smul_apply]
    ring
  rw [hf] at hd
  rcases mul_eq_zero.mp hd with h | h
  · rcases mul_eq_zero.mp h with h | h
    · have : μ = 1 := sub_eq_zero.mp h
      rw [this]
      norm_num
    · have : μ = 17 / 27 := sub_eq_zero.mp h
      rw [this]
      norm_num
  · have : μ = 1 / 2 := sub_eq_zero.mp h
    rw [this]
    norm_num

theorem result : ¬ claim := by
  intro hc
  have hθ : ∀ i, 0 < weights i ∧ weights i < 1 := by
    intro i
    norm_num [weights]
  have hs : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_two]
  have hin := hc 2 (fun _ : Fin 2 => chain) weights hθ hs glued_eigenvalue
  have hh : convexHull ℝ (⋃ _ : Fin 2, spectrum ℂ (chain.A.map (algebraMap ℝ ℂ))) ⊆ {z : ℂ | 1 / 2 ≤ z.re} := by
    apply convexHull_min _ (convex_halfSpace_re_ge (1 / 2))
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    exact input_halfplane hi
  have := hh hin
  norm_num at this

end
end D5.S3.Quantum.Matrix.HanWangYuGluingSpectrumRefutation
