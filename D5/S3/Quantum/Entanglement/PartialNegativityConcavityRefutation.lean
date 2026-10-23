/- GID: D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.claim; result=D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.result; claim=D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.claim
   digest: The root of the product of the two largest eigenvalues is not concave on qutrits. -/

/-
proof_shape: hhat: definition (the reduced function of the partial negativity; the decreasing
  eigenvalue list is the decreasing sort of the characteristic roots, the encoding already used
  by D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.concurrence)
proof_shape: claim: definition (published conjecture, arXiv:2212.06521v6, read for every finite
  dimension d >= 2)
proof_shape: dg: definition (real diagonal 3 x 3 matrices, private)
proof_shape: sorted_roots_dg, dg_posSemidef, dg_trace, dg_mix: bind-only, each consumed on the
  proof path of result (Matrix.charpoly_diagonal, Polynomial.roots_prod, Multiset.coe_sort and
  List.mergeSort_of_pairwise; Matrix.posSemidef_diagonal_iff; Matrix.trace_diagonal; entrywise
  evaluation)
proof_shape: result: bind-only (instantiation of claim at d = 3, t = 1/2 and the diagonal
  states (1/2, 1/3, 1/6), (1/2, 1/6, 1/3), followed by Real.sqrt_lt_sqrt)
escape_witness: none (the settlement of the external named conjecture is the new content)
admission_basis: open-problem-resolution (issue #14495; Refuted)
Direct frozen dependencies (GID, statement_id): none; the module uses pinned Mathlib only.
computational_content: certified-instance (one explicit pair of qutrit states), admitted through
  the refutes basis: claim is the closed proposition, result its negation.
-/

import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.PartialNegativityConcavityRefutation

/-!
Y. Guo, *Partial-Norm of Entanglement: Entanglement Monotones That are not Monogamous*,
arXiv:2212.06521v6 (New J. Phys. 25 (2023) 083047), defines the partial negativity of a pure
state with decreasing Schmidt coefficients `λ₁ ≥ λ₂ ≥ ⋯` as `λ₁ λ₂`, with reduced function
`ĥ(ρ) = √(δ₁ δ₂)` for the two largest eigenvalues `δ₁ ≥ δ₂` of the reduced state, and
conjectures that `ĥ` is concave. It is not: `ρ = diag(1/2, 1/3, 1/6)` and
`σ = diag(1/2, 1/6, 1/3)` have `ĥ(ρ) = ĥ(σ) = √(1/6)`, while their midpoint
`diag(1/2, 1/4, 1/4)` has `ĥ = √(1/8)`.
-/

noncomputable section

open Matrix Polynomial
open scoped ComplexOrder

/-- `ĥ(A) = √(δ₁ δ₂)`, where `δ₁ ≥ δ₂ ≥ ⋯` are the real parts of the roots of the characteristic
polynomial of `A`, with multiplicity, sorted decreasingly. For a Hermitian matrix these are its
eigenvalues in decreasing order, so `δ₁` and `δ₂` are the two largest eigenvalues. -/
def hhat {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.sqrt (((A.charpoly.roots.map Complex.re).sort (· ≥ ·)).getD 0 0 *
    ((A.charpoly.roots.map Complex.re).sort (· ≥ ·)).getD 1 0)

/-- Concavity of `ĥ` on the density matrices of every dimension `d ≥ 2`. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ ρ σ : Matrix (Fin d) (Fin d) ℂ,
    ρ.PosSemidef → ρ.trace = 1 → σ.PosSemidef → σ.trace = 1 →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        t * hhat ρ + (1 - t) * hhat σ ≤ hhat (t • ρ + (1 - t) • σ)

private def dg (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun i => ((v i : ℝ) : ℂ)

private theorem sorted_roots_dg (v : Fin 3 → ℝ) (l : List ℝ) (hperm : (List.ofFn v).Perm l)
    (hsorted : l.Pairwise (· ≥ ·)) :
    ((dg v).charpoly.roots.map Complex.re).sort (· ≥ ·) = l := by
  unfold dg
  rw [Matrix.charpoly_diagonal]
  have hroots : (∏ i : Fin 3, (X - C ((v i : ℝ) : ℂ))).roots =
      Finset.univ.val.map (fun i => ((v i : ℝ) : ℂ)) := by
    rw [Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _)]
    simp [roots_X_sub_C]
  have hre : (Complex.re ∘ fun i => ((v i : ℝ) : ℂ)) = v := by
    ext i; simp
  rw [hroots, Multiset.map_map, hre, Fin.univ_val_map, Multiset.coe_eq_coe.mpr hperm,
    Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simpa [decide_eq_true_eq] using hsorted

private theorem dg_posSemidef (v : Fin 3 → ℝ) (hv : ∀ i, 0 ≤ v i) : (dg v).PosSemidef := by
  unfold dg
  refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
  exact_mod_cast hv i

private theorem dg_trace (v : Fin 3 → ℝ) (hv : v 0 + v 1 + v 2 = 1) : (dg v).trace = 1 := by
  unfold dg
  rw [Matrix.trace_diagonal, Fin.sum_univ_three]
  exact_mod_cast hv

private theorem dg_mix (u v : Fin 3 → ℝ) (t : ℝ) :
    t • dg u + (1 - t) • dg v = dg fun i => t * u i + (1 - t) * v i := by
  ext i j
  by_cases h : i = j
  · subst h; simp [dg]
  · simp [dg, h]

theorem result : ¬ claim := by
  intro h
  have key := h 3 (by norm_num) (dg ![1 / 2, 1 / 3, 1 / 6]) (dg ![1 / 2, 1 / 6, 1 / 3])
    (dg_posSemidef _ (by intro i; fin_cases i <;> norm_num))
    (dg_trace _ (by norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]))
    (dg_posSemidef _ (by intro i; fin_cases i <;> norm_num))
    (dg_trace _ (by norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]))
    (1 / 2) (by norm_num) (by norm_num)
  have h1 : hhat (dg ![1 / 2, 1 / 3, 1 / 6]) = Real.sqrt (1 / 6) := by
    rw [hhat, sorted_roots_dg _ [1 / 2, 1 / 3, 1 / 6] (by simp) (by norm_num)]
    norm_num
  have h2 : hhat (dg ![1 / 2, 1 / 6, 1 / 3]) = Real.sqrt (1 / 6) := by
    rw [hhat, sorted_roots_dg _ [1 / 2, 1 / 3, 1 / 6]
      (by simp; exact List.Perm.swap _ _ _) (by norm_num)]
    norm_num
  have h3 : hhat ((1 / 2 : ℝ) • dg ![1 / 2, 1 / 3, 1 / 6] +
      (1 - 1 / 2 : ℝ) • dg ![1 / 2, 1 / 6, 1 / 3]) = Real.sqrt (1 / 8) := by
    rw [dg_mix, hhat, sorted_roots_dg _ [1 / 2, 1 / 4, 1 / 4]
      (by simp [List.ofFn_succ]; norm_num) (by norm_num)]
    norm_num
  rw [h1, h2, h3] at key
  have h4 : Real.sqrt (1 / 8) < Real.sqrt (1 / 6) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end

end D5.S3.Quantum.Entanglement.PartialNegativityConcavityRefutation
