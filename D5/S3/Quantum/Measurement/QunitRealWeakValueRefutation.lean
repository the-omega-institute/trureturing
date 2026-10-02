/- GID: D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/QunitRealWeakValueRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.claim; result=D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.result; claim=D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.claim
   digest: Real qutrit bases give all-real weak values outside the real span of 1512.02113. -/

/-
proof_shape: result: bind-only (evaluation of the definitions at one explicit pair of real
  orthonormal bases of C^3 and one traceless Hermitian matrix: orthonormality, overlaps and the
  nine weak values by norm_num, non-membership in the real span by three matrix entries and
  linarith)
escape_witness: null
admission_basis: open-problem-resolution (issue #12048; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.QunitRealWeakValueRefutation

open Matrix

/-- The weak value `W_{φ,ψ}(M) = ⟨ψ|M|φ⟩ / ⟨ψ|φ⟩` of the observable `M` for the pre-selected
state `φ` and the post-selected state `ψ`. -/
noncomputable def weakValue {n : ℕ} (φ ψ : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (star ψ ⬝ᵥ (M *ᵥ φ)) / (star ψ ⬝ᵥ φ)

/-- `b 0, …, b (n - 1)` is an orthonormal basis of `ℂⁿ`: `⟨b i|b j⟩ = δ_ij`. -/
def IsONB {n : ℕ} (b : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j, star (b i) ⬝ᵥ b j = if i = j then 1 else 0

/-- The traceless part `|v⟩⟨v| - I/n` of the projector onto `v`. -/
noncomputable def tracelessProj {n : ℕ} (v : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  vecMulVec v (star v) - (n : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ)

/-- `ℛ_{φ,ψ}`: the real span of the traceless projectors `|φ_i⟩⟨φ_i| - I/n` and
`|ψ_j⟩⟨ψ_j| - I/n` of the two bases. -/
noncomputable def realSpan {n : ℕ} (φ ψ : Fin n → Fin n → ℂ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  Submodule.span ℝ
    (Set.range (Sum.elim (fun i => tracelessProj (φ i)) (fun j => tracelessProj (ψ j))))

/-- The conjecture of Farinholt, Ghazarians and Troupe (arXiv:1512.02113, Conjecture in
Section 7): for orthonormal bases `φ`, `ψ` of `ℂⁿ` whose pairs `(φ_i, ψ_j)` are distinct and
nonorthogonal, a traceless Hermitian `M` has all weak values `W_{φ_i,ψ_j}(M)` real if and only
if `M ∈ ℛ_{φ,ψ}`. -/
def claim : Prop :=
  ∀ (n : ℕ) (φ ψ : Fin n → Fin n → ℂ), 2 ≤ n → IsONB φ → IsONB ψ →
    (∀ i j, star (ψ j) ⬝ᵥ φ i ≠ 0) → (∀ i j, φ i ≠ ψ j) →
    ∀ M : Matrix (Fin n) (Fin n) ℂ, M.IsHermitian → M.trace = 0 →
      ((∀ i j, (weakValue (φ i) (ψ j) M).im = 0) ↔ M ∈ realSpan φ ψ)

/-- The conjecture fails for `n = 3`: with the standard basis, the columns of the orthogonal
matrix `(1/3)[[1,2,2],[2,1,-2],[2,-2,1]]` and `M = E₀₁ + E₁₀`, all nine weak values are real
while `M ∉ ℛ_{φ,ψ}`. -/
theorem result : ¬ claim := by
  intro h
  let φ : Fin 3 → Fin 3 → ℂ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]
  let ψ : Fin 3 → Fin 3 → ℂ :=
    ![![1/3, 2/3, 2/3], ![2/3, 1/3, -2/3], ![2/3, -2/3, 1/3]]
  let M : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  have hφ : IsONB φ := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [φ, dotProduct, Fin.sum_univ_three]
  have hψ : IsONB ψ := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [ψ, dotProduct, Fin.sum_univ_three, map_ofNat, map_div₀, map_neg] <;> norm_num
  have hov : ∀ i j, star (ψ j) ⬝ᵥ φ i ≠ 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [φ, ψ, dotProduct, Fin.sum_univ_three, map_ofNat, map_div₀, map_neg]
  have hne : ∀ i j, φ i ≠ ψ j := by
    intro i j hij
    have h0 := congrFun hij 0
    fin_cases i <;> fin_cases j <;> norm_num [φ, ψ] at h0
  have hM : M.IsHermitian := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [M]
  have htr : M.trace = 0 := by simp [M, Matrix.trace, Fin.sum_univ_three]
  have hreal : ∀ i j, (weakValue (φ i) (ψ j) M).im = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [weakValue, φ, ψ, M, dotProduct, mulVec, Fin.sum_univ_three, map_ofNat, map_div₀,
        map_neg] <;> norm_num
  have hnot : M ∉ realSpan φ ψ := by
    intro hmem
    rw [realSpan, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    have e01 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => (A 0 1).re) hc
    have e02 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => (A 0 2).re) hc
    have e12 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => (A 1 2).re) hc
    simp [Fintype.sum_sum_type, Fin.sum_univ_three, tracelessProj, φ, ψ, M, vecMulVec, map_ofNat,
      map_div₀, map_neg] at e01 e02 e12
    norm_num at e01 e02 e12
    linarith
  exact hnot ((h 3 φ ψ (by norm_num) hφ hψ hov hne M hM htr).mp hreal)

end D5.S3.Quantum.Measurement.QunitRealWeakValueRefutation
