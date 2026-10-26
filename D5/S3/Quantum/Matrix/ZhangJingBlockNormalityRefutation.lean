/- GID: D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.claim; result=D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.result; claim=D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.claim
   digest: An admissible scalar pair gives a positive block for a nonnormal complex matrix. -/

/-
result:
  proof_shape: bind-only (square-root uniqueness, diagonal functional calculus,
    Gram positivity, and exact scalar and matrix normalization).
  escape_witness: none.
  admission_basis: open-problem-resolution (#18699; Refuted).
  Direct frozen dependencies:
    D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
    statement_id: sha256:873e4955783786d99a250879f3da4640dab6550433b567150988ca3aaede9fe0.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The source expression for |A| is inlined as CFC.sqrt (Aᴴ * A), which is the
existing CFC.abs construction; no duplicate absolute-value definition is added.
The block and claim are source definitions, not additional theorem claims.
-/

import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

set_option autoImplicit false

open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation

/-- The block matrix `[[f(|A|), A*], [A, g(|A|)]]`, with `f(|A|)`, `g(|A|)` by the continuous functional
calculus. -/
noncomputable def block (f g : ℝ → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fromBlocks (cfc f ((CFC.sqrt (Aᴴ * A)))) Aᴴ A (cfc g ((CFC.sqrt (Aᴴ * A))))

/-- Zhang–Jing, ELA 41 (2025), Question 2.14 ("Let A ∈ M_n. Then [[f(|A|), A*], [A, g(|A|)]] ≥ 0 if and only
if A is normal under the conditions that f(x)g(x) = x² for x ≥ 0, f(x) ≥ g(x) (x ≥ 1) and g(x) ≥ f(x)
(0 ≤ x ≤ 1)."), as the assertion that the equivalence holds for every such pair `f, g` and every `A`. -/
def claim : Prop :=
  ∀ f g : ℝ → ℝ, (∀ x, 0 ≤ x → f x * g x = x ^ 2) → (∀ x, 1 ≤ x → g x ≤ f x) →
    (∀ x, 0 ≤ x → x ≤ 1 → f x ≤ g x) →
      ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℂ, (block f g A).PosSemidef ↔ Aᴴ * A = A * Aᴴ

set_option maxHeartbeats 800000 in
theorem result : ¬ D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.claim := by
  intro hc
  let g : ℝ → ℝ := fun x => 1 + (x - 1) / (1 + (x - 1)^2)
  let f : ℝ → ℝ := fun x => x^2 / g x
  have hd (x : ℝ) : 0 < 1 + (x - 1)^2 := by positivity
  have hg (x : ℝ) : 0 < g x := by
    dsimp [g]
    have he : -(1:ℝ) < (x-1) / (1+(x-1)^2) := by
      apply (lt_div_iff₀ (hd x)).2
      nlinarith [sq_nonneg (x - 1 + 1/2)]
    linarith
  have hprod (x : ℝ) (_ : 0 ≤ x) : f x * g x = x^2 := by
    exact div_mul_cancel₀ _ (ne_of_gt (hg x))
  have hhigh (x : ℝ) (hx : 1 ≤ x) : g x ≤ f x := by
    have hgx : g x ≤ x := by
      dsimp [g]
      have ht := mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (x-1))
      have he : (x-1) / (1+(x-1)^2) ≤ x-1 := by
        apply (div_le_iff₀ (hd x)).2
        nlinarith
      linarith
    apply (le_div_iff₀ (hg x)).2
    nlinarith [hg x]
  have hlow (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : f x ≤ g x := by
    have hxg : x ≤ g x := by
      dsimp [g]
      have ht := mul_nonneg (sub_nonneg.mpr hx1) (sq_nonneg (x-1))
      have he : x-1 ≤ (x-1) / (1+(x-1)^2) := by
        apply (le_div_iff₀ (hd x)).2
        nlinarith
      linarith
    apply (div_le_iff₀ (hg x)).2
    nlinarith [hg x]
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![0, 3/2; 3, 0]
  let d : Fin 2 → ℝ := ![3, 3/2]
  let D : Matrix (Fin 2) (Fin 2) ℂ := diagonal fun i => (d i : ℂ)
  have hD : D.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [d, Complex.nonneg_iff]
  have hsquare : D * D = Aᴴ * A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D, d, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat]
  have habs : (CFC.sqrt (Aᴴ * A)) = D := by
    exact CFC.sqrt_unique hsquare hD.nonneg
  have hfc : cfc f ((CFC.sqrt (Aᴴ * A))) = diagonal ![(45/7 : ℂ), 45/28] := by
    rw [habs]
    change cfc f (diagonal fun i => (d i : ℂ)) = _
    rw [D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num [d, f, g]
  have hgc : cfc g ((CFC.sqrt (Aᴴ * A))) = (7/5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [habs]
    change cfc g (diagonal fun i => (d i : ℂ)) = _
    rw [D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [d, g, Matrix.diagonal_apply]
  let Q : Matrix (Fin 2) (Fin 2 ⊕ Fin 2) ℂ := fromCols A ((7/5 : ℂ) • 1)
  have hgram : block f g A = (5/7 : ℝ) • (Qᴴ * Q) := by
    unfold block
    rw [hfc, hgc]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [Q, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.fromBlocks, Matrix.fromCols, Matrix.diagonal_apply, Complex.real_smul, map_ofNat]
  have hpos : (block f g A).PosSemidef := by
    rw [hgram]
    exact (Matrix.posSemidef_conjTranspose_mul_self Q).smul (by norm_num : (0 : ℝ) ≤ 5/7)
  have hnormal := (hc f g hprod hhigh hlow 2 A).mp hpos
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) hnormal
  norm_num [A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat] at he

end D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation
