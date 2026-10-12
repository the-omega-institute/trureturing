/- GID: D5/S3/Quantum/Schatten/Holder
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/Holder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Product Schatten Holder inequality for every positive exponent. -/

/-
Attributed source: leanprover-community/physlib, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142.
Original module: QuantumInfo/ForMathlib/HermitianMat/Schatten.lean.
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
Full license: docs/reports/inoutbalance/physlib-LICENSE.txt.
Retire this transplant when an equivalent consumed declaration exists in the
repository-pinned Mathlib, replacing it by direct application.
No mathematical originality is claimed for the attributed source.
-/
module

public import D5.S3.Quantum.Schatten.PowerMajorization

@[expose] public section

variable {d : Type*} [Fintype d] [DecidableEq d]
noncomputable section

noncomputable def schattenNorm (A : Matrix d d ℂ) (p : ℝ) : ℝ :=
  RCLike.re ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).cfc (· ^ (p/2))).trace ^ (1/p)


lemma schattenNorm_nonneg (A : Matrix d d ℂ) (p : ℝ) :
    0 ≤ schattenNorm A p := by
  by_cases hp : p = 0 <;> simp [ *, schattenNorm ];
  by_cases h₁ : 0 ≤ RCLike.re ( Matrix.trace ( Matrix.IsHermitian.cfc ( Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose ) fun x => x ^ ( p / 2 ) ) ) <;> simp_all [ Real.rpow_nonneg ];
  contrapose! h₁; simp_all [Matrix.trace ] ; ring_nf; norm_num [ Real.exp_nonneg, Real.log_nonneg ] ; (
  refine' Finset.sum_nonneg fun i _ => _ ; norm_num [ Matrix.IsHermitian.cfc ] ; ring_nf ; norm_num [ Real.exp_nonneg, Real.log_nonneg ] ; (
  simp [ Matrix.mul_apply, Matrix.diagonal ] ; ring_nf ; norm_num [ Real.exp_nonneg, Real.log_nonneg ] ; (
  --TODO: If we import Order, the whole line is just `positivity`.
  exact Finset.sum_nonneg fun _ _ => add_nonneg ( mul_nonneg ( sq_nonneg _ ) ( Real.rpow_nonneg (
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A _) ) _ ) ) ( mul_nonneg ( Real.rpow_nonneg (
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A _) ) _ ) ( sq_nonneg _ ) ))));


lemma schattenNorm_trace_as_eigenvalue_sum (A : Matrix d d ℂ) (p : ℝ) :
    RCLike.re ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).cfc (· ^ (p/2))).trace =
    ∑ i : d, ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i) ^ (p/2) := by
  rw [ Matrix.IsHermitian.cfc ];
  simp [ Matrix.trace_mul_comm, Matrix.mul_assoc ]

/-
The Schatten p-norm raised to the p-th power equals the sum of singular values
    raised to the p-th power: `‖A‖_p^p = ∑ σᵢ(A)^p`.
-/
lemma schattenNorm_rpow_eq_sum_singularValues (A : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p ^ p = ∑ i : d, singularValues A i ^ p := by
  unfold schattenNorm;
  rw [ ← Real.rpow_mul ( _ ), one_div_mul_cancel hp.ne', Real.rpow_one ];
  · convert schattenNorm_trace_as_eigenvalue_sum A p using 1
    refine' Finset.sum_congr rfl fun i _ => _;
    unfold singularValues; rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( _ ) ]
    ring_nf
    simp +zetaDelta at *;
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i;
  · have h_nonneg : ∀ i : d, 0 ≤ ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i) ^ (p / 2) := by
      exact fun i => Real.rpow_nonneg ( by have := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A; aesop ) _;
    convert! Finset.sum_nonneg fun i _ => h_nonneg i using 1;
    convert schattenNorm_trace_as_eigenvalue_sum A p using 1

/- The Schatten p-norm equals the ℓ^p quasi-norm of the singular values:
    `‖A‖_p = (∑ σᵢ(A)^p)^{1/p}`. -/
lemma schattenNorm_eq_sum_singularValues_rpow (A : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p = (∑ i : d, singularValues A i ^ p) ^ (1/p) := by
  rw [ ←schattenNorm_rpow_eq_sum_singularValues A hp ];
  rw [ ← Real.rpow_mul ( by exact Real.rpow_nonneg ( by
    simp [ Matrix.trace ];
    refine' Finset.sum_nonneg fun i _ => _;
    rw [ Matrix.IsHermitian.cfc ];
    simp [ Matrix.mul_apply, Matrix.diagonal ];
    field_simp;
    exact Finset.sum_nonneg fun _ _ => mul_nonneg ( Real.rpow_nonneg ( by
      exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg A _ ) _ ) ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ) _ ), mul_one_div_cancel hp.ne', Real.rpow_one ]

lemma schattenNorm_mul_le (A B : Matrix d d ℂ) {r p q : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hq : 0 < q) (hpqr : 1 / r = 1 / p + 1 / q) :
    schattenNorm (A * B) r ≤ schattenNorm A p * schattenNorm B q := by
  -- It suffices to show the inequality for r-th powers, since x ↦ x^{1/r} is monotone.
  rw [schattenNorm_eq_sum_singularValues_rpow (A * B) hr,
      schattenNorm_eq_sum_singularValues_rpow A hp,
      schattenNorm_eq_sum_singularValues_rpow B hq]
  -- Rewrite sums over d to sums over Fin (Fintype.card d) via sorted singular values
  rw [sum_singularValues_rpow_eq_sum_sorted (A * B) r,
      sum_singularValues_rpow_eq_sum_sorted A p,
      sum_singularValues_rpow_eq_sum_sorted B q]
  -- Now we need:
  -- (∑ σ↓ᵢ(AB)^r)^{1/r} ≤ (∑ σ↓ᵢ(A)^p)^{1/p} · (∑ σ↓ᵢ(B)^q)^{1/q}
  -- Step 1: From sum_rpow_singularValues_mul_le, we have
  --   ∑ σ↓ᵢ(AB)^r ≤ ∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r
  have h_sv_ineq := sum_rpow_singularValues_mul_le A B hr
  -- Step 2: From holder_step_for_singularValues, we have
  --   ∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σ↓ᵢ(A)^p)^{r/p} · (∑ σ↓ᵢ(B)^q)^{r/q}
  have h_holder := holder_step_for_singularValues A B hr hp hq hpqr
  -- Step 3: Combine and take 1/r-th power
  -- Need: (∑ σ↓ᵢ(AB)^r)^{1/r} ≤ ((∑ σ↓ᵢ(A)^p)^{r/p} · (∑ σ↓ᵢ(B)^q)^{r/q})^{1/r}
  --      = (∑ σ↓ᵢ(A)^p)^{1/p} · (∑ σ↓ᵢ(B)^q)^{1/q}
  have h_combined : ∑ i, singularValuesSorted (A * B) i ^ r ≤
      (∑ i, singularValuesSorted A i ^ p) ^ (r / p) *
      (∑ i, singularValuesSorted B i ^ q) ^ (r / q) :=
    le_trans h_sv_ineq h_holder
  -- Take 1/r-th power of both sides
  have h_rpow : (∑ i, singularValuesSorted (A * B) i ^ r) ^ (1/r) ≤
      ((∑ i, singularValuesSorted A i ^ p) ^ (r / p) *
       (∑ i, singularValuesSorted B i ^ q) ^ (r / q)) ^ (1/r) := by
    apply Real.rpow_le_rpow
    · exact Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _
    · exact h_combined
    · positivity
  -- Simplify the RHS: (X^{r/p} · Y^{r/q})^{1/r} = X^{1/p} · Y^{1/q}
  have h_simplify :
      ((∑ i, singularValuesSorted A i ^ p) ^ (r / p) *
       (∑ i, singularValuesSorted B i ^ q) ^ (r / q)) ^ (1/r) =
      (∑ i, singularValuesSorted A i ^ p) ^ (1/p) *
      (∑ i, singularValuesSorted B i ^ q) ^ (1/q) := by
    have hsp : 0 ≤ (∑ i, singularValuesSorted A i ^ p) ^ (r / p) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _) _
    have hsq : 0 ≤ (∑ i, singularValuesSorted B i ^ q) ^ (r / q) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _) _
    rw [Real.mul_rpow hsp hsq]
    have hsp' : (0 : ℝ) ≤ ∑ i, singularValuesSorted A i ^ p :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _
    have hsq' : (0 : ℝ) ≤ ∑ i, singularValuesSorted B i ^ q :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _
    congr 1 <;> rw [← Real.rpow_mul (by assumption)] <;> congr 1 <;> field_simp
  linarith


#print axioms schattenNorm_mul_le

end
