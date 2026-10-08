/- GID: D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two-qubit fully entangled fraction is at most 1 - |c|/2, tight for every |c|. -/

/-
proof_shape:
  canonical_bound: content
  operator_bound: content
  result: content
  cs_form: bind-only (consumers psd_sub_rank_one, canonical_bound)
escape_witness: canonical_bound, the operator bound sigma <= (1 - |a(sigma)|/2) 1 for
  every positive semidefinite two-qubit sigma whose Bob marginal is 1/2, with a(sigma) the
  Bloch vector of its Alice marginal. It lies on the live path
  canonical_bound -> filtered_bound -> operator_bound -> maxent_le -> fef_le -> result
  and is not obtained from the frozen prerequisites by instantiation, projection or
  normalization.
admission_basis: open-problem-resolution (#14206; Proved)
Direct frozen dependencies (declaration statement_id):
  D5/S3/Quantum/FiniteDimensional.qubitX:
    sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
  D5/S3/Quantum/FiniteDimensional.qubitZ:
    sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli:
    sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X:
    sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y:
    sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z:
    sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix:
    sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft:
    sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight:
    sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceLeft:
    sha256:70e429b7996075b0f25052d5fb6f603c2ac2556abcf0d2510142499e0c5d267c
  D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight:
    sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_posSemidef:
    sha256:57037555d268cd6c22ff19563a5f64496a1d89f7e5d8b6b98943b78b84af873d
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_posSemidef:
    sha256:534be990ab7c643fd18c2a086aa7a7b696bb02a8baa49a26c15e479b63e74944
The Pauli matrices are the frozen pauliMatrix; pauli only indexes pauliMatrix .X, .Y, .Z by
Fin 3 and is consumed by blochA, blochB, corr.
Private declarations, each on the live path of result (consumer in brackets):
  content: rad_le_trace [canonical_bound, operator_bound, degenerate_bound],
    rad_rank_one [canonical_bound],
    psd_sub_rank_one [canonical_bound, degenerate_bound], filtered_bound [operator_bound],
    rank_one_det [degenerate_bound], trace_sq_le [overlap_sq_le],
    overlap_sq_le [degenerate_bound], degenerate_bound [operator_bound],
    tight_blochB, tight_blochA, tight_corr [tight_centre],
    tight_trace, tight_centre, tight_phase [result]
  bind-only: cs_form [psd_sub_rank_one, canonical_bound], the Mathlib Cauchy-Schwarz
    inequality inner_mul_inner_self_le for the form Matrix.toInnerProductSpace;
    pauli_zero, pauli_one, pauli_two [blochVec_zero, blochVec_one, blochVec_two,
    filtered_bound, tight_corr]; blochVec_zero, blochVec_one, blochVec_two [rad_le_trace,
    rad_rank_one, blochVec_scalar, filtered_bound, rank_one_det, tight_blochA, tight_blochB];
    vlen_eq_norm [vlen_add_le, vlen_smul]; vlen_add_le, vlen_smul [canonical_bound,
    degenerate_bound]; vlen_nonneg [filtered_bound]; blochVec_add, blochVec_smul
    [canonical_bound, degenerate_bound]; blochVec_sub, blochVec_scalar [canonical_bound];
    trace_mul_kron_one [canonical_bound, operator_bound, tight_blochA]; trace_mul_one_kron
    [filtered_bound, operator_bound, degenerate_bound, tight_blochB]; form_one_kron
    [degenerate_bound, maxent_le]; ptL_conj, trace_conj_kron, kron_sub, form_conj_mul
    [filtered_bound]; ptL_sub [canonical_bound, degenerate_bound]; ptL_smul [canonical_bound,
    filtered_bound, degenerate_bound]; ptR_sub, ptR_smul [canonical_bound];
    form_conj [cs_form, psd_sub_rank_one]; form_real [psd_sub_rank_one, canonical_bound,
    degenerate_bound]; form_vecMulVec [psd_sub_rank_one]; trace_vecMulVec [canonical_bound,
    degenerate_bound]; halfPhase_mul [phase_max, tight_phase]; phase_max [fef_le, result];
    maxent_le [fef_le, result]; fef_le [result]; tight_psd [result]; tight_entry
    [tight_trace, tight_blochA, tight_blochB, tight_corr, tight_phase]; vlen_e3 [tight_centre].
Utility: none. The module proves a universal inequality and a tightness statement for
every t in [0, 1]; the explicit family tight t is the existential witness of the second
clause for every parameter, not a finite certificate, enumeration, checker or numeric
reduction.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli pauliMatrix)

namespace D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction

/-!
A. Milne, D. Jennings, S. Jevtic and T. Rudolph, *Quantum correlations of two-qubit states
with one maximally mixed marginal*, Phys. Rev. A 90, 024302 (2014), arXiv:1404.3951v2,
Conjecture 2: for a two-qubit state `ρ` whose steering ellipsoid is centred at `c`, the fully
entangled fraction is tightly bounded as `f(ρ) ≤ 1 - |c|/2`. It holds.

Write `ρ_B` for Bob's marginal and `b` for its Bloch vector. If `|b| < 1`, a local filter
`1 ⊗ H` with `H ρ_B Hᴴ` proportional to the identity turns `ρ` into a state `σ` with Bob
marginal `1/2` and Alice Bloch vector `c`; the Cauchy–Schwarz bound `σ ⪰ w wᴴ / t` with
`w = σ φ`, `t = ⟨φ|σ|φ⟩`, applied to both marginals of the rank-one operator `w wᴴ` (which have
equal Bloch-vector length) gives `σ ⪯ (1 - |c|/2) 1`. Undoing the filter gives
`ρ ⪯ (2 - |c|) (1 ⊗ ρ_B)`. If `|b| = 1` the same Cauchy–Schwarz step shows `ρ ⪯ 1 ⊗ ρ_B`.
A maximally entangled `e` has `⟨e|1 ⊗ ρ_B|e⟩ = 1/2`. The states
`(|χ⟩⟨χ| + t(1 - t)|01⟩⟨01|)/(2 - t)` with `χ = |00⟩ + (1 - t)|11⟩` have `|c| = t` and attain
the bound on a multiple of `|00⟩ + |11⟩`.
-/

/-- Two-qubit operators; the first factor of the index is Alice's qubit. -/
local notation "TwoQubit" => Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The Pauli matrices `σ_x, σ_y, σ_z` indexed by `Fin 3`: the frozen `pauliMatrix` at the
labels `X`, `Y`, `Z`. -/
def pauli (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := pauliMatrix (![Pauli.X, Pauli.Y, Pauli.Z] i)

/-- Alice's Bloch vector `a_i = Re tr(ρ (σ_i ⊗ 1))`. -/
def blochA (ρ : TwoQubit) (i : Fin 3) : ℝ :=
  (trace (ρ * (pauli i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))).re

/-- Bob's Bloch vector `b_j = Re tr(ρ (1 ⊗ σ_j))`. -/
def blochB (ρ : TwoQubit) (j : Fin 3) : ℝ :=
  (trace (ρ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli j))).re

/-- The correlation matrix `T_ij = Re tr(ρ (σ_i ⊗ σ_j))`. -/
def corr (ρ : TwoQubit) (i j : Fin 3) : ℝ := (trace (ρ * (pauli i ⊗ₖ pauli j))).re

/-- The Euclidean length of a vector of `ℝ³`. -/
def vlen (v : Fin 3 → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- The centre of Alice's steering ellipsoid: `c = (a - T b)/(1 - |b|²)` when `|b| ≠ 1`, and
`c = a` when `|b| = 1`. -/
def centre (ρ : TwoQubit) : Fin 3 → ℝ :=
  if vlen (blochB ρ) = 1 then blochA ρ
  else fun i => (blochA ρ i - ∑ j, corr ρ i j * blochB ρ j) / (1 - vlen (blochB ρ) ^ 2)

/-- A maximally entangled vector: a unit vector both of whose reduced states are `1/2`. -/
def IsMaxEntangled (e : Fin 2 × Fin 2 → ℂ) : Prop :=
  ∑ k, ‖e k‖ ^ 2 = 1 ∧ partialTraceRight (vecMulVec e (star e)) = (1 / 2 : ℂ) • 1 ∧
    partialTraceLeft (vecMulVec e (star e)) = (1 / 2 : ℂ) • 1

/-- The fully entangled fraction: the supremum of `⟨e|ρ|e⟩` over maximally entangled `e`. -/
def fef (ρ : TwoQubit) : ℝ :=
  sSup {f | ∃ e, IsMaxEntangled e ∧ f = (star e ⬝ᵥ (ρ *ᵥ e)).re}

/-- Conjecture 2 of arXiv:1404.3951: `f(ρ) ≤ 1 - |c(ρ)|/2` for every two-qubit density
matrix, and every value `|c| = t ∈ [0, 1]` is attained by a state with `f = 1 - t/2`. -/
def claim : Prop :=
  (∀ ρ : TwoQubit, ρ.PosSemidef → trace ρ = 1 → fef ρ ≤ 1 - vlen (centre ρ) / 2) ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ ρ : TwoQubit, ρ.PosSemidef ∧ trace ρ = 1 ∧
      vlen (centre ρ) = t ∧ fef ρ = 1 - t / 2

private lemma pauli_zero : pauli 0 = !![0, 1; 1, 0] := by
  simp [pauli, pauliMatrix, qubitX]

private lemma pauli_one : pauli 1 = !![0, -Complex.I; Complex.I, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli, pauliMatrix, qubitX, qubitZ]

private lemma pauli_two : pauli 2 = !![1, 0; 0, -1] := by
  simp [pauli, pauliMatrix, qubitZ]

private def blochVec (X : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 3) : ℝ := (trace (X * pauli i)).re

private lemma blochVec_zero (X : Matrix (Fin 2) (Fin 2) ℂ) : blochVec X 0 = (X 0 1 + X 1 0).re := by
  simp [blochVec, pauli_zero, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private lemma blochVec_one (X : Matrix (Fin 2) (Fin 2) ℂ) :
    blochVec X 1 = (Complex.I * X 0 1 - Complex.I * X 1 0).re := by
  simp [blochVec, pauli_one, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

private lemma blochVec_two (X : Matrix (Fin 2) (Fin 2) ℂ) : blochVec X 2 = (X 0 0 - X 1 1).re := by
  simp [blochVec, pauli_two, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

private lemma vlen_eq_norm (v : Fin 3 → ℝ) :
    vlen v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ := by
  rw [EuclideanSpace.norm_eq]; simp [vlen, Real.norm_eq_abs, sq_abs]

private lemma vlen_add_le (u v : Fin 3 → ℝ) : vlen (u + v) ≤ vlen u + vlen v := by
  rw [vlen_eq_norm, vlen_eq_norm, vlen_eq_norm, WithLp.toLp_add]; exact norm_add_le _ _

private lemma vlen_smul (c : ℝ) (v : Fin 3 → ℝ) : vlen (c • v) = |c| * vlen v := by
  rw [vlen_eq_norm, vlen_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

private lemma vlen_nonneg (v : Fin 3 → ℝ) : 0 ≤ vlen v := Real.sqrt_nonneg _

private lemma blochVec_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    blochVec (X + Y) = blochVec X + blochVec Y := by
  funext i; simp [blochVec, add_mul, trace_add]

private lemma blochVec_sub (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    blochVec (X - Y) = blochVec X - blochVec Y := by
  funext i; simp [blochVec, sub_mul, trace_sub]

private lemma blochVec_smul (c : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    blochVec ((c : ℂ) • X) = c • blochVec X := by
  funext i; simp [blochVec, trace_smul]

private lemma blochVec_scalar (c : ℂ) : blochVec (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
  funext i; fin_cases i
  · simp [blochVec_zero]
  · simp [blochVec_one]
  · simp [blochVec_two]

private lemma rad_le_trace {Z : Matrix (Fin 2) (Fin 2) ℂ} (hZ : Z.PosSemidef) :
    vlen (blochVec Z) ≤ (trace Z).re := by
  have h10 : Z 1 0 = star (Z 0 1) := (hZ.isHermitian.apply 1 0).symm
  have d0 := Complex.le_def.mp (hZ.diag_nonneg (i := 0))
  have d1 := Complex.le_def.mp (hZ.diag_nonneg (i := 1))
  have hdet := Complex.le_def.mp hZ.det_nonneg
  rw [det_fin_two, h10] at hdet
  simp only [Complex.zero_re, Complex.zero_im, Complex.sub_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im] at d0 d1 hdet
  have htr : 0 ≤ (trace Z).re := by rw [trace_fin_two, Complex.add_re]; linarith [d0.1, d1.1]
  have key : ∑ i, blochVec Z i ^ 2 ≤ (trace Z).re ^ 2 := by
    rw [Fin.sum_univ_three, blochVec_zero, blochVec_one, blochVec_two, trace_fin_two, h10]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [hdet.1, d0.2, d1.2]
  calc vlen (blochVec Z) ≤ Real.sqrt ((trace Z).re ^ 2) := Real.sqrt_le_sqrt key
    _ = (trace Z).re := Real.sqrt_sq htr

private lemma rad_rank_one (w : Fin 2 × Fin 2 → ℂ) :
    vlen (blochVec (partialTraceRight (vecMulVec w (star w)))) =
      vlen (blochVec (partialTraceLeft (vecMulVec w (star w)))) := by
  unfold vlen; congr 1
  simp only [Fin.sum_univ_three, blochVec_zero, blochVec_one, blochVec_two, partialTraceRight,
    partialTraceLeft, vecMulVec_apply, Fin.sum_univ_two, Pi.star_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private lemma trace_mul_kron_one (ρ : TwoQubit) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (ρ * (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) = trace (partialTraceRight ρ * A) := by
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, partialTraceRight,
    Matrix.one_apply]
  ring

private lemma trace_mul_one_kron (ρ : TwoQubit) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (ρ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B)) = trace (partialTraceLeft ρ * B) := by
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, partialTraceLeft,
    Matrix.one_apply]
  ring

private lemma form_one_kron (B : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 × Fin 2 → ℂ) :
    star x ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B) *ᵥ x) =
      trace (B * partialTraceLeft (vecMulVec x (star x))) := by
  simp [dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.trace, Matrix.mul_apply,
    partialTraceLeft, vecMulVec_apply, Matrix.one_apply]
  ring

private lemma ptL_conj (K : Matrix (Fin 2) (Fin 2) ℂ) (ρ : TwoQubit) :
    partialTraceLeft (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * ρ *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K)ᴴ) =
      K * partialTraceLeft ρ * Kᴴ := by
  ext b d
  simp [partialTraceLeft, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Matrix.one_apply]
  ring

private lemma trace_conj_kron (K A : Matrix (Fin 2) (Fin 2) ℂ) (ρ : TwoQubit) :
    trace (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * ρ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K)ᴴ *
      (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) = trace (ρ * (A ⊗ₖ (Kᴴ * K))) := by
  have h : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K)ᴴ * (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) = A ⊗ₖ (Kᴴ * K) := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp
  rw [← h]
  set X := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K
  set Y := A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [show X * ρ * Xᴴ * Y = (X * ρ) * (Xᴴ * Y) by simp only [Matrix.mul_assoc], trace_mul_comm,
    show (Xᴴ * Y) * (X * ρ) = (Xᴴ * Y * X) * ρ by simp only [Matrix.mul_assoc], trace_mul_comm]

private lemma ptL_sub (x y : TwoQubit) :
    partialTraceLeft (x - y) = partialTraceLeft x - partialTraceLeft y := by
  ext b d; simp [partialTraceLeft, Finset.sum_sub_distrib]

private lemma ptR_sub (x y : TwoQubit) :
    partialTraceRight (x - y) = partialTraceRight x - partialTraceRight y := by
  ext b d; simp [partialTraceRight, Finset.sum_sub_distrib]

private lemma ptL_smul (c : ℂ) (x : TwoQubit) :
    partialTraceLeft (c • x) = c • partialTraceLeft x := by
  ext b d; simp [partialTraceLeft]; ring

private lemma ptR_smul (c : ℂ) (x : TwoQubit) :
    partialTraceRight (c • x) = c • partialTraceRight x := by
  ext b d; simp [partialTraceRight]; ring

private lemma form_conj {M : TwoQubit} (hM : M.IsHermitian) (x y : Fin 2 × Fin 2 → ℂ) :
    star (star x ⬝ᵥ (M *ᵥ y)) = star y ⬝ᵥ (M *ᵥ x) := by
  rw [← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec, hM.eq]

private lemma form_real {M : TwoQubit} (hM : M.PosSemidef) (x : Fin 2 × Fin 2 → ℂ) :
    star x ⬝ᵥ (M *ᵥ x) = ((star x ⬝ᵥ (M *ᵥ x)).re : ℂ) := by
  have h := Complex.le_def.mp (hM.dotProduct_mulVec_nonneg x)
  apply Complex.ext <;> simp
  simpa using h.2.symm

private lemma cs_form {M : TwoQubit} (hM : M.PosSemidef) (x y : Fin 2 × Fin 2 → ℂ) :
    Complex.normSq (star x ⬝ᵥ (M *ᵥ y)) ≤
      (star x ⬝ᵥ (M *ᵥ x)).re * (star y ⬝ᵥ (M *ᵥ y)).re := by
  let _ := M.toSeminormedAddCommGroup hM
  let _ := M.toInnerProductSpace hM
  have e : ∀ u v : Fin 2 × Fin 2 → ℂ, inner ℂ u v = star u ⬝ᵥ (M *ᵥ v) :=
    fun u v => dotProduct_comm _ _
  have h := inner_mul_inner_self_le (𝕜 := ℂ) x y
  rwa [e, e, e, e, ← form_conj hM.isHermitian x y, norm_star, ← sq,
    ← Complex.normSq_eq_norm_sq] at h

private lemma form_vecMulVec (w x : Fin 2 × Fin 2 → ℂ) :
    star x ⬝ᵥ (vecMulVec w (star w) *ᵥ x) = (star x ⬝ᵥ w) * (star w ⬝ᵥ x) := by
  simp [dotProduct, mulVec, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private lemma trace_vecMulVec (w : Fin 2 × Fin 2 → ℂ) :
    trace (vecMulVec w (star w)) = star w ⬝ᵥ w := by
  simp [Matrix.trace, vecMulVec_apply, dotProduct, mul_comm]

private lemma psd_sub_rank_one {M : TwoQubit} (hM : M.PosSemidef) (φ : Fin 2 × Fin 2 → ℂ)
    {t : ℝ} (ht : t = (star φ ⬝ᵥ (M *ᵥ φ)).re) (hpos : 0 < t) :
    (M - ((t⁻¹ : ℝ) : ℂ) • vecMulVec (M *ᵥ φ) (star (M *ᵥ φ))).PosSemidef := by
  have hc : (0 : ℂ) ≤ ((t⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.mpr (inv_nonneg.mpr hpos.le)
  have hW := (posSemidef_vecMulVec_self_star (M *ᵥ φ)).smul hc
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hM.isHermitian.sub hW.isHermitian) fun x => ?_
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, form_vecMulVec, smul_eq_mul]
  have hφx : star (M *ᵥ φ) ⬝ᵥ x = star (star x ⬝ᵥ (M *ᵥ φ)) := by
    rw [form_conj hM.isHermitian, star_mulVec, ← dotProduct_mulVec, hM.isHermitian.eq]
  rw [hφx, form_real hM x, Complex.star_def, Complex.mul_conj]
  have hcs := cs_form hM x φ
  rw [← ht] at hcs
  rw [Complex.le_def]
  constructor
  · simp only [Complex.zero_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have : t⁻¹ * Complex.normSq (star x ⬝ᵥ (M *ᵥ φ)) ≤ (star x ⬝ᵥ (M *ᵥ x)).re := by
      rw [inv_mul_le_iff₀ hpos]; linarith
    linarith
  · simp

/-- A positive semidefinite two-qubit operator whose Bob marginal is `1/2` satisfies
`σ ⪯ (1 - |a(σ)|/2) 1`, where `a(σ)` is the Bloch vector of its Alice marginal. -/
theorem canonical_bound (σ : TwoQubit) (hσ : σ.PosSemidef)
    (hB : partialTraceLeft σ = (1 / 2 : ℂ) • 1) (φ : Fin 2 × Fin 2 → ℂ) :
    (star φ ⬝ᵥ (σ *ᵥ φ)).re ≤ (1 - vlen (blochA σ) / 2) * (star φ ⬝ᵥ φ).re := by
  have hA : blochA σ = blochVec (partialTraceRight σ) := by
    funext i; simp only [blochA, blochVec, trace_mul_kron_one]
  have htrσ : trace σ = 1 := by
    rw [← trace_partialTraceLeft, hB, trace_smul, trace_one]; norm_num
  have hrA : vlen (blochA σ) ≤ 1 := by
    have := rad_le_trace (partialTraceRight_posSemidef hσ)
    rwa [trace_partialTraceRight, htrσ, Complex.one_re, ← hA] at this
  have hone : (1 : TwoQubit).PosSemidef := PosSemidef.one
  have hn0 : 0 ≤ (star φ ⬝ᵥ φ).re := by
    simpa using (Complex.le_def.mp (hone.dotProduct_mulVec_nonneg φ)).1
  set t := (star φ ⬝ᵥ (σ *ᵥ φ)).re with ht
  set n := (star φ ⬝ᵥ φ).re with hn
  have ht0 : 0 ≤ t := (Complex.le_def.mp (hσ.dotProduct_mulVec_nonneg φ)).1
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · rw [← h0]; exact mul_nonneg (by linarith) hn0
  set w := σ *ᵥ φ with hw
  have hD := psd_sub_rank_one hσ φ ht hpos
  set D := σ - ((t⁻¹ : ℝ) : ℂ) • vecMulVec w (star w) with hDdef
  set N := (star w ⬝ᵥ w).re with hN
  have eB : partialTraceLeft D =
      (1 / 2 : ℂ) • 1 - ((t⁻¹ : ℝ) : ℂ) • partialTraceLeft (vecMulVec w (star w)) := by
    rw [hDdef, ptL_sub, ptL_smul, hB]
  have eA : partialTraceRight σ =
      ((t⁻¹ : ℝ) : ℂ) • partialTraceRight (vecMulVec w (star w)) + partialTraceRight D := by
    rw [hDdef, ptR_sub, ptR_smul]; abel
  have radB : vlen (blochVec (partialTraceLeft D)) =
      t⁻¹ * vlen (blochVec (partialTraceLeft (vecMulVec w (star w)))) := by
    rw [eB, blochVec_sub, blochVec_scalar, blochVec_smul, zero_sub, ← neg_smul, vlen_smul, abs_neg,
      abs_of_pos (inv_pos.mpr hpos)]
  have trB : (trace (partialTraceLeft D)).re = 1 - t⁻¹ * N := by
    rw [eB, trace_sub, trace_smul, trace_smul, trace_one, trace_partialTraceLeft, trace_vecMulVec]
    simp [hN]
  have trA : (trace (partialTraceRight D)).re = 1 - t⁻¹ * N := by
    rw [trace_partialTraceRight, hDdef, trace_sub, trace_smul, htrσ, trace_vecMulVec]
    simp [hN]
  have hB1 := rad_le_trace (partialTraceLeft_posSemidef hD)
  have hA1 := rad_le_trace (partialTraceRight_posSemidef hD)
  have hAlice : vlen (blochA σ) ≤
      t⁻¹ * vlen (blochVec (partialTraceRight (vecMulVec w (star w)))) + (1 - t⁻¹ * N) := by
    rw [hA, eA, blochVec_add, blochVec_smul]
    calc vlen (t⁻¹ • blochVec (partialTraceRight (vecMulVec w (star w))) +
          blochVec (partialTraceRight D))
        ≤ vlen (t⁻¹ • blochVec (partialTraceRight (vecMulVec w (star w)))) +
          vlen (blochVec (partialTraceRight D)) := vlen_add_le _ _
      _ = t⁻¹ * vlen (blochVec (partialTraceRight (vecMulVec w (star w)))) +
          vlen (blochVec (partialTraceRight D)) := by
        rw [vlen_smul, abs_of_pos (inv_pos.mpr hpos)]
      _ ≤ _ := by linarith
  rw [rad_rank_one] at hAlice
  have hcomb : vlen (blochA σ) ≤ 2 - 2 * (t⁻¹ * N) := by linarith
  have hcs : t ^ 2 ≤ n * N := by
    have h := cs_form hone φ w
    simp only [one_mulVec] at h
    have hreal : star φ ⬝ᵥ w = (t : ℂ) := form_real hσ φ
    rw [hreal, Complex.normSq_ofReal] at h
    nlinarith
  have hNt : t⁻¹ * N ≤ 1 - vlen (blochA σ) / 2 := by linarith
  calc t = t⁻¹ * t ^ 2 := by field_simp
    _ ≤ t⁻¹ * (n * N) := by gcongr
    _ = (t⁻¹ * N) * n := by ring
    _ ≤ (1 - vlen (blochA σ) / 2) * n := by gcongr

private lemma form_conj_mul (X σ : TwoQubit) (x : Fin 2 × Fin 2 → ℂ) :
    star x ⬝ᵥ ((X * σ * Xᴴ) *ᵥ x) = star (Xᴴ *ᵥ x) ⬝ᵥ (σ *ᵥ (Xᴴ *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

private lemma kron_sub (A X Y : Matrix (Fin 2) (Fin 2) ℂ) : A ⊗ₖ (X - Y) = A ⊗ₖ X - A ⊗ₖ Y := by
  ext a b; simp [mul_sub]

private lemma filtered_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (hb : vlen (blochB ρ) < 1) (x : Fin 2 × Fin 2 → ℂ) :
    (star x ⬝ᵥ (ρ *ᵥ x)).re ≤ (2 - vlen (centre ρ)) *
      (star x ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ partialTraceLeft ρ) *ᵥ x)).re := by
  have hbP : blochB ρ = blochVec (partialTraceLeft ρ) := by
    funext j; simp only [blochB, blochVec, trace_mul_one_kron]
  set P := partialTraceLeft ρ with hPdef
  have hP : P.PosSemidef := partialTraceLeft_posSemidef hρ
  have htrP : trace P = 1 := by rw [hPdef, trace_partialTraceLeft, htr]
  set p := (P 0 0).re with hpdef
  set r := (P 1 1).re with hrdef
  set q := P 0 1 with hqdef
  have d0 := Complex.le_def.mp (hP.diag_nonneg (i := 0))
  have d1 := Complex.le_def.mp (hP.diag_nonneg (i := 1))
  have hP00 : P 0 0 = (p : ℂ) := Complex.ext rfl (by simpa using d0.2.symm)
  have hP11 : P 1 1 = (r : ℂ) := Complex.ext rfl (by simpa using d1.2.symm)
  have hP10 : P 1 0 = star q := (hP.isHermitian.apply 1 0).symm
  have hp0 : 0 ≤ p := by simpa using d0.1
  have hpr : p + r = 1 := by
    have := congrArg Complex.re htrP
    rw [trace_fin_two, hP00, hP11] at this; simpa using this
  set d := p * r - Complex.normSq q with hd
  have hlen : vlen (blochB ρ) ^ 2 = 1 - 4 * d := by
    rw [hbP, vlen, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_three,
      blochVec_zero, blochVec_one, blochVec_two, hP10, hP00, hP11, ← hqdef, hd,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re]
    linear_combination (p + r + 1) * hpr
  have hd0 : 0 < d := by nlinarith [vlen_nonneg (blochB ρ)]
  have hp : 0 < p := by
    rcases eq_or_lt_of_le hp0 with h | h
    · exfalso; rw [hd, ← h, zero_mul] at hd0; linarith [Complex.normSq_nonneg q]
    · exact h
  set u := Real.sqrt d with hudef
  have hu : u * u = d := Real.mul_self_sqrt hd0.le
  have huC : (u : ℂ) * u = d := by exact_mod_cast hu
  have hdC : (d : ℂ) = p * r - q * (starRingEnd ℂ) q := by
    rw [hd, Complex.mul_conj]; push_cast; ring
  have hprC : (p : ℂ) + r = 1 := by exact_mod_cast hpr
  have hPmat : P = !![(p : ℂ), q; star q, (r : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hP00, hP11, hP10, hqdef]
  set H : Matrix (Fin 2) (Fin 2) ℂ := !![(u : ℂ), 0; -star q, (p : ℂ)] with hHdef
  set G : Matrix (Fin 2) (Fin 2) ℂ := !![(p : ℂ), 0; star q, (u : ℂ)] with hGdef
  have H1 : H * P * Hᴴ = ((p * d : ℝ) : ℂ) • 1 := by
    rw [hPmat]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [hHdef, Matrix.mul_apply, Fin.sum_univ_two, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff, -mul_eq_zero]
    all_goals first
      | ring1
      | linear_combination (p : ℂ) * huC
      | linear_combination (-(p : ℂ)) * hdC
  have H2 : G * H = ((p * u : ℝ) : ℂ) • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hHdef, hGdef, Matrix.mul_apply, Fin.sum_univ_two, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff, -mul_eq_zero]
    all_goals ring1
  have H3 : G * Gᴴ = (p : ℂ) • P := by
    rw [hPmat]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [hGdef, Matrix.mul_apply, Fin.sum_univ_two, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff, -mul_eq_zero]
    all_goals first | ring1 | linear_combination huC + hdC
  have H4 : Hᴴ * H = (p : ℂ) • (1 - P) := by
    rw [hPmat]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [hHdef, Matrix.mul_apply, Fin.sum_univ_two, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff, -mul_eq_zero]
    all_goals first
      | ring1
      | linear_combination huC + hdC + (p : ℂ) * hprC
      | linear_combination (p : ℂ) * hprC
  have hbloch : (1 : Matrix (Fin 2) (Fin 2) ℂ) - P =
      (1 / 2 : ℂ) • (1 - ∑ j, ((blochVec P j : ℝ) : ℂ) • pauli j) := by
    rw [Fin.sum_univ_three, blochVec_zero, blochVec_one, blochVec_two, pauli_zero, pauli_one,
      pauli_two, hP10, hP00, hP11, ← hqdef, hPmat]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> apply Complex.ext <;> simp <;> linarith
  have hp2 : 0 < 2 * p * d := by positivity
  set c : ℝ := 1 / (2 * p * d) with hcdef
  set X : TwoQubit := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ H with hXdef
  set σ : TwoQubit := (c : ℂ) • (X * ρ * Xᴴ) with hσdef
  have hc0 : (0 : ℂ) ≤ (c : ℂ) := Complex.zero_le_real.mpr (by positivity)
  have hσ : σ.PosSemidef := (hρ.mul_mul_conjTranspose_same X).smul hc0
  have hσB : partialTraceLeft σ = (1 / 2 : ℂ) • 1 := by
    rw [hσdef, ptL_smul, hXdef, ptL_conj, ← hPdef, H1, smul_smul]
    congr 1; rw [hcdef]; push_cast; field_simp
  have hσA : blochA σ = centre ρ := by
    have hne : vlen (blochB ρ) ≠ 1 := ne_of_lt hb
    rw [centre, if_neg hne]
    funext i
    have htr_i : trace (σ * (pauli i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) =
        ((1 / (4 * d) : ℝ) : ℂ) * (trace (ρ * (pauli i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) -
          ∑ j, ((blochVec P j : ℝ) : ℂ) * trace (ρ * (pauli i ⊗ₖ pauli j))) := by
      rw [hσdef, Matrix.smul_mul, trace_smul, hXdef, trace_conj_kron, H4, hbloch, smul_smul,
        kronecker_smul, Matrix.mul_smul, trace_smul, kron_sub, Matrix.mul_sub, trace_sub,
        Fin.sum_univ_three, Fin.sum_univ_three, kronecker_add, kronecker_add, kronecker_smul,
        kronecker_smul, kronecker_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul,
        Matrix.mul_smul, Matrix.mul_smul, trace_add, trace_add, trace_smul, trace_smul, trace_smul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
      congr 1
      rw [hcdef]; push_cast; field_simp; ring
    simp only [blochA]
    rw [htr_i, Complex.re_ofReal_mul, Complex.sub_re, Complex.re_sum]
    simp only [Complex.re_ofReal_mul]
    rw [hlen, ← hbP]
    simp only [corr]
    have h4d : (1 : ℝ) - (1 - 4 * d) = 4 * d := by ring
    rw [h4d]
    field_simp
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  set Y : TwoQubit := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ G with hYdef
  have hYX : Y * X = ((p * u : ℝ) : ℂ) • 1 := by
    rw [hYdef, hXdef, ← mul_kronecker_mul, Matrix.one_mul, H2, kronecker_smul, one_kronecker_one]
  have hT : Y * σ * Yᴴ = ((p / 2 : ℝ) : ℂ) • ρ := by
    have e : Y * σ * Yᴴ = (c : ℂ) • ((Y * X) * ρ * (Y * X)ᴴ) := by
      rw [hσdef, Matrix.mul_smul, Matrix.smul_mul, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e, hYX, conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
    congr 1
    rw [hcdef, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    nlinarith [hu]
  have hYY : Y * Yᴴ = (p : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P) := by
    rw [hYdef, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, H3,
      kronecker_smul]
  have hrho : ρ = ((2 / p : ℝ) : ℂ) • (Y * σ * Yᴴ) := by
    rw [hT, smul_smul, ← Complex.ofReal_mul, show 2 / p * (p / 2) = (1 : ℝ) by field_simp,
      Complex.ofReal_one, one_smul]
  have hF : star x ⬝ᵥ (ρ *ᵥ x) =
      ((2 / p : ℝ) : ℂ) * (star (Yᴴ *ᵥ x) ⬝ᵥ (σ *ᵥ (Yᴴ *ᵥ x))) := by
    conv_lhs => rw [hrho]
    rw [smul_mulVec, dotProduct_smul, form_conj_mul, smul_eq_mul]
  have hN : star (Yᴴ *ᵥ x) ⬝ᵥ (Yᴴ *ᵥ x) =
      (p : ℂ) * (star x ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P) *ᵥ x)) := by
    have h := form_conj_mul Y 1 x
    rw [Matrix.mul_one, hYY, one_mulVec] at h
    rw [← h, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hcan := canonical_bound σ hσ hσB (Yᴴ *ᵥ x)
  rw [hσA, hN, Complex.re_ofReal_mul] at hcan
  rw [hF, Complex.re_ofReal_mul]
  have hp2' : 0 ≤ 2 / p := by positivity
  calc 2 / p * (star (Yᴴ *ᵥ x) ⬝ᵥ (σ *ᵥ (Yᴴ *ᵥ x))).re
      ≤ 2 / p * ((1 - vlen (centre ρ) / 2) *
          (p * (star x ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P) *ᵥ x)).re)) := by gcongr
    _ = (2 - vlen (centre ρ)) * (star x ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P) *ᵥ x)).re := by
      field_simp

private lemma rank_one_det (w : Fin 2 × Fin 2 → ℂ)
    (h : (star w ⬝ᵥ w).re ≤ vlen (blochVec (partialTraceLeft (vecMulVec w (star w))))) :
    w (0, 0) * w (1, 1) = w (0, 1) * w (1, 0) := by
  have hN0 : 0 ≤ (star w ⬝ᵥ w).re := by
    simpa using (Complex.le_def.mp
      ((PosSemidef.one (n := Fin 2 × Fin 2) (R := ℂ)).dotProduct_mulVec_nonneg w)).1
  have hsq : (star w ⬝ᵥ w).re ^ 2 ≤ vlen (blochVec (partialTraceLeft (vecMulVec w (star w)))) ^ 2 :=
    pow_le_pow_left₀ hN0 h 2
  have hid : vlen (blochVec (partialTraceLeft (vecMulVec w (star w)))) ^ 2 =
      (star w ⬝ᵥ w).re ^ 2 - 4 * Complex.normSq (w (0, 0) * w (1, 1) - w (0, 1) * w (1, 0)) := by
    rw [vlen, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp only [Fin.sum_univ_three, blochVec_zero, blochVec_one, blochVec_two, partialTraceLeft,
      vecMulVec_apply, Fin.sum_univ_two, Pi.star_apply, dotProduct, Fintype.sum_prod_type,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.sub_im, Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    ring
  have h0 : Complex.normSq (w (0, 0) * w (1, 1) - w (0, 1) * w (1, 0)) = 0 := by
    have := Complex.normSq_nonneg (w (0, 0) * w (1, 1) - w (0, 1) * w (1, 0)); nlinarith
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp h0)

private lemma trace_sq_le (a b c d : ℂ) (h : a * d = b * c) :
    Complex.normSq (a + d) ≤ Complex.normSq a + Complex.normSq b + Complex.normSq c +
      Complex.normSq d := by
  rw [Complex.normSq_add]
  have h1 : (a * (starRingEnd ℂ) d).re ≤ ‖a‖ * ‖d‖ := by
    calc (a * (starRingEnd ℂ) d).re ≤ ‖a * (starRingEnd ℂ) d‖ := Complex.re_le_norm _
      _ = ‖a‖ * ‖d‖ := by rw [norm_mul, Complex.norm_conj]
  have h2 : ‖a‖ * ‖d‖ = ‖b‖ * ‖c‖ := by rw [← norm_mul, ← norm_mul, h]
  have h3 : 2 * (‖b‖ * ‖c‖) ≤ ‖b‖ ^ 2 + ‖c‖ ^ 2 := by nlinarith [sq_nonneg (‖b‖ - ‖c‖)]
  rw [Complex.normSq_eq_norm_sq b, Complex.normSq_eq_norm_sq c]
  linarith

private lemma overlap_sq_le (w x : Fin 2 × Fin 2 → ℂ)
    (hdet : w (0, 0) * w (1, 1) = w (0, 1) * w (1, 0)) :
    Complex.normSq (star x ⬝ᵥ w) ≤
      (trace (partialTraceLeft (vecMulVec w (star w)) *
        partialTraceLeft (vecMulVec x (star x)))).re := by
  set A : Fin 2 → Fin 2 → ℂ := fun i k => ∑ j, w (i, j) * star (x (k, j)) with hA
  have e1 : star x ⬝ᵥ w = A 0 0 + A 1 1 := by
    simp [hA, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; ring
  have e2 : trace (partialTraceLeft (vecMulVec w (star w)) *
      partialTraceLeft (vecMulVec x (star x))) =
      A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1) + A 1 0 * star (A 1 0) +
        A 1 1 * star (A 1 1) := by
    simp [hA, Matrix.trace, Matrix.mul_apply, partialTraceLeft, vecMulVec_apply, Fin.sum_univ_two,
      star_add, star_mul']
    ring
  have e3 : A 0 0 * A 1 1 = A 0 1 * A 1 0 := by
    have : A 0 0 * A 1 1 - A 0 1 * A 1 0 =
        (w (0, 0) * w (1, 1) - w (0, 1) * w (1, 0)) *
          (star (x (0, 0)) * star (x (1, 1)) - star (x (0, 1)) * star (x (1, 0))) := by
      simp [hA, Fin.sum_univ_two]; ring
    rw [hdet, sub_self, zero_mul] at this
    exact sub_eq_zero.mp this
  rw [e1, e2]
  simp only [Complex.add_re, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  exact trace_sq_le _ _ _ _ e3

private lemma degenerate_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (hb : vlen (blochB ρ) = 1) (x : Fin 2 × Fin 2 → ℂ) :
    (star x ⬝ᵥ (ρ *ᵥ x)).re ≤
      (star x ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ partialTraceLeft ρ) *ᵥ x)).re := by
  have hbP : blochB ρ = blochVec (partialTraceLeft ρ) := by
    funext j; simp only [blochB, blochVec, trace_mul_one_kron]
  set P := partialTraceLeft ρ with hPdef
  have hP : P.PosSemidef := partialTraceLeft_posSemidef hρ
  have hR0 : 0 ≤ (star x ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P) *ᵥ x)).re :=
    (Complex.le_def.mp ((PosSemidef.one.kronecker hP).dotProduct_mulVec_nonneg x)).1
  set t := (star x ⬝ᵥ (ρ *ᵥ x)).re with ht
  have ht0 : 0 ≤ t := (Complex.le_def.mp (hρ.dotProduct_mulVec_nonneg x)).1
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · rw [← h0]; exact hR0
  set w := ρ *ᵥ x with hw
  have hD := psd_sub_rank_one hρ x ht hpos
  set D := ρ - ((t⁻¹ : ℝ) : ℂ) • vecMulVec w (star w) with hDdef
  set N := (star w ⬝ᵥ w).re with hN
  set RB := partialTraceLeft (vecMulVec w (star w)) with hRB
  have eB : partialTraceLeft D = P - ((t⁻¹ : ℝ) : ℂ) • RB := by
    rw [hDdef, ptL_sub, ptL_smul]
  have hZB := partialTraceLeft_posSemidef hD
  have trB : (trace (partialTraceLeft D)).re = 1 - t⁻¹ * N := by
    rw [trace_partialTraceLeft, hDdef, trace_sub, trace_smul, htr, trace_vecMulVec]
    simp [hN]
  have hB1 := rad_le_trace hZB
  have hsplit : vlen (blochVec P) ≤ vlen (blochVec (partialTraceLeft D)) +
      t⁻¹ * vlen (blochVec RB) := by
    have e : P = partialTraceLeft D + ((t⁻¹ : ℝ) : ℂ) • RB := by rw [eB]; abel
    calc vlen (blochVec P) = vlen (blochVec (partialTraceLeft D) + t⁻¹ • blochVec RB) := by
          conv_lhs => rw [e]
          rw [blochVec_add, blochVec_smul]
      _ ≤ vlen (blochVec (partialTraceLeft D)) + vlen (t⁻¹ • blochVec RB) := vlen_add_le _ _
      _ = _ := by rw [vlen_smul, abs_of_pos (inv_pos.mpr hpos)]
  rw [← hbP, hb] at hsplit
  have hge : N ≤ vlen (blochVec RB) := by
    have : t⁻¹ * N ≤ t⁻¹ * vlen (blochVec RB) := by linarith
    exact le_of_mul_le_mul_left this (inv_pos.mpr hpos)
  have hdet := rank_one_det w hge
  have hkey := overlap_sq_le w x hdet
  have hreal : star x ⬝ᵥ w = (t : ℂ) := form_real hρ x
  rw [hreal, Complex.normSq_ofReal] at hkey
  set NX := partialTraceLeft (vecMulVec x (star x)) with hNX
  have hZN : 0 ≤ (trace (partialTraceLeft D * NX)).re := by
    rw [← form_one_kron]
    exact (Complex.le_def.mp ((PosSemidef.one.kronecker hZB).dotProduct_mulVec_nonneg x)).1
  have hsplitN : (trace (partialTraceLeft D * NX)).re =
      (trace (P * NX)).re - t⁻¹ * (trace (RB * NX)).re := by
    rw [eB, Matrix.sub_mul, Matrix.smul_mul, trace_sub, trace_smul, Complex.sub_re, smul_eq_mul,
      Complex.re_ofReal_mul]
  have hPN : (trace (P * NX)).re =
      (star x ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P) *ᵥ x)).re := by
    rw [form_one_kron]
  rw [← hPN]
  have h1 : t * t ≤ t * (trace (P * NX)).re := by
    have : t⁻¹ * (trace (RB * NX)).re ≤ (trace (P * NX)).re := by linarith
    have h2 : (trace (RB * NX)).re ≤ t * (trace (P * NX)).re := by
      rwa [inv_mul_le_iff₀ hpos] at this
    linarith
  exact le_of_mul_le_mul_left h1 hpos

/-- Every two-qubit density matrix satisfies `ρ ⪯ (2 - |c(ρ)|) (1 ⊗ ρ_B)`. -/
theorem operator_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (x : Fin 2 × Fin 2 → ℂ) :
    (star x ⬝ᵥ (ρ *ᵥ x)).re ≤ (2 - vlen (centre ρ)) *
      (star x ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ partialTraceLeft ρ) *ᵥ x)).re := by
  have hR0 : 0 ≤ (star x ⬝ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ partialTraceLeft ρ) *ᵥ x)).re :=
    (Complex.le_def.mp ((PosSemidef.one.kronecker
      (partialTraceLeft_posSemidef hρ)).dotProduct_mulVec_nonneg x)).1
  by_cases hb : vlen (blochB ρ) = 1
  · have hc : centre ρ = blochA ρ := by rw [centre, if_pos hb]
    have hA : vlen (blochA ρ) ≤ 1 := by
      have := rad_le_trace (partialTraceRight_posSemidef hρ)
      have e : blochA ρ = blochVec (partialTraceRight ρ) := by
        funext i; simp only [blochA, blochVec, trace_mul_kron_one]
      rwa [trace_partialTraceRight, htr, Complex.one_re, ← e] at this
    rw [hc]
    have := degenerate_bound ρ hρ htr hb x
    nlinarith
  · have hle : vlen (blochB ρ) ≤ 1 := by
      have := rad_le_trace (partialTraceLeft_posSemidef hρ)
      have e : blochB ρ = blochVec (partialTraceLeft ρ) := by
        funext j; simp only [blochB, blochVec, trace_mul_one_kron]
      rwa [trace_partialTraceLeft, htr, Complex.one_re, ← e] at this
    exact filtered_bound ρ hρ htr (lt_of_le_of_ne hle hb) x

private def halfPhase : ℂ := (1 + Complex.I) / 2

private lemma halfPhase_mul : halfPhase * (starRingEnd ℂ) halfPhase = 2⁻¹ := by
  rw [halfPhase, Complex.mul_conj]
  simp [Complex.normSq_apply]; norm_num

private def phase : Fin 2 × Fin 2 → ℂ := fun k => if k.1 = k.2 then halfPhase else 0

private lemma phase_max : IsMaxEntangled phase := by
  have hn : ‖halfPhase‖ ^ 2 = 1 / 2 := by
    rw [Complex.sq_norm, halfPhase]; simp [Complex.normSq_apply]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · simp [phase, Fintype.sum_prod_type, Fin.sum_univ_two, hn]
    norm_num
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [phase, partialTraceRight, vecMulVec_apply, halfPhase_mul]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [phase, partialTraceLeft, vecMulVec_apply, halfPhase_mul]

private lemma maxent_le (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (e : Fin 2 × Fin 2 → ℂ) (he : IsMaxEntangled e) :
    (star e ⬝ᵥ (ρ *ᵥ e)).re ≤ 1 - vlen (centre ρ) / 2 := by
  have h := operator_bound ρ hρ htr e
  rw [form_one_kron, he.2.2, Matrix.mul_smul, Matrix.mul_one, trace_smul, trace_partialTraceLeft,
    htr] at h
  norm_num at h
  linarith

private lemma fef_le (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    fef ρ ≤ 1 - vlen (centre ρ) / 2 :=
  csSup_le ⟨_, phase, phase_max, rfl⟩ fun _ ⟨e, he, hf⟩ => hf ▸ maxent_le ρ hρ htr e he

private def tv (t : ℝ) (k : Fin 2 × Fin 2) : ℝ := ![![1, 0], ![0, 1 - t]] k.1 k.2

private def ev (k : Fin 2 × Fin 2) : ℝ := ![![0, 1], ![0, 0]] k.1 k.2

private def tight (t : ℝ) : TwoQubit :=
  ((1 / (2 - t) : ℝ) : ℂ) • (vecMulVec (fun k => (tv t k : ℂ)) (star fun k => (tv t k : ℂ)) +
    ((t * (1 - t) : ℝ) : ℂ) • vecMulVec (fun k => (ev k : ℂ)) (star fun k => (ev k : ℂ)))

private lemma tight_psd (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (tight t).PosSemidef := by
  have h1 : (0 : ℂ) ≤ ((1 / (2 - t) : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (div_nonneg zero_le_one (by linarith))
  have h2 : (0 : ℂ) ≤ ((t * (1 - t) : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (mul_nonneg ht0 (by linarith))
  exact ((posSemidef_vecMulVec_self_star _).add
    ((posSemidef_vecMulVec_self_star _).smul h2)).smul h1

private lemma tight_entry (t : ℝ) (x y : Fin 2 × Fin 2) :
    tight t x y = ((1 / (2 - t) : ℝ) : ℂ) *
      ((tv t x * tv t y + t * (1 - t) * (ev x * ev y) : ℝ) : ℂ) := by
  simp only [tight, Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply, Pi.star_apply,
    Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  push_cast; ring

private lemma tight_trace (t : ℝ) (ht1 : t ≤ 1) : trace (tight t) = 1 := by
  have h2' : (2 : ℝ) - t ≠ 0 := by linarith
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, tight_entry,
    ← mul_add, ← Complex.ofReal_add, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_one]; congr 1
  simp [tv, ev]
  field_simp
  ring

private lemma vlen_e3 (s : ℝ) : vlen ![0, 0, s] = |s| := by
  simp [vlen, Fin.sum_univ_three, Real.sqrt_sq_eq_abs]

private lemma tight_blochB (t : ℝ) (ht1 : t ≤ 1) : blochB (tight t) = ![0, 0, t / (2 - t)] := by
  have h2' : (2 : ℝ) - t ≠ 0 := by linarith
  have e : blochB (tight t) = blochVec (partialTraceLeft (tight t)) := by
    funext j; simp only [blochB, blochVec, trace_mul_one_kron]
  have h2 : blochVec (partialTraceLeft (tight t)) 2 = t / (2 - t) := by
    simp only [blochVec_two, partialTraceLeft, Fin.sum_univ_two, tight_entry]
    set s : ℝ := 1 / (2 - t) with hs
    simp [tv, ev]
    rw [hs]; field_simp; ring
  rw [e]
  funext j; fin_cases j
  · simp [blochVec_zero, partialTraceLeft, Fin.sum_univ_two, tight_entry, tv, ev]
  · simp [blochVec_one, partialTraceLeft, Fin.sum_univ_two, tight_entry, tv, ev]
  · simpa using h2

private lemma tight_blochA (t : ℝ) (ht1 : t ≤ 1) :
    blochA (tight t) = ![0, 0, t * (3 - 2 * t) / (2 - t)] := by
  have h2' : (2 : ℝ) - t ≠ 0 := by linarith
  have e : blochA (tight t) = blochVec (partialTraceRight (tight t)) := by
    funext i; simp only [blochA, blochVec, trace_mul_kron_one]
  have h2 : blochVec (partialTraceRight (tight t)) 2 = t * (3 - 2 * t) / (2 - t) := by
    simp only [blochVec_two, partialTraceRight, Fin.sum_univ_two, tight_entry]
    set s : ℝ := 1 / (2 - t) with hs
    simp [tv, ev]
    rw [hs]; field_simp; ring
  rw [e]
  funext j; fin_cases j
  · simp [blochVec_zero, partialTraceRight, Fin.sum_univ_two, tight_entry, tv, ev]
  · simp [blochVec_one, partialTraceRight, Fin.sum_univ_two, tight_entry, tv, ev]
  · simpa using h2

private lemma tight_corr (t : ℝ) (ht1 : t ≤ 1) :
    corr (tight t) 0 2 = 0 ∧ corr (tight t) 1 2 = 0 ∧
      corr (tight t) 2 2 = (2 - 3 * t + 2 * t ^ 2) / (2 - t) := by
  have h2' : (2 : ℝ) - t ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp [corr, pauli_zero, pauli_two, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, tight_entry, tv, ev]
  · simp [corr, pauli_one, pauli_two, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, tight_entry, tv, ev]
  · simp only [corr, pauli_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, tight_entry]
    set s : ℝ := 1 / (2 - t) with hs
    simp [tv, ev]
    rw [hs]; field_simp; ring

private lemma tight_centre (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : vlen (centre (tight t)) = t := by
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · subst h1
    have hb : vlen (blochB (tight 1)) = 1 := by rw [tight_blochB 1 le_rfl, vlen_e3]; norm_num
    rw [centre, if_pos hb, tight_blochA 1 le_rfl, vlen_e3]; norm_num
  · have h2 : (0 : ℝ) < 2 - t := by linarith
    have hblen : vlen (blochB (tight t)) = t / (2 - t) := by
      rw [tight_blochB t ht1, vlen_e3, abs_of_nonneg (div_nonneg ht0 h2.le)]
    have hb : vlen (blochB (tight t)) ≠ 1 := by
      rw [hblen]; intro h; rw [div_eq_one_iff_eq h2.ne'] at h; linarith
    obtain ⟨c0, c1, c2⟩ := tight_corr t ht1
    have h1' : (1 : ℝ) - t ≠ 0 := by linarith
    have h4 : (4 : ℝ) - t * 4 ≠ 0 := by linarith
    have hcent : centre (tight t) = ![0, 0, t] := by
      rw [centre, if_neg hb, hblen]
      funext i; fin_cases i
      · simp [Fin.sum_univ_three, tight_blochA t ht1, tight_blochB t ht1, c0]
      · simp [Fin.sum_univ_three, tight_blochA t ht1, tight_blochB t ht1, c1]
      · have hden : (1 : ℝ) - (t / (2 - t)) ^ 2 ≠ 0 := by
          rw [div_pow, one_sub_div (pow_ne_zero 2 h2.ne')]
          exact div_ne_zero (by nlinarith) (pow_ne_zero 2 h2.ne')
        have key : (t * (3 - 2 * t) / (2 - t) - (0 * 0 + 0 * 0 +
            (2 - 3 * t + 2 * t ^ 2) / (2 - t) * (t / (2 - t)))) / (1 - (t / (2 - t)) ^ 2) = t := by
          rw [div_eq_iff hden]; field_simp; ring
        simpa [Fin.sum_univ_three, tight_blochA t ht1, tight_blochB t ht1, c2] using key
    rw [hcent, vlen_e3, abs_of_nonneg ht0]

private lemma tight_phase (t : ℝ) (ht1 : t ≤ 1) :
    (star phase ⬝ᵥ (tight t *ᵥ phase)).re = 1 - t / 2 := by
  have h2' : (2 : ℝ) - t ≠ 0 := by linarith
  have e : star phase ⬝ᵥ (tight t *ᵥ phase) = (halfPhase * (starRingEnd ℂ) halfPhase) *
      (tight t (0, 0) (0, 0) + tight t (0, 0) (1, 1) + tight t (1, 1) (0, 0) +
        tight t (1, 1) (1, 1)) := by
    simp [dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, phase]; ring
  rw [e, halfPhase_mul, tight_entry, tight_entry, tight_entry, tight_entry]
  set s : ℝ := 1 / (2 - t) with hs
  simp [tv, ev]
  rw [hs]; field_simp; ring

/-- Conjecture 2 of arXiv:1404.3951 holds. -/
theorem result : claim := by
  refine ⟨fun ρ hρ htr => fef_le ρ hρ htr, fun t ht0 ht1 => ?_⟩
  have hpsd := tight_psd t ht0 ht1
  have htr := tight_trace t ht1
  have hc := tight_centre t ht0 ht1
  refine ⟨tight t, hpsd, htr, hc, le_antisymm ?_ ?_⟩
  · have := fef_le (tight t) hpsd htr; rwa [hc] at this
  · have hbdd : BddAbove {f | ∃ e, IsMaxEntangled e ∧ f = (star e ⬝ᵥ (tight t *ᵥ e)).re} :=
      ⟨1 - vlen (centre (tight t)) / 2, fun _ ⟨e, he, hf⟩ => hf ▸ maxent_le _ hpsd htr e he⟩
    rw [← tight_phase t ht1]
    exact le_csSup hbdd ⟨phase, phase_max, rfl⟩

/-- The hypotheses of `canonical_bound` are satisfiable: `1/4` is such a state. -/
example : ((((1 / 4 : ℝ) : ℂ)) • (1 : TwoQubit)).PosSemidef ∧
    partialTraceLeft ((((1 / 4 : ℝ) : ℂ)) • (1 : TwoQubit)) = (1 / 2 : ℂ) • 1 := by
  refine ⟨PosSemidef.one.smul (Complex.zero_le_real.mpr (by norm_num)), ?_⟩
  ext b d; fin_cases b <;> fin_cases d <;> simp [partialTraceLeft] <;> norm_num

/-- Two-qubit density matrices and maximally entangled vectors exist. -/
example : (∃ ρ : TwoQubit, ρ.PosSemidef ∧ trace ρ = 1) ∧ ∃ e, IsMaxEntangled e :=
  ⟨⟨tight 0, tight_psd 0 le_rfl zero_le_one, tight_trace 0 zero_le_one⟩, phase, phase_max⟩

end D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
