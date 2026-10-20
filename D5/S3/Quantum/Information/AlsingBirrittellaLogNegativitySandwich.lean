/- GID: D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Logarithmic negativity bounds for positive Hermitian amplitude ensembles. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#19208; Proved)
Direct frozen dependencies (declaration statement_id):
  D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.partialTranspose
    sha256:2373e14505428583f492752adc05d104ae8b1567265ff8182e03646de824c089
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm
    sha256:12ad034b5758446e6d628c75121b3ad5f0c80bb305937e8c9ff87e82076bc059
  D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.swap
    sha256:af00961077f2b900aa4516b8bd97fa47e80318e7fde839e758a281d3e541b1de
  D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.swapHermitian
    sha256:f54d121473ff7089d6a4e4ddb59f07c052a2b01de8dbb2be98989df6087984d7
  D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.swapSquare
    sha256:e38cf16db43e5fa807ef6b0b29d793ec6e2f3c6755db13a2496a370e78352442
  D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.replicaSwap_commutes
    sha256:4e959fbf6211116c2b2f1192bc6dcc6b24a3bbd20d41e9f98e2cae0823852cc8
  D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.Commutant.replicaSwap_apply
    sha256:e3427bb6efbbe3e9b723be03b86574ca66e788ed2d360508fdb706fa7b764080
Private proof declarations, each with proof_shape: bind-only and escape_witness: none:
  mul_swap; consumers: factorization.
  swap_selfAdjoint; consumers: trace_norm_evaluation.
  swap_square; consumers: trace_norm_evaluation.
  factorization; consumers: trace_norm_evaluation.
  positiveFactor_psd; consumers: trace_norm_evaluation.
  factor_commutes; consumers: trace_norm_evaluation.
  trace_norm_evaluation; consumers: result.
  minor_nonneg; consumers: minor_norm, mixed_pair_real.
  minor_norm; consumers: pure_value, minor_le_difference_re, mixed_pair_real.
  pure_value; consumers: trace_square_ge_one, weighted_pure_value, result.
  trace_square_ge_one; consumers: result.
  ensemble_difference; consumers: mixed_pair_bound, mixed_pair_real.
  minor_le_difference_re; consumers: mixed_pair_bound.
  mixed_pair_bound; consumers: mixed_bound.
  mixed_pair_real; consumers: mixed_real.
  mixed_bound; consumers: result.
  mixed_real; consumers: result.
  logb_jensen; consumers: result.
  weighted_pure_value; consumers: result.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19279
The amplitude vector is Function.uncurry C, definitionally the literal entry
map fun x => C x.1 x.2. The swap is the frozen conical-design swap matrix.
The published swap owner audits are unfinished under issue #19279: CHaarConcatenationNonmonotone.swapHermitian (statement_id sha256:f54d121473ff7089d6a4e4ddb59f07c052a2b01de8dbb2be98989df6087984d7), CHaarConcatenationNonmonotone.swapSquare (statement_id sha256:e38cf16db43e5fa807ef6b0b29d793ec6e2f3c6755db13a2496a370e78352442), and HaarTwoCopyTwirl.replicaSwap_commutes (statement_id sha256:4e959fbf6211116c2b2f1192bc6dcc6b24a3bbd20d41e9f98e2cae0823852cc8).
The ordered half-sums and real-amplitude transpose condition are those of #19208.
-/

import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl

/-! Binding conventions for P. M. Alsing and R. J. Birrittella, "Numerical Evidence for a Bipartite Pure State
Entanglement Witness from Approximate Analytical Diagonalization", arXiv:2404.13725v1 (Foundations 5 (2025) 19):
Equations (LogNeg:Approx:line:1–2) (the pure-state approximation), (Neg:LogNeg:Approx:rhoab) (the mixed-state ansatz),
(LN:avg:defn) and the numerically observed sandwich (mixed:state:summary:again) with its real-amplitude equality. -/

namespace D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich

open scoped ComplexOrder MatrixOrder Matrix
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)

/-- The mixed state `ρ = Σ_i p_i |ψ_i⟩⟨ψ_i|` of a pure state decomposition with amplitude matrices `C_i`. -/
noncomputable def ensembleState {d K : ℕ} (p : Fin K → ℝ) (C : Fin K → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∑ i, (p i : ℂ) • Matrix.vecMulVec (Function.uncurry (C i)) (star (Function.uncurry (C i)))

/-- The exact Log Negativity `LN_e(ρ) = log₂ ‖ρ^Γ‖₁` (partial transpose on the second subsystem). -/
noncomputable def exactLogNegativity {d : ℕ} (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  Real.logb 2 (traceNorm (partialTranspose ρ))

/-- Equation (LogNeg:Approx:line:1): `N_a(|ψ⟩) = ½ Σ_n Σ_{m≠n} |det [[c_nn, c_nm], [c_mn, c_mm]]|`. -/
noncomputable def pureApproxNegativity {d : ℕ} (C : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (1 / 2) * ∑ n, ∑ m, if m = n then 0 else ‖C n n * C m m - C n m * C m n‖

/-- Equation (LogNeg:Approx:line:2): `LN_a(|ψ⟩) = log₂(1 + 2 N_a)`. -/
noncomputable def pureApproxLogNegativity {d : ℕ} (C : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.logb 2 (1 + 2 * pureApproxNegativity C)

/-- Equation (Neg:LogNeg:Approx:rhoab:line:2): `N_a(ρ) = ½ Σ_{n, m≠n} |ρ_{nn,mm} − ρ_{nm,mn}|`. -/
noncomputable def mixedApproxNegativity {d : ℕ} (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  (1 / 2) * ∑ n, ∑ m, if m = n then 0 else ‖ρ (n, n) (m, m) - ρ (n, m) (m, n)‖

/-- Equation (Neg:LogNeg:Approx:rhoab:line:3): `LN_a(ρ) = log₂(1 + 2 N_a(ρ))`. -/
noncomputable def mixedApproxLogNegativity {d : ℕ} (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  Real.logb 2 (1 + 2 * mixedApproxNegativity ρ)

/-- Equation (mixed:state:summary:again), "we have numerically found that 𝓛𝓝_a^avg(ρ) ≤ LN_e(ρ) ≤ LN_a(ρ)" for pure
state decompositions with positive Hermitian amplitude matrices `C_i = C_i† ≥ 0`, "Further, … the second inequality is
surprisingly saturated … if the … C_i matrices above are real, i.e. C_i = C_i^T". -/
def claim : Prop :=
  ∀ (d K : ℕ) (p : Fin K → ℝ) (C : Fin K → Matrix (Fin d) (Fin d) ℂ),
    (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
    (∀ i, (C i).PosSemidef ∧ (C i * (C i)ᴴ).trace = 1) →
      (∑ i, p i * pureApproxLogNegativity (C i) ≤ exactLogNegativity (ensembleState p C) ∧
        exactLogNegativity (ensembleState p C) ≤ mixedApproxLogNegativity (ensembleState p C)) ∧
      ((∀ i, (C i)ᵀ = C i) →
        exactLogNegativity (ensembleState p C) = mixedApproxLogNegativity (ensembleState p C))

end D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich
open scoped Kronecker
open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)

private noncomputable def positiveFactor {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ) :=
  ∑ i, (p i : ℂ) • (C i ⊗ₖ C i)

private theorem mul_swap {d : ℕ} (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (x y) :
    (A * D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d) x y = A x y.swap := by
  classical
  change (A * (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ).submatrix
    (Equiv.refl _) Prod.swap) x y = _
  rw [Matrix.mul_submatrix_one]
  rfl

private theorem swap_selfAdjoint (d : ℕ) : (D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d)ᴴ = D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d := by
  classical
  have hS : D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d =
      Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) := by
    ext r c
    rw [D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Commutant.replicaSwap_apply]
    simp [D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap,
      Matrix.one_apply, Prod.ext_iff, and_comm, eq_comm]
  rw [hS]
  exact D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone.swapHermitian (n := Fin d)

private theorem swap_square (d : ℕ) : D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d * D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d = 1 := by
  classical
  have hS : D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d =
      Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) := by
    ext r c
    rw [D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Commutant.replicaSwap_apply]
    simp [D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap,
      Matrix.one_apply, Prod.ext_iff, and_comm, eq_comm]
  rw [hS]
  exact D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone.swapSquare (n := Fin d)

private theorem factorization {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ)
    (hC : ∀ i, (C i).IsHermitian) :
    partialTranspose (ensembleState p C) = positiveFactor p C * D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d := by
  ext ⟨a,b⟩ ⟨c,e⟩
  rw [mul_swap]
  simp only [partialTranspose, ensembleState, positiveFactor, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Function.uncurry,
    Pi.star_apply, Matrix.kroneckerMap_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change (p i : ℂ) * (C i a e * star (C i c b)) =
    (p i : ℂ) * (C i a e * C i b c)
  rw [(hC i).apply b c]

private theorem positiveFactor_psd {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hC : ∀ i, (C i).PosSemidef) :
    (positiveFactor p C).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i hi
  exact ((hC i).kronecker (hC i)).smul (show (0 : ℂ) ≤ p i by exact_mod_cast hp i)

private theorem factor_commutes {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ) :
    positiveFactor p C * D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d = D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d * positiveFactor p C := by
  classical
  have hS : D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d =
      Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) := by
    ext r c
    rw [D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Commutant.replicaSwap_apply]
    simp [D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap,
      Matrix.one_apply, Prod.ext_iff, and_comm, eq_comm]
  unfold positiveFactor
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.smul_mul, Matrix.mul_smul, hS]
  exact congrArg (fun A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ => (p i : ℂ) • A)
    (D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.replicaSwap_commutes (C i)).symm

private theorem trace_norm_evaluation {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hC : ∀ i, (C i).PosSemidef) :
    traceNorm (partialTranspose (ensembleState p C)) =
      ∑ i, p i * ((C i).trace.re)^2 := by
  have hQ := positiveFactor_psd p C hp hC
  have hfac := factorization p C (fun i => (hC i).1)
  have hcom := factor_commutes p C
  have hs : positiveFactor p C * positiveFactor p C =
      (partialTranspose (ensembleState p C))ᴴ * partialTranspose (ensembleState p C) := by
    rw [hfac, Matrix.conjTranspose_mul, swap_selfAdjoint, hQ.1.eq]
    have hc : Commute (positiveFactor p C) (D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.swap d) := hcom
    rw [← hc.eq, hc.symm.mul_mul_mul_comm, swap_square, Matrix.mul_one]
  have hroot := CFC.sqrt_unique hs hQ.nonneg
  change (CFC.sqrt ((partialTranspose (ensembleState p C))ᴴ *
    partialTranspose (ensembleState p C))).trace.re = _
  rw [hroot]
  simp only [positiveFactor, Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_kronecker,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have him : ((C i).trace).im = 0 := (hC i).trace_nonneg.2.symm
  simp [Complex.mul_re, him, pow_two]

end D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich

namespace D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich
open Matrix
open scoped ComplexOrder MatrixOrder

private theorem minor_nonneg {d : ℕ} {C : Matrix (Fin d) (Fin d) ℂ}
    (hC : C.PosSemidef) (n m : Fin d) :
    0 ≤ C n n * C m m - C n m * C m n := by
  have hd := (hC.submatrix ![n,m]).det_nonneg
  simpa only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using hd

private theorem minor_norm {d : ℕ} {C : Matrix (Fin d) (Fin d) ℂ}
    (hC : C.PosSemidef) (n m : Fin d) :
    ‖C n n * C m m - C n m * C m n‖ =
      (C n n * C m m - C n m * C m n).re := by
  exact congrArg Complex.re (Complex.norm_of_nonneg' (minor_nonneg hC n m))

private theorem pure_value {d : ℕ} {C : Matrix (Fin d) (Fin d) ℂ}
    (hC : C.PosSemidef) (hn : (C * Cᴴ).trace = 1) :
    1 + 2 * pureApproxNegativity C = C.trace.re ^ 2 := by
  have hs : (∑ n, ∑ m, if m = n then 0 else
      ‖C n n * C m m - C n m * C m n‖) =
      (C.trace * C.trace - (C * C).trace).re := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    by_cases h : m = n
    · subst m; simp
    · simp only [h, ↓reduceIte]
      rw [minor_norm hC n m]
      congr 1
      ring
  have htrace : (C.trace : ℂ).im = 0 := hC.trace_nonneg.2.symm
  have hnorm : (C * C).trace = 1 := by simpa only [hC.1.eq] using hn
  rw [pureApproxNegativity, hs]
  simp only [Complex.sub_re, Complex.mul_re, htrace, hnorm, Complex.one_re]
  ring

private theorem trace_square_ge_one {d : ℕ} {C : Matrix (Fin d) (Fin d) ℂ}
    (hC : C.PosSemidef) (hn : (C * Cᴴ).trace = 1) :
    1 ≤ C.trace.re ^ 2 := by
  rw [← pure_value hC hn]
  have h : 0 ≤ pureApproxNegativity C := by
    unfold pureApproxNegativity
    positivity
  linarith

end D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich

namespace D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich
open Matrix
open scoped ComplexOrder MatrixOrder

private theorem ensemble_difference {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ)
    (hC : ∀ i, (C i).IsHermitian) (n m : Fin d) :
    ensembleState p C (n,n) (m,m) - ensembleState p C (n,m) (m,n) =
      ∑ i, (p i : ℂ) * (C i n n * C i m m - C i n m * C i n m) := by
  simp only [ensembleState, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply, Function.uncurry, Pi.star_apply,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(hC i).apply m m, (hC i).apply n m]
  ring

private theorem minor_le_difference_re {d : ℕ} {C : Matrix (Fin d) (Fin d) ℂ}
    (hC : C.PosSemidef) (n m : Fin d) :
    ‖C n n * C m m - C n m * C m n‖ ≤
      (C n n * C m m - C n m * C n m).re := by
  rw [minor_norm hC, ← hC.1.apply m n]
  simp only [Complex.sub_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (C n m).im]

private theorem mixed_pair_bound {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hC : ∀ i, (C i).PosSemidef) (n m : Fin d) :
    (∑ i, p i * ‖C i n n * C i m m - C i n m * C i m n‖) ≤
      ‖ensembleState p C (n,n) (m,m) - ensembleState p C (n,m) (m,n)‖ := by
  calc
    _ ≤ ∑ i, p i * (C i n n * C i m m - C i n m * C i n m).re := by
      exact Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (minor_le_difference_re (hC i) n m) (hp i))
    _ = (ensembleState p C (n,n) (m,m) - ensembleState p C (n,m) (m,n)).re := by
      rw [ensemble_difference p C (fun i => (hC i).1)]
      simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    _ ≤ _ := Complex.re_le_norm _

private theorem mixed_pair_real {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hC : ∀ i, (C i).PosSemidef)
    (hr : ∀ i, (C i)ᵀ = C i) (n m : Fin d) :
    ‖ensembleState p C (n,n) (m,m) - ensembleState p C (n,m) (m,n)‖ =
      ∑ i, p i * ‖C i n n * C i m m - C i n m * C i m n‖ := by
  have he (i : Fin K) : C i n m = C i m n := by
    exact congrArg (fun A => A m n) (hr i)
  have hs : ensembleState p C (n,n) (m,m) - ensembleState p C (n,m) (m,n) =
      ∑ i, (p i : ℂ) * (C i n n * C i m m - C i n m * C i m n) := by
    rw [ensemble_difference p C (fun i => (hC i).1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i]
  have hn : 0 ≤ ensembleState p C (n,n) (m,m) - ensembleState p C (n,m) (m,n) := by
    rw [hs]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (by exact_mod_cast hp i) (minor_nonneg (hC i) n m)
  have hn' : ‖ensembleState p C (n,n) (m,m) - ensembleState p C (n,m) (m,n)‖ =
      (ensembleState p C (n,n) (m,m) - ensembleState p C (n,m) (m,n)).re :=
    congrArg Complex.re (Complex.norm_of_nonneg' hn)
  rw [hn', hs]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [minor_norm (hC i)]

private theorem mixed_bound {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hC : ∀ i, (C i).PosSemidef) :
    ∑ i, p i * pureApproxNegativity (C i) ≤ mixedApproxNegativity (ensembleState p C) := by
  have hs : (∑ i, p i * pureApproxNegativity (C i)) =
      (1/2) * ∑ n, ∑ m, if m = n then 0 else
        ∑ i, p i * ‖C i n n * C i m m - C i n m * C i m n‖ := by
    simp only [pureApproxNegativity, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    split_ifs <;> simp [Finset.mul_sum, mul_assoc, mul_left_comm]
  rw [hs, mixedApproxNegativity]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro m hm
  split_ifs
  · rfl
  · exact mixed_pair_bound p C hp hC n m

private theorem mixed_real {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hC : ∀ i, (C i).PosSemidef)
    (hr : ∀ i, (C i)ᵀ = C i) :
    mixedApproxNegativity (ensembleState p C) = ∑ i, p i * pureApproxNegativity (C i) := by
  symm
  unfold mixedApproxNegativity pureApproxNegativity
  simp_rw [mixed_pair_real p C hp hC hr]
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  split_ifs <;> simp [Finset.mul_sum, mul_assoc, mul_left_comm]

end D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich

namespace D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich
open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

private theorem logb_jensen {K : ℕ} (p t : Fin K → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ht : ∀ i, 0 < t i) :
    ∑ i, p i * Real.logb 2 (t i) ≤ Real.logb 2 (∑ i, p i * t i) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (w := p) (p := t) (fun i hi => hp i) hsum
    (fun i hi => ht i)
  simp only [smul_eq_mul] at h
  simpa only [Real.logb, mul_div_assoc, Finset.sum_div] using
    (div_le_div_of_nonneg_right h (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))

private theorem weighted_pure_value {d K : ℕ} (p : Fin K → ℝ)
    (C : Fin K → Matrix (Fin d) (Fin d) ℂ)
    (hsum : ∑ i, p i = 1)
    (hC : ∀ i, (C i).PosSemidef ∧ (C i * (C i)ᴴ).trace = 1) :
    1 + 2 * (∑ i, p i * pureApproxNegativity (C i)) =
      ∑ i, p i * (C i).trace.re ^ 2 := by
  calc
    _ = ∑ i, (p i + 2 * (p i * pureApproxNegativity (C i))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    _ = ∑ i, p i * (1 + 2 * pureApproxNegativity (C i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := Finset.sum_congr rfl (fun i hi => by rw [pure_value (hC i).1 (hC i).2])

theorem result : D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich.claim := by
  intro d K p C hp hsum hC
  have hnorm := trace_norm_evaluation p C hp (fun i => (hC i).1)
  have hval := weighted_pure_value p C hsum hC
  have hT : 0 < ∑ i, p i * (C i).trace.re ^ 2 := by
    have hge : 1 ≤ ∑ i, p i * (C i).trace.re ^ 2 := by
      calc
        1 = ∑ i, p i * 1 := by simpa using hsum.symm
        _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
          (trace_square_ge_one (hC i).1 (hC i).2) (hp i))
    exact lt_of_lt_of_le zero_lt_one hge
  have he : exactLogNegativity (ensembleState p C) =
      Real.logb 2 (∑ i, p i * (C i).trace.re ^ 2) :=
    congrArg (Real.logb 2) hnorm
  constructor
  · constructor
    · rw [he]
      have hpure (i : Fin K) : pureApproxLogNegativity (C i) =
          Real.logb 2 ((C i).trace.re ^ 2) := by
        exact congrArg (Real.logb 2) (pure_value (hC i).1 (hC i).2)
      simp_rw [hpure]
      exact logb_jensen p _ hp hsum (fun i => lt_of_lt_of_le (by norm_num)
        (trace_square_ge_one (hC i).1 (hC i).2))
    · rw [he, mixedApproxLogNegativity]
      apply Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hT
      rw [← hval]
      linarith [mixed_bound p C hp (fun i => (hC i).1)]
  · intro hr
    rw [he, mixedApproxLogNegativity, mixed_real p C hp (fun i => (hC i).1) hr, hval]

end D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich
