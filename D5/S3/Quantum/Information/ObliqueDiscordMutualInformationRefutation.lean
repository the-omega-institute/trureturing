/- GID: D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.claim; result=D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.result; claim=D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.claim
   digest: A normalized oblique operation increases the mutual information of two qubits. -/

/-
proof_shape: result: bind-only (explicit rational matrix certificates, upstream spectral
  identities and logarithmic monotonicity, followed by finite and algebraic normalization)
escape_witness: none
admission_basis: open-problem-resolution (#11784; Refuted)
Registration is paused under CLAUDE.md §3.9 (information-escape registration pause).
Direct frozen dependencies:
  D5/S3/Quantum/Information/PartialTraceMutualInformation.spectral_sum_eq_of_charpoly_prod,
  D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalLeft,
  D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalRight,
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft,
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight,
  D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation;
  module statement_id: sha256:a9412bc39f47c48d0206a946c9781d89d5e3a19963de2c334eda8ba43e136130
  D5/S3/Quantum/Information/InputInformationBalance.entropy_eq_sum;
  D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.vonNeumannEntropy;
  D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState
-/

import D5.S3.Quantum.Information.InputInformationBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section

namespace D5.S3.Quantum.Information.ObliqueDiscordMutualInformationRefutation

open scoped Classical

open Matrix Polynomial
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- A normalized possibly oblique basis with its biorthogonal dual. -/
structure ObliqueBasis (n : ℕ) where
  v : Module.Basis (Fin n) ℂ (Fin n → ℂ)
  w : Module.Basis (Fin n) ℂ (Fin n → ℂ)
  normalized : ∀ i, star (v i) ⬝ᵥ v i = 1
  dual : ∀ i j, star (v i) ⬝ᵥ w j = if i = j then 1 else 0

def kraus {n : ℕ} (b : ObliqueBasis n) (i : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec (b.v i) (star (b.w i))

def rawOblique {nA nB : ℕ} (b : ObliqueBasis nA)
    (rho : Matrix (Fin nA × Fin nB) (Fin nA × Fin nB) ℂ) :
    Matrix (Fin nA × Fin nB) (Fin nA × Fin nB) ℂ :=
  ∑ i, (kraus b i ⊗ₖ (1 : Matrix (Fin nB) (Fin nB) ℂ)) * rho *
    (kraus b i ⊗ₖ (1 : Matrix (Fin nB) (Fin nB) ℂ))ᴴ

/-- The source denominator: trace over B of the sum of dual-vector sandwiches. -/
noncomputable def normalizer {nA nB : ℕ} (b : ObliqueBasis nA)
    (rho : Matrix (Fin nA × Fin nB) (Fin nA × Fin nB) ℂ) : ℝ :=
  (partialTraceRight (∑ i,
    (Matrix.replicateRow Unit (star (b.w i)) ⊗ₖ (1 : Matrix (Fin nB) (Fin nB) ℂ)) * rho *
      (Matrix.replicateRow Unit (star (b.w i)) ⊗ₖ
        (1 : Matrix (Fin nB) (Fin nB) ℂ))ᴴ) () ()).re

/-- Eq. (13), normalized by its source denominator. -/
noncomputable def phi {nA nB : ℕ} (b : ObliqueBasis nA)
    (rho : DensityState (Fin nA × Fin nB))
    (ht : 0 < normalizer b (CStarMatrix.ofMatrix.symm rho.1)) :
    DensityState (Fin nA × Fin nB) := by
  let T := rawOblique b (CStarMatrix.ofMatrix.symm rho.1)
  have hp : T.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ =>
      (Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)).mul_mul_conjTranspose_same _
  have hnormal : normalizer b (CStarMatrix.ofMatrix.symm rho.1) = (Matrix.trace T).re := by
    have hweight (i : Fin nA) :
        (kraus b i)ᴴ * kraus b i =
          ((Matrix.replicateRow Unit (star (b.w i)))ᴴ *
            Matrix.replicateRow Unit (star (b.w i)) :
              Matrix (Fin nA) (Fin nA) ℂ) := by
      ext a c
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, kraus,
        Matrix.vecMulVec_apply, Matrix.replicateRow_apply, Pi.star_apply, star_mul, star_star]
      have hn := b.normalized i
      simp only [dotProduct, Pi.star_apply] at hn
      simp only [Fintype.sum_unique]
      calc
        _ = b.w i a * (∑ x, star (b.v i x) * b.v i x) * star (b.w i c) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = _ := by rw [hn]; ring
    have htrace : Matrix.trace T =
        partialTraceRight (∑ i,
          (Matrix.replicateRow Unit (star (b.w i)) ⊗ₖ
            (1 : Matrix (Fin nB) (Fin nB) ℂ)) * CStarMatrix.ofMatrix.symm rho.1 *
          (Matrix.replicateRow Unit (star (b.w i)) ⊗ₖ
            (1 : Matrix (Fin nB) (Fin nB) ℂ))ᴴ) () () := by
      have hunit (M : Matrix (Unit × Fin nB) (Unit × Fin nB) ℂ) :
          partialTraceRight M () () = Matrix.trace M := by
        simp [Matrix.trace, partialTraceRight, Fintype.sum_prod_type]
      rw [hunit]
      change Matrix.trace (rawOblique b (CStarMatrix.ofMatrix.symm rho.1)) = _
      rw [rawOblique, Matrix.trace_sum, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => rw [Matrix.trace_mul_cycle]
      conv_rhs => rw [Matrix.trace_mul_cycle]
      simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, hweight]
    exact congrArg Complex.re htrace.symm
  refine ⟨CStarMatrix.ofMatrix ((normalizer b (CStarMatrix.ofMatrix.symm rho.1))⁻¹ • T), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (hp.smul (inv_nonneg.mpr ht.le)).nonneg
  · change Matrix.trace ((normalizer b (CStarMatrix.ofMatrix.symm rho.1))⁻¹ • T) = 1
    rw [hnormal] at ht
    rw [hnormal]
    have hre : Matrix.trace T = ((Matrix.trace T).re : ℂ) := by
      rw [hp.isHermitian.trace_eq_sum_eigenvalues]
      simp
    rw [Matrix.trace_smul, hre, Complex.ofReal_re, Complex.real_smul, ← Complex.ofReal_mul]
    rw [inv_mul_cancel₀ ht.ne', Complex.ofReal_one]

def claim : Prop :=
  ∀ nA nB : ℕ, ∀ b : ObliqueBasis nA,
    ∀ rho : DensityState (Fin nA × Fin nB),
    ∀ ht : 0 < normalizer b (CStarMatrix.ofMatrix.symm rho.1),
    quantumMutualInformation (phi b rho ht) ≤ quantumMutualInformation rho

private abbrev Pair := Fin 2 × Fin 2

private def rhoQ : Matrix Pair Pair ℚ := Matrix.submatrix
  (fun i j => (![![64, 0, 0, 8], ![0, 0, 0, 0], ![0, 0, 0, 0], ![8, 0, 0, 1]] : Matrix (Fin 4) (Fin 4) ℚ) i j / 65) finProdFinEquiv finProdFinEquiv

private def tauQ : Matrix Pair Pair ℚ := Matrix.submatrix
  (fun i j => (![![64, 0, 0, 8], ![0, 4, 8, 0], ![0, 8, 16, 0], ![8, 0, 0, 1]] : Matrix (Fin 4) (Fin 4) ℚ) i j / 85) finProdFinEquiv finProdFinEquiv

private def Pq : Matrix Pair Pair ℚ := Matrix.submatrix
  ![![8, 0, 0, 1], ![0, 1, 2, 0], ![0, 2, -1, 0], ![1, 0, 0, -8]] finProdFinEquiv finProdFinEquiv

private def Qq : Matrix Pair Pair ℚ := Matrix.submatrix
  ![![8/65, 0, 0, 1/65], ![0, 1/5, 2/5, 0], ![0, 2/5, -1/5, 0], ![1/65, 0, 0, -8/65]] finProdFinEquiv finProdFinEquiv

private def rhoEig : Pair → ℚ := fun z => (![1,0,0,0] : Fin 4 → ℚ) (finProdFinEquiv z)

private def tauEig : Pair → ℚ := fun z => (![13/17,4/17,0,0] : Fin 4 → ℚ) (finProdFinEquiv z)

private noncomputable def V : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ((![![2,1],![2,-1]] : Matrix (Fin 2) (Fin 2) ℂ) i j) / (Real.sqrt 5 : ℂ)

private noncomputable def W : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (Real.sqrt 5 : ℂ) *
    ((![![1/4,1/2],![1/4,-1/2]] : Matrix (Fin 2) (Fin 2) ℂ) i j)

/-- Xu's conjecture fails at the explicit two-qubit witness. -/
theorem result : ¬ claim := by
  intro hc
  have rho_psd : (rhoQ.map (Rat.castHom ℂ)).PosSemidef := by
    let u : Pair → ℂ := fun z => (![8,0,0,1] : Fin 4 → ℂ) (finProdFinEquiv z)
    have he : rhoQ.map (Rat.castHom ℂ) = (1 / 65 : ℝ) • vecMulVec u (star u) := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [rhoQ, Matrix.submatrix, finProdFinEquiv, u,
        vecMulVec_apply, Pi.star_apply, Matrix.smul_apply]
    rw [he]
    exact (posSemidef_vecMulVec_self_star u).smul (by norm_num)

  have tau_psd : (tauQ.map (Rat.castHom ℂ)).PosSemidef := by
    let u : Pair → ℂ := fun z => (![8,0,0,1] : Fin 4 → ℂ) (finProdFinEquiv z)
    let v : Pair → ℂ := fun z => (![0,2,4,0] : Fin 4 → ℂ) (finProdFinEquiv z)
    have he : tauQ.map (Rat.castHom ℂ) = (1 / 85 : ℝ) •
        (vecMulVec u (star u) + vecMulVec v (star v)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [tauQ, Matrix.submatrix, finProdFinEquiv, u, v,
        vecMulVec_apply, Pi.star_apply, Matrix.smul_apply]
    rw [he]
    exact ((posSemidef_vecMulVec_self_star u).add
      (posSemidef_vecMulVec_self_star v)).smul (by norm_num)

  let rho : DensityState Pair :=
    ⟨CStarMatrix.ofMatrix (rhoQ.map (Rat.castHom ℂ)),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv rho_psd.nonneg, by
        change Matrix.trace (rhoQ.map (Rat.castHom ℂ)) = 1
        norm_num [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, rhoQ, Matrix.submatrix, finProdFinEquiv, Matrix.smul_apply]⟩

  let tau : DensityState Pair :=
    ⟨CStarMatrix.ofMatrix (tauQ.map (Rat.castHom ℂ)),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv tau_psd.nonneg, by
        change Matrix.trace (tauQ.map (Rat.castHom ℂ)) = 1
        norm_num [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, tauQ, Matrix.submatrix, finProdFinEquiv, Matrix.smul_apply]⟩

  have hPQ : Pq * Qq = 1 := by decide +kernel

  have rho_charpoly : (rhoQ.map (Rat.castHom ℂ)).charpoly =
      ∏ z, (X - C ((rhoEig z : ℚ) : ℂ)) := by
    have hRP : rhoQ * Pq = Pq * diagonal rhoEig := by decide +kernel
    have he : rhoQ = Pq * (diagonal rhoEig * Qq) := by
      rw [← Matrix.mul_assoc, ← hRP, Matrix.mul_assoc _ Pq Qq, hPQ, Matrix.mul_one]
    have hc : rhoQ.charpoly = ∏ z, (X - C (rhoEig z)) := by
      rw [he, Matrix.charpoly_mul_comm, Matrix.mul_assoc, mul_eq_one_comm.mp hPQ,
        Matrix.mul_one, Matrix.charpoly_diagonal]
    rw [Matrix.charpoly_map, hc, Polynomial.map_prod]
    simp

  have tau_charpoly : (tauQ.map (Rat.castHom ℂ)).charpoly =
      ∏ z, (X - C ((tauEig z : ℚ) : ℂ)) := by
    have hTP : tauQ * Pq = Pq * diagonal tauEig := by decide +kernel
    have he : tauQ = Pq * (diagonal tauEig * Qq) := by
      rw [← Matrix.mul_assoc, ← hTP, Matrix.mul_assoc _ Pq Qq, hPQ, Matrix.mul_one]
    have hc : tauQ.charpoly = ∏ z, (X - C (tauEig z)) := by
      rw [he, Matrix.charpoly_mul_comm, Matrix.mul_assoc, mul_eq_one_comm.mp hPQ,
        Matrix.mul_one, Matrix.charpoly_diagonal]
    rw [Matrix.charpoly_map, hc, Polynomial.map_prod]
    simp

  have entropy_rho : vonNeumannEntropy rho = 0 := by
    rw [D5.S3.Quantum.Information.InputInformationBalance.entropy_eq_sum]
    change ∑ i, Real.negMulLog (rho_psd.isHermitian.eigenvalues i) = _
    rw [spectral_sum_eq_of_charpoly_prod rho_psd.isHermitian (fun z => (rhoEig z : ℝ))
        Real.negMulLog (by simpa [rho] using rho_charpoly)]
    norm_num [rhoEig, finProdFinEquiv, Fintype.sum_prod_type, Fin.sum_univ_two]

  have tau_spectrum :
      Multiset.map tau_psd.isHermitian.eigenvalues Finset.univ.val =
        Multiset.map (fun z => (tauEig z : ℝ)) Finset.univ.val := by
    have hroots : (tauQ.map (Rat.castHom ℂ)).charpoly.roots =
        Multiset.map (fun z => (tauEig z : ℂ)) Finset.univ.val := by
      rw [tau_charpoly, Polynomial.roots_prod _ _ (by
        simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
      simp
    have he := tau_psd.isHermitian.roots_charpoly_eq_eigenvalues.symm.trans hroots
    have hre := congrArg (Multiset.map Complex.re) he
    simpa [Function.comp_def] using hre

  have entropy_tau : vonNeumannEntropy tau =
      Real.negMulLog (13/17) + Real.negMulLog (4/17) := by
    rw [D5.S3.Quantum.Information.InputInformationBalance.entropy_eq_sum]
    change ∑ i, Real.negMulLog (tau_psd.isHermitian.eigenvalues i) = _
    have hs := congrArg (fun ms : Multiset ℝ => (ms.map Real.negMulLog).sum) tau_spectrum
    have hs' : (∑ i, Real.negMulLog (tau_psd.isHermitian.eigenvalues i)) =
        ∑ z, Real.negMulLog (tauEig z : ℝ) := by
      simpa only [Finset.sum, Multiset.map_map, Function.comp_def] using hs
    rw [hs']
    norm_num [tauEig, finProdFinEquiv, Fintype.sum_prod_type, Fin.sum_univ_two]

  have entropy_diagonal {n : Type} [Fintype n] [DecidableEq n]
      (sigma : DensityState n) (d : n → ℝ)
      (he : CStarMatrix.ofMatrix.symm sigma.1 = diagonal (fun i => (d i : ℂ))) :
      vonNeumannEntropy sigma = ∑ i, Real.negMulLog (d i) := by
    rw [D5.S3.Quantum.Information.InputInformationBalance.entropy_eq_sum]
    apply spectral_sum_eq_of_charpoly_prod
    change (CStarMatrix.ofMatrix.symm sigma.1).charpoly = _
    rw [he, Matrix.charpoly_diagonal]
    simp

  have marginal_rho_A : CStarMatrix.ofMatrix.symm (marginalRight rho).1 =
      diagonal (fun i : Fin 2 => ((![64/65, 1/65] : Fin 2 → ℝ) i : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [marginalRight, partialTraceRight, rho, rhoQ, Matrix.submatrix, finProdFinEquiv,
        Fin.sum_univ_two, diagonal_apply]

  have marginal_rho_B : CStarMatrix.ofMatrix.symm (marginalLeft rho).1 =
      diagonal (fun i : Fin 2 => ((![64/65, 1/65] : Fin 2 → ℝ) i : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [marginalLeft, partialTraceLeft, rho, rhoQ, Matrix.submatrix, finProdFinEquiv,
        Fin.sum_univ_two, diagonal_apply]

  have marginal_tau_A : CStarMatrix.ofMatrix.symm (marginalRight tau).1 =
      diagonal (fun i : Fin 2 => ((![4/5, 1/5] : Fin 2 → ℝ) i : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [marginalRight, partialTraceRight, tau, tauQ, Matrix.submatrix, finProdFinEquiv,
        Fin.sum_univ_two, diagonal_apply]

  have marginal_tau_B : CStarMatrix.ofMatrix.symm (marginalLeft tau).1 =
      diagonal (fun i : Fin 2 => ((![16/17, 1/17] : Fin 2 → ℝ) i : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [marginalLeft, partialTraceLeft, tau, tauQ, Matrix.submatrix, finProdFinEquiv,
        Fin.sum_univ_two, diagonal_apply]

  have VW : V * Wᴴ = 1 := by
    have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [V, W, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.one_apply, Complex.star_def, Complex.conj_ofReal, map_ofNat]
    all_goals field_simp
    all_goals norm_num
    all_goals ring

  have WV : W * Vᴴ = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] using congrArg Matrix.conjTranspose VW

  let basisWitness : ObliqueBasis 2 := {
    v := basisOfPiSpaceOfLinearIndependent
      (Matrix.linearIndependent_rows_of_isUnit (isUnit_iff_exists_inv.mpr ⟨Wᴴ, VW⟩))
    w := basisOfPiSpaceOfLinearIndependent
      (Matrix.linearIndependent_rows_of_isUnit (isUnit_iff_exists_inv.mpr ⟨Vᴴ, WV⟩))
    normalized := by
      have hs : (Real.sqrt 5 : ℂ)^2 = 5 := by
        exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      intro i
      simp only [coe_basisOfPiSpaceOfLinearIndependent]
      fin_cases i <;>
        norm_num [V, Matrix.row, dotProduct, Pi.star_apply, Fin.sum_univ_two,
          Complex.star_def, Complex.conj_ofReal, map_ofNat]
      all_goals
        have hn : (Real.sqrt 5 : ℂ) ≠ 0 := by
          exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
        field_simp
        linear_combination -hs
    dual := by
      intro i j
      simp only [coe_basisOfPiSpaceOfLinearIndependent]
      have hh := congrFun (congrFun WV j) i
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hh
      simpa only [Matrix.row, dotProduct, Pi.star_apply, mul_comm, eq_comm] using hh
  }

  have witnessK (i : Fin 2) : kraus basisWitness i =
      (if i = 0 then ![![1/2,1],![1/4,1/2]] else
        ![![1/2,-1],![-1/4,1/2]] : Matrix (Fin 2) (Fin 2) ℂ) := by
    have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
    have hv : ⇑basisWitness.v = V.row := coe_basisOfPiSpaceOfLinearIndependent _
    have hw : ⇑basisWitness.w = W.row := coe_basisOfPiSpaceOfLinearIndependent _
    simp only [kraus, hv, hw]
    ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [V, W, Matrix.row, Matrix.vecMulVec_apply,
        Pi.star_apply, Complex.star_def, Complex.conj_ofReal, map_ofNat]
    all_goals field_simp
    all_goals norm_num
    all_goals ring

  have raw_witness : rawOblique basisWitness (CStarMatrix.ofMatrix.symm rho.1) =
      (17/26 : ℝ) • (CStarMatrix.ofMatrix.symm tau.1) := by
    have hK0 : kraus basisWitness 0 = (![![1/2,1],![1/4,1/2]] : Matrix (Fin 2) (Fin 2) ℂ) := by
      simpa using witnessK 0
    have hK1 : kraus basisWitness 1 = (![![1/2,-1],![-1/4,1/2]] : Matrix (Fin 2) (Fin 2) ℂ) := by
      simpa using witnessK 1
    ext i j
    simp only [rawOblique, Fin.sum_univ_two, hK0, hK1]
    fin_cases i <;> fin_cases j <;>
      norm_num [rho, tau, rhoQ, tauQ, Matrix.submatrix, finProdFinEquiv,
        Fin.sum_univ_two, Fintype.sum_prod_type, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.smul_apply, Matrix.one_apply, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, map_ofNat]

  have entropy_inequality : 2*Real.binEntropy (1/65) < Real.binEntropy (1/5) + Real.binEntropy (1/17) - Real.binEntropy (4/17) := by
    have h5 : (5 : ℝ)^3 < 2^7 := by norm_num
    have h13 : (13 : ℝ)^17 < 2^63 := by norm_num
    have hl5 := Real.log_lt_log (by positivity : (0 : ℝ) < 5^3) h5
    have hl13 := Real.log_lt_log (by positivity : (0 : ℝ) < 13^17) h13
    rw [Real.log_pow, Real.log_pow] at hl5 hl13
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    norm_num at hl5 hl13
    have hl : 1105 * Real.log 5 + 1365 * Real.log 13 < 7648 * Real.log 2 := by
      linarith only [hl5, hl13, hl2]
    have l65 : Real.log (65 : ℝ) = Real.log 5 + Real.log 13 := by
      rw [show (65 : ℝ) = 5*13 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have l64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
    have l16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
    have l4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    norm_num [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog]
    rw [Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num)]
    simp only [Real.log_one, l65, l64, l16, l4]
    norm_num at hl ⊢
    linarith only [hl]

  have mi_rho : quantumMutualInformation rho = 2*Real.binEntropy (1/65) := by
    rw [quantumMutualInformation, entropy_diagonal _ _ marginal_rho_A,
      entropy_diagonal _ _ marginal_rho_B, entropy_rho]
    norm_num [Fin.sum_univ_two, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    ring

  have mi_tau : quantumMutualInformation tau = Real.binEntropy (1/5) + Real.binEntropy (1/17) - Real.binEntropy (4/17) := by
    rw [quantumMutualInformation, entropy_diagonal _ _ marginal_tau_A,
      entropy_diagonal _ _ marginal_tau_B, entropy_tau]
    norm_num [Fin.sum_univ_two, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    ring

  have hnormal : normalizer basisWitness (CStarMatrix.ofMatrix.symm rho.1) =
      (Matrix.trace (rawOblique basisWitness (CStarMatrix.ofMatrix.symm rho.1))).re := by
    have hw : ⇑basisWitness.w = W.row := coe_basisOfPiSpaceOfLinearIndependent _
    have hs : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hn : normalizer basisWitness (CStarMatrix.ofMatrix.symm rho.1) = 17/26 := by
      change normalizer basisWitness (rhoQ.map (Rat.castHom ℂ)) = _
      simp only [normalizer, hw]
      norm_num [partialTraceRight, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Matrix.one_apply, Matrix.replicateRow_apply, Pi.star_apply, W, Matrix.row, rhoQ, Matrix.submatrix,
        finProdFinEquiv, Complex.star_def, Complex.conj_ofReal, map_ofNat]
      norm_num [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
      nlinarith [hs]
    rw [hn, raw_witness, Matrix.trace_smul]
    change _ = ((17/26 : ℝ) • Matrix.trace (tauQ.map (Rat.castHom ℂ))).re
    rw [show Matrix.trace (tauQ.map (Rat.castHom ℂ)) = 1 from tau.2.2]
    norm_num

  have ht : (Matrix.trace (rawOblique basisWitness (CStarMatrix.ofMatrix.symm rho.1))).re =
      17/26 := by
    rw [raw_witness, Matrix.trace_smul]
    change ((17/26 : ℝ) • Matrix.trace (tauQ.map (Rat.castHom ℂ))).re = _
    have htrace : Matrix.trace (tauQ.map (Rat.castHom ℂ)) = 1 := tau.2.2
    rw [htrace]
    norm_num
  have hpos : 0 < normalizer basisWitness (CStarMatrix.ofMatrix.symm rho.1) :=
    by rw [hnormal, ht]; norm_num
  have he : phi basisWitness rho hpos = tau := by
    apply Subtype.ext
    change CStarMatrix.ofMatrix
      ((normalizer basisWitness (CStarMatrix.ofMatrix.symm rho.1))⁻¹ •
        rawOblique basisWitness (CStarMatrix.ofMatrix.symm rho.1)) = _
    rw [hnormal, ht, raw_witness, smul_smul]
    norm_num
  have hle := hc 2 2 basisWitness rho hpos
  rw [he, mi_rho, mi_tau] at hle
  exact (not_le.mpr entropy_inequality) hle

#print axioms ObliqueBasis
#print axioms kraus
#print axioms rawOblique
#print axioms normalizer
#print axioms phi
#print axioms claim
#print axioms result
end D5.S3.Quantum.Information.ObliqueDiscordMutualInformationRefutation
