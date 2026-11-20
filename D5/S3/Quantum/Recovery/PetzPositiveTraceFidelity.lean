import D5.S3.Quantum.CommutingMidpoint.Fidelity
import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
import D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation

/-!
Finite POVM characterization and positive trace-preserving monotonicity
for the library root fidelity. The construction follows the spectral
measurement in positive-map-postselected-petz-recovery.txt and its audit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.CommutingMidpoint (rootFidelity)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability (entryNormSq_eq_hs_sq)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer (spectral_sqrt_inverse_products)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)

namespace PetzPositiveTraceFidelity

variable {n m ι : Type*} [Fintype n] [DecidableEq n]

/-- The unnormalized classical overlap of the two lists of outcome masses. -/
def povmOverlap [Fintype ι] (U V : Matrix n n ℂ) (N : ι → Matrix n n ℂ) : ℝ :=
  ∑ i, Real.sqrt ((trace (U * N i)).re * (trace (V * N i)).re)

private theorem traceNorm_mul_le_frobenius (A B : Matrix n n ℂ) :
    traceNorm (A * B) ≤ ‖A‖ * ‖B‖ := by
  simpa only [entryNormSq_eq_hs_sq, Real.sqrt_sq_eq_abs, abs_norm] using
    D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.traceNorm_mul_le_hsSq A B

omit [DecidableEq n] in
private theorem traceNorm_sum_le (s : Finset ι) (A : ι → Matrix n n ℂ) :
    traceNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, traceNorm (A i) := by
  classical
  refine Finset.le_sum_of_subadditive traceNorm ?_ traceNorm_add_le s A
  simp [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm, CFC.sqrt_zero]

private theorem frobenius_sqrt_mul_sqrt (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ‖CFC.sqrt A * CFC.sqrt B‖ = Real.sqrt (trace (A * B)).re := by
  have hRA : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hRB : (CFC.sqrt B)ᴴ = CFC.sqrt B :=
    (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hGram :
      (CFC.sqrt A * CFC.sqrt B)ᴴ * (CFC.sqrt A * CFC.sqrt B) =
        CFC.sqrt B * A * CFC.sqrt B := by
    rw [Matrix.conjTranspose_mul, hRA, hRB]
    calc
      _ = CFC.sqrt B * (CFC.sqrt A * CFC.sqrt A) * CFC.sqrt B := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self A hA.nonneg]
  have htrace : trace (CFC.sqrt B * A * CFC.sqrt B) = trace (A * B) := by
    rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self B hB.nonneg, Matrix.trace_mul_comm B A]
  have hs := congrArg Complex.re
    (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace (CFC.sqrt A * CFC.sqrt B))
  rw [hGram, htrace, Complex.ofReal_re] at hs
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

private theorem rootFidelity_eq_traceNorm (U V : Matrix n n ℂ) (hV : V.PosSemidef) :
    rootFidelity U V = traceNorm (CFC.sqrt V * CFC.sqrt U) := by
  have hRU : (CFC.sqrt U)ᴴ = CFC.sqrt U :=
    (CFC.sqrt_nonneg U).posSemidef.isHermitian.eq
  have hRV : (CFC.sqrt V)ᴴ = CFC.sqrt V :=
    (CFC.sqrt_nonneg V).posSemidef.isHermitian.eq
  have hGram :
      (CFC.sqrt V * CFC.sqrt U)ᴴ * (CFC.sqrt V * CFC.sqrt U) =
        CFC.sqrt U * V * CFC.sqrt U := by
    rw [Matrix.conjTranspose_mul, hRU, hRV]
    calc
      _ = CFC.sqrt U * (CFC.sqrt V * CFC.sqrt V) * CFC.sqrt U := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self V hV.nonneg]
  change (trace (CFC.sqrt (CFC.sqrt U * V * CFC.sqrt U))).re =
    (trace (CFC.sqrt ((CFC.sqrt V * CFC.sqrt U)ᴴ * (CFC.sqrt V * CFC.sqrt U)))).re
  rw [hGram]

/-- Every finite POVM bounds root fidelity from above, for arbitrary PSD masses. -/
theorem rootFidelity_le_povmOverlap [Fintype ι] (U V : Matrix n n ℂ)
    (hU : U.PosSemidef) (hV : V.PosSemidef) (N : ι → Matrix n n ℂ)
    (hN : ∀ i, (N i).PosSemidef) (hSum : ∑ i, N i = 1) :
    rootFidelity U V ≤ povmOverlap U V N := by
  classical
  let A := fun i => CFC.sqrt V * CFC.sqrt (N i)
  let B := fun i => CFC.sqrt (N i) * CFC.sqrt U
  have hsplit : CFC.sqrt V * CFC.sqrt U = ∑ i, A i * B i := by
    have hterm (i : ι) : A i * B i = CFC.sqrt V * N i * CFC.sqrt U := by
      calc
        _ = CFC.sqrt V * (CFC.sqrt (N i) * CFC.sqrt (N i)) * CFC.sqrt U := by
          simp only [A, B, Matrix.mul_assoc]
        _ = _ := by rw [CFC.sqrt_mul_sqrt_self _ (hN i).nonneg]
    simp only [hterm, ← Matrix.sum_mul, ← Matrix.mul_sum, hSum, Matrix.mul_one]
  calc
    rootFidelity U V = traceNorm (∑ i, A i * B i) := by
      rw [rootFidelity_eq_traceNorm U V hV, hsplit]
    _ ≤ ∑ i, traceNorm (A i * B i) := traceNorm_sum_le Finset.univ _
    _ ≤ povmOverlap U V N := by
      unfold povmOverlap
      refine Finset.sum_le_sum fun i _ => ?_
      calc
        traceNorm (A i * B i) ≤ ‖A i‖ * ‖B i‖ := traceNorm_mul_le_frobenius _ _
        _ = Real.sqrt ((trace (U * N i)).re * (trace (V * N i)).re) := by
          rw [show ‖A i‖ = Real.sqrt (trace (V * N i)).re from
                frobenius_sqrt_mul_sqrt V (N i) hV (hN i),
              show ‖B i‖ = Real.sqrt (trace (N i * U)).re from
                frobenius_sqrt_mul_sqrt (N i) U (hN i) hU,
              Matrix.trace_mul_comm (N i) U,
              Real.sqrt_mul (Complex.nonneg_iff.mp (hU.trace_mul_nonneg (hN i))).1]
          exact mul_comm _ _

/-- The spectral observable whose restriction to the support of U attains the overlap. -/
def fidelityObservable (U V : Matrix n n ℂ) : Matrix n n ℂ :=
  spectralInverseSqrt U * CFC.sqrt (CFC.sqrt U * V * CFC.sqrt U) *
    spectralInverseSqrt U

private theorem fidelityObservable_facts (U V : Matrix n n ℂ)
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    let P := spectralSupport U
    let K := fidelityObservable U V
    K.PosSemidef ∧ P * K = K ∧ K * P = K ∧ K * U * K = P * V * P ∧
      (trace (U * K)).re = rootFidelity U V := by
  let P := spectralSupport U
  let R := CFC.sqrt U
  let W := spectralInverseSqrt U
  let Z := R * V * R
  let H := CFC.sqrt Z
  let K := fidelityObservable U V
  obtain ⟨hR, hW, hP, -, -, hRP, -, hWUW⟩ := spectral_sqrt_normalization U hU
  obtain ⟨hRW, hWR, hPW, hWP⟩ := spectral_sqrt_inverse_products U hU
  change Rᴴ = R at hR
  change Wᴴ = W at hW
  change Pᴴ = P at hP
  change R * P = R at hRP
  change W * U * W = P at hWUW
  change R * W = P at hRW
  change W * R = P at hWR
  change P * W = W at hPW
  change W * P = W at hWP
  have hZ : Z.PosSemidef := by
    simpa only [Z, hR] using hV.conjTranspose_mul_mul_same R
  have hH : H.PosSemidef := (CFC.sqrt_nonneg Z).posSemidef
  have hHH : H * H = Z := CFC.sqrt_mul_sqrt_self _ hZ.nonneg
  have hRQ : R * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hRP, sub_self]
  have hQ : (1 - P)ᴴ = 1 - P := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP]
  have hHQ : H * (1 - P) = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    calc
      _ = (1 - P) * (H * H) * (1 - P) := by
        simp only [Matrix.conjTranspose_mul, hQ, hH.isHermitian.eq, Matrix.mul_assoc]
      _ = 0 := by
        simp only [hHH, Z, Matrix.mul_assoc, hRQ, Matrix.mul_zero]
  have hHP : H * P = H := by
    rw [Matrix.mul_sub, Matrix.mul_one] at hHQ
    exact (sub_eq_zero.mp hHQ).symm
  have hPH : P * H = H := by
    simpa only [Matrix.conjTranspose_mul, hP, hH.isHermitian.eq] using
      congrArg Matrix.conjTranspose hHP
  have hK : K = W * H * W := rfl
  have hKU : K * U * K = P * V * P := by
    calc
      K * U * K = W * H * (W * U * W) * H * W := by
        rw [hK]
        simp only [Matrix.mul_assoc]
      _ = W * (H * P) * H * W := by rw [hWUW]; simp only [Matrix.mul_assoc]
      _ = W * (H * H) * W := by rw [hHP, Matrix.mul_assoc W H H]
      _ = (W * R) * V * (R * W) := by rw [hHH]; simp only [Z, Matrix.mul_assoc]
      _ = P * V * P := by rw [hWR, hRW]
  have hUW : U * W = R := by
    have hRR : R * R = U := CFC.sqrt_mul_sqrt_self U hU.nonneg
    calc
      U * W = R * (R * W) := by rw [← Matrix.mul_assoc, hRR]
      _ = R := by rw [hRW, hRP]
  have htrace : trace (U * K) = trace H := by
    calc
      _ = trace (R * H * W) := by
        rw [hK, ← Matrix.mul_assoc U (W * H) W, ← Matrix.mul_assoc U W H, hUW]
      _ = trace H := by rw [Matrix.trace_mul_cycle, hWR, hPH]
  change K.PosSemidef ∧ P * K = K ∧ K * P = K ∧ K * U * K = P * V * P ∧
    (trace (U * K)).re = rootFidelity U V
  refine ⟨?_, ?_, ?_, hKU, ?_⟩
  · rw [hK]
    simpa only [hW] using hH.conjTranspose_mul_mul_same W
  · rw [hK]
    simp only [← Matrix.mul_assoc, hPW]
  · rw [hK, Matrix.mul_assoc (W * H) W P, hWP]
  · exact congrArg Complex.re htrace

theorem fidelityObservable_posSemidef (U V : Matrix n n ℂ)
    (hU : U.PosSemidef) (hV : V.PosSemidef) : (fidelityObservable U V).PosSemidef :=
  (fidelityObservable_facts U V hU hV).1

/-- The distinct real eigenvalues, with each eigenspace used once. -/
def fidelityEigenvalues {K : Matrix n n ℂ} (hK : K.IsHermitian) : Finset ℝ := by
  classical
  exact Finset.univ.image hK.eigenvalues

private theorem mem_fidelityEigenvalues {K : Matrix n n ℂ} (hK : K.IsHermitian)
    (x : ℝ) : x ∈ fidelityEigenvalues hK ↔ x ∈ spectrum ℝ K := by
  classical
  simp only [fidelityEigenvalues, hK.spectrum_real_eq_range_eigenvalues, Finset.mem_image,
    Finset.mem_univ, true_and, Set.mem_range]

private def eigenIndicator (k x : ℝ) : ℝ := by
  classical
  exact if x = k then 1 else 0

private def eigenProjection (K : Matrix n n ℂ) (k : ℝ) : Matrix n n ℂ :=
  cfc (eigenIndicator k) K

private theorem eigenProjection_facts {K : Matrix n n ℂ} (hK : K.IsHermitian) (k : ℝ) :
    IsStarProjection (eigenProjection K k) ∧
      K * eigenProjection K k = k • eigenProjection K k := by
  classical
  let f := eigenIndicator k
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ K) :=
    K.finite_real_spectrum.continuousOn g
  change IsStarProjection (cfc f K) ∧ K * cfc f K = k • cfc f K
  constructor
  · refine ⟨?_, cfc_predicate f K⟩
    change cfc f K * cfc f K = cfc f K
    rw [← cfc_mul f f K (hc f) (hc f)]
    apply cfc_congr
    intro x _
    by_cases hx : x = k <;> simp [f, eigenIndicator, hx]
  · calc
      K * cfc f K = cfc (fun x : ℝ => x) K * cfc f K := by
        rw [cfc_id' ℝ K hK.isSelfAdjoint]
      _ = cfc (fun x : ℝ => x * f x) K := (cfc_mul _ _ K (hc _) (hc _)).symm
      _ = cfc (fun x : ℝ => k * f x) K := by
        apply cfc_congr
        intro x _
        by_cases hx : x = k <;> simp [f, eigenIndicator, hx]
      _ = k • cfc f K := cfc_const_mul k f K (hc f)

private theorem sum_eigenProjection {K : Matrix n n ℂ} (hK : K.IsHermitian) :
    ∑ i : ↥(fidelityEigenvalues hK), eigenProjection K i.val = 1 := by
  classical
  let f : ↥(fidelityEigenvalues hK) → ℝ → ℝ := fun i => eigenIndicator i.val
  change (∑ i, cfc (f i) K) = 1
  rw [← cfc_sum_univ f K (fun i => K.finite_real_spectrum.continuousOn (f i))]
  calc
    _ = cfc (fun _ : ℝ => 1) K := by
      apply cfc_congr
      intro x hx
      let i : ↥(fidelityEigenvalues hK) := ⟨x, (mem_fidelityEigenvalues hK x).mpr hx⟩
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp [f, eigenIndicator, i]
      · intro j _ hji
        have hne : x ≠ j.val := fun he => hji (Subtype.ext he.symm)
        simp [f, eigenIndicator, hne]
      · simp
    _ = 1 := cfc_const_one ℝ K hK.isSelfAdjoint

/-- The spectral projections of K restricted to the support of U, completed by
the orthogonal complement as outcome none. -/
def fidelitySpectralPovm (U V : Matrix n n ℂ) (hK : (fidelityObservable U V).IsHermitian) :
    Option ↥(fidelityEigenvalues hK) → Matrix n n ℂ
  | none => 1 - spectralSupport U
  | some i => spectralSupport U * eigenProjection (fidelityObservable U V) i.val

set_option maxHeartbeats 1000000 in
/-- An actual finite projective POVM attains the overlap, including for singular
or zero inputs of arbitrary trace. -/
theorem fidelitySpectralPovm_attains (U V : Matrix n n ℂ)
    (hU : U.PosSemidef) (hV : V.PosSemidef) (hK : (fidelityObservable U V).IsHermitian) :
    (∀ i, IsStarProjection (fidelitySpectralPovm U V hK i)) ∧
    (∑ i, fidelitySpectralPovm U V hK i) = 1 ∧
    povmOverlap U V (fidelitySpectralPovm U V hK) = rootFidelity U V := by
  classical
  let P := spectralSupport U
  let K := fidelityObservable U V
  let E := fun i : ↥(fidelityEigenvalues hK) => eigenProjection K i.val
  let N := fidelitySpectralPovm U V hK
  obtain ⟨-, -, hP, hPP, -, -, hPU, -⟩ := spectral_sqrt_normalization U hU
  obtain ⟨hKpos, hPK, hKP, hKUK, hTrace⟩ := fidelityObservable_facts U V hU hV
  change Pᴴ = P at hP
  change P * P = P at hPP
  change P * U = U at hPU
  change P * K = K at hPK
  change K * P = K at hKP
  change K * U * K = P * V * P at hKUK
  change (trace (U * K)).re = rootFidelity U V at hTrace
  have hPproj : IsStarProjection P := ⟨hPP, hP⟩
  have hKcommP : Commute K P := hKP.trans hPK.symm
  have hNsome (i : ↥(fidelityEigenvalues hK)) : N (some i) = P * E i := rfl
  have hEcommP (i : ↥(fidelityEigenvalues hK)) : Commute (E i) P :=
    hKcommP.cfc_real (eigenIndicator i.val)
  have hProj (i : Option ↥(fidelityEigenvalues hK)) : IsStarProjection (N i) := by
    cases i with
    | none => exact hPproj.one_sub
    | some i =>
      rw [hNsome]
      exact hPproj.mul (eigenProjection_facts hK i.val).1 (hEcommP i).symm
  have hSum : (∑ i, N (some i)) = P := by
    simp only [hNsome, ← Matrix.mul_sum, show (∑ i, E i) = 1 from sum_eigenProjection hK,
      Matrix.mul_one]
  have hComplete : (∑ i, N i) = 1 := by
    rw [Fintype.sum_option, hSum]
    change (1 - P) + P = 1
    exact sub_add_cancel 1 P
  have hUP : U * P = U := by
    simpa only [Matrix.conjTranspose_mul, hU.isHermitian.eq, hP] using
      congrArg Matrix.conjTranspose hPU
  have hNone : (trace (U * N none)).re = 0 := by
    change (Matrix.trace (U * (1 - P))).re = 0
    rw [Matrix.mul_sub, Matrix.mul_one, hUP, sub_self, Matrix.trace_zero, Complex.zero_re]
  have hPN (i : ↥(fidelityEigenvalues hK)) : P * N (some i) = N (some i) := by
    rw [hNsome, ← Matrix.mul_assoc P P, hPP]
  have hNP (i : ↥(fidelityEigenvalues hK)) : N (some i) * P = N (some i) := by
    rw [hNsome, Matrix.mul_assoc P (E i) P, (hEcommP i).eq, ← Matrix.mul_assoc P P, hPP]
  have hKN (i : ↥(fidelityEigenvalues hK)) : K * N (some i) = i.val • N (some i) := by
    have hEigen : K * E i = i.val • E i := (eigenProjection_facts hK i.val).2
    rw [hNsome]
    calc
      K * (P * E i) = P * (K * E i) := by
        simp only [← Matrix.mul_assoc, hKP, hPK]
      _ = _ := by rw [hEigen, Matrix.mul_smul]
  have hNK (i : ↥(fidelityEigenvalues hK)) : N (some i) * K = K * N (some i) := by
    have hEK : Commute (E i) K := (Commute.refl K).cfc_real (eigenIndicator i.val)
    rw [hNsome]
    calc
      (P * E i) * K = P * (K * E i) := by rw [Matrix.mul_assoc, hEK.eq]
      _ = K * (P * E i) := by simp only [← Matrix.mul_assoc, hKP, hPK]
  have hMass (i : ↥(fidelityEigenvalues hK)) :
      (trace (V * N (some i))).re = i.val ^ 2 * (trace (U * N (some i))).re := by
    let D := N (some i)
    have hCompress : trace ((P * V * P) * D) = trace (V * D) := by
      calc
        _ = trace (P * (V * D)) := by simp only [Matrix.mul_assoc, D, hPN]
        _ = trace ((V * D) * P) := Matrix.trace_mul_comm _ _
        _ = _ := by rw [Matrix.mul_assoc V D P, show D * P = D from hNP i]
    have hProd : (K * D) * K = i.val ^ 2 • D := by
      change (K * N (some i)) * K = i.val ^ 2 • N (some i)
      rw [hKN, Matrix.smul_mul, hNK, hKN, smul_smul, pow_two]
    change (trace (V * D)).re = i.val ^ 2 * (trace (U * D)).re
    calc
      _ = (trace ((K * U * K) * D)).re := by rw [hKUK, hCompress]
      _ = (trace (K * (U * (K * D)))).re := by simp only [Matrix.mul_assoc]
      _ = (trace ((U * (K * D)) * K)).re := congrArg Complex.re (Matrix.trace_mul_comm _ _)
      _ = (trace (U * ((K * D) * K))).re := by rw [Matrix.mul_assoc U (K * D) K]
      _ = _ := by simp only [hProd, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re,
        smul_eq_mul]
  have hTerm (i : ↥(fidelityEigenvalues hK)) :
      Real.sqrt ((trace (U * N (some i))).re * (trace (V * N (some i))).re) =
        (trace (U * (K * N (some i)))).re := by
    let a := (trace (U * N (some i))).re
    have ha : 0 ≤ a :=
      (Complex.nonneg_iff.mp (hU.trace_mul_nonneg (hProj (some i)).nonneg.posSemidef)).1
    have hi : 0 ≤ i.val := by
      have hs := (mem_fidelityEigenvalues hK i.val).mp i.property
      rw [hK.spectrum_real_eq_range_eigenvalues] at hs
      obtain ⟨j, hj⟩ := hs
      rw [← hj]
      exact hKpos.eigenvalues_nonneg j
    rw [hMass, hKN, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
    change Real.sqrt (a * (i.val ^ 2 * a)) = i.val * a
    rw [show a * (i.val ^ 2 * a) = (i.val * a) ^ 2 by ring, Real.sqrt_sq (mul_nonneg hi ha)]
  refine ⟨hProj, hComplete, ?_⟩
  change povmOverlap U V N = rootFidelity U V
  calc
    povmOverlap U V N = ∑ i, (trace (U * (K * N (some i)))).re := by
      simp only [povmOverlap, Fintype.sum_option, hNone, zero_mul, Real.sqrt_zero,
        zero_add, hTerm]
    _ = (trace (U * (K * ∑ i, N (some i)))).re := by
      simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    _ = rootFidelity U V := by rw [hSum, hKP, hTrace]

/-- Root fidelity is the minimum overlap over finite POVMs. -/
theorem rootFidelity_isLeast_povmOverlap (U V : Matrix n n ℂ)
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    IsLeast {a : ℝ | ∃ (α : Type) (hα : Fintype α) (N : α → Matrix n n ℂ),
      letI : Fintype α := hα
      (∀ i, (N i).PosSemidef) ∧ (∑ i, N i) = 1 ∧ a = povmOverlap U V N}
      (rootFidelity U V) := by
  let hK := (fidelityObservable_posSemidef U V hU hV).isHermitian
  obtain ⟨hProj, hSum, hOverlap⟩ := fidelitySpectralPovm_attains U V hU hV hK
  constructor
  · exact ⟨Option ↥(fidelityEigenvalues hK), inferInstance, fidelitySpectralPovm U V hK,
      fun i => (hProj i).nonneg.posSemidef, hSum, hOverlap.symm⟩
  · intro a ha
    obtain ⟨α, hα, N, hN, hSum, hOverlap⟩ := ha
    let _ : Fintype α := hα
    rw [hOverlap]
    exact rootFidelity_le_povmOverlap U V hU hV N hN hSum

/-- Trace preservation of the forward map makes its actual trace dual unital. -/
theorem traceDual_unital [Fintype m] [DecidableEq m] (Φ : MatrixMap n m ℂ)
    (hTP : ∀ X, trace (Φ X) = trace X) : Φ.dual 1 = 1 := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  rw [← MatrixMap.Dual.trace_eq]
  simpa only [Matrix.mul_one] using hTP X

/-- Root fidelity increases under finite complex-linear positive trace-preserving
maps. The PSD arguments may have arbitrary traces. -/
theorem rootFidelity_mono_positive_tracePreserving [Fintype m] [DecidableEq m]
    (Φ : MatrixMap n m ℂ) (hΦ : Φ.IsPositive)
    (hTP : ∀ X, trace (Φ X) = trace X)
    (U V : Matrix n n ℂ) (hU : U.PosSemidef) (hV : V.PosSemidef) :
    rootFidelity U V ≤ rootFidelity (Φ U) (Φ V) := by
  let hK := (fidelityObservable_posSemidef (Φ U) (Φ V) (hΦ hU) (hΦ hV)).isHermitian
  let N := fidelitySpectralPovm (Φ U) (Φ V) hK
  obtain ⟨hN, hSum, hOverlap⟩ := fidelitySpectralPovm_attains (Φ U) (Φ V) (hΦ hU) (hΦ hV) hK
  change (∀ i, IsStarProjection (N i)) at hN
  change (∑ i, N i) = 1 at hSum
  change povmOverlap (Φ U) (Φ V) N = rootFidelity (Φ U) (Φ V) at hOverlap
  have hDual : Φ.dual.IsPositive := hΦ.dual
  let M := fun i => Φ.dual (N i)
  have hM (i : Option ↥(fidelityEigenvalues hK)) : (M i).PosSemidef :=
    hDual (hN i).nonneg.posSemidef
  have hMSum : (∑ i, M i) = 1 := by
    simp only [M, ← map_sum, hSum, traceDual_unital Φ hTP]
  calc
    rootFidelity U V ≤ povmOverlap U V M :=
      rootFidelity_le_povmOverlap U V hU hV M hM hMSum
    _ = povmOverlap (Φ U) (Φ V) N := by
      simp only [povmOverlap, M, ← MatrixMap.Dual.trace_eq]
    _ = _ := hOverlap

end PetzPositiveTraceFidelity
