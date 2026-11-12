/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormQubitBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormQubitBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-dimensional separable qubit fourth-order correlation-minor bound. -/

import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry
import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormTetrahedron
import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormDesignObstruction

/-! The unrestricted qubit fourth-order replacement from the CC BY 4.0 return
note by Haobo Ma (Chrono AI, Singapore) and Wenlin Zhang (NUS and Chrono AI,
Singapore). The proof uses an arbitrary finite actual separable decomposition.
No FNF restriction, decomposition-size bound or classification of maximizers is
introduced. Sharpness in dimensions two and three is not claimed. -/

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Matrix Module
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity

namespace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormQubitBound

private lemma alice_basis : IsHermBasis alice :=
  (rational_noisy_family 0 (by norm_num) (by norm_num)).2.2.1

/-- The determinant-normalizing qubit coordinate scaling. -/
def qubitScaling : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, Real.sqrt 3, Real.sqrt 3, Real.sqrt 3]

private def scaledCoordinates (A : Matrix (Fin 2) (Fin 2) ℂ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (qubitScaling.mulVec (coordinates alice A).ofLp)

private lemma alice_identity_coordinate (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsDensity A) :
    coordinates alice A 0 = 1 / Real.sqrt 2 := by
  simp [coordinates, alice, Matrix.mul_smul, Matrix.trace_smul,
    D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
    Matrix.mul_one, hA.2]
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

private lemma scaled_coordinate_bound (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsDensity A) :
    ‖scaledCoordinates A‖ ≤ Real.sqrt 2 := by
  have hp := (density_purity_bounds A hA).2
  have he := coordinates_purity alice alice_basis A hA.1.isHermitian
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 := alice_identity_coordinate A hA
  have hz : (coordinates alice A 0) ^ 2 = 1/2 := by
    rw [h0, div_pow, hs2]; norm_num
  have hn : ‖scaledCoordinates A‖ ^ 2 = 3 * ‖coordinates alice A‖ ^ 2 - 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [scaledCoordinates, qubitScaling, Matrix.mulVec_diagonal,
      Fin.sum_univ_succ, mul_pow, hs3]
    nlinarith [hz]
  have hu : ‖scaledCoordinates A‖ ^ 2 ≤ 2 := by rw [hn, he]; linarith
  nlinarith [norm_nonneg (scaledCoordinates A), Real.sqrt_nonneg (2:ℝ)]

private lemma coordinate_density_bound {D : ℕ}
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b)
    (B : Matrix (Fin D) (Fin D) ℂ) (hB : IsDensity B) : ‖coordinates b B‖ ≤ 1 := by
  have he := coordinates_purity b hb B hB.1.isHermitian
  have hu := (density_purity_bounds B hB).2
  nlinarith [norm_nonneg (coordinates b B)]

/-- The existing real rectangular nuclear norm controls the scaled correlation.
Transposition makes its column Gram exactly the four-dimensional row Gram. -/
theorem scaled_correlation_traceNorm {D : ℕ}
    (ρ : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) (hρ : IsSeparable ρ)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b) :
    traceNorm (qubitScaling * corr ρ alice b).transpose ≤ Real.sqrt 2 := by
  classical
  obtain ⟨v, w, A, B, hw, hsum, hab, heq⟩ := hρ
  have hc := correlation_finite_decomposition w A B alice b
    (fun j => (hab j).1.1.isHermitian) (fun j => (hab j).2.1.isHermitian)
    alice_basis.1 hb.1
  have hm : (qubitScaling * corr ρ alice b).transpose =
      weightedOuter (fun j => coordinates b (B j)) (fun j => scaledCoordinates (A j)) w := by
    rw [heq, hc]
    ext i k
    simp only [weightedOuter, Matrix.transpose_apply, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, scaledCoordinates,
      WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hm]
  calc
    _ ≤ ∑ j, w j * ‖coordinates b (B j)‖ * ‖scaledCoordinates (A j)‖ :=
      traceNorm_weightedOuter_le _ _ _ hw
    _ ≤ ∑ j, w j * 1 * Real.sqrt 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hx := coordinate_density_bound b hb (B j) (hab j).2
      have hy := scaled_coordinate_bound (A j) (hab j).1
      exact mul_le_mul (mul_le_mul_of_nonneg_left hx (hw j)) hy
        (norm_nonneg _) (by simpa using hw j)
    _ = Real.sqrt 2 := by rw [← Finset.sum_mul]; simp [hsum]

private lemma four_product_le (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) : a*b*c*d ≤ ((a+b+c+d)/4)^4 := by
  have hab : a*b ≤ ((a+b)/2)^2 := by nlinarith [sq_nonneg (a-b)]
  have hcd : c*d ≤ ((c+d)/2)^2 := by nlinarith [sq_nonneg (c-d)]
  have hm : (a+b)*(c+d)/4 ≤ ((a+b+c+d)/4)^2 := by
    nlinarith [sq_nonneg ((a+b)-(c+d))]
  calc
    _ ≤ ((a+b)/2)^2 * ((c+d)/2)^2 := by
      simpa only [mul_assoc] using mul_le_mul hab hcd (mul_nonneg hc hd) (sq_nonneg _)
    _ = ((a+b)*(c+d)/4)^2 := by ring
    _ ≤ (((a+b+c+d)/4)^2)^2 :=
      pow_le_pow_left₀ (by positivity) hm 2
    _ = _ := by ring

private lemma psd_four_det_le_trace (H : Matrix (Fin 4) (Fin 4) ℝ) (hH : H.PosSemidef) :
    H.det ≤ (H.trace/4)^4 := by
  rw [hH.isHermitian.det_eq_prod_eigenvalues, hH.isHermitian.trace_eq_sum_eigenvalues]
  simpa [Fin.prod_univ_succ, Fin.sum_univ_succ, mul_assoc, add_assoc] using
    four_product_le (hH.isHermitian.eigenvalues 0) (hH.isHermitian.eigenvalues 1)
      (hH.isHermitian.eigenvalues 2) (hH.isHermitian.eigenvalues 3)
      (hH.eigenvalues_nonneg 0) (hH.eigenvalues_nonneg 1)
      (hH.eigenvalues_nonneg 2) (hH.eigenvalues_nonneg 3)

private lemma sqrt_gram_det_le_traceNorm {m : ℕ} (C : Matrix (Fin 4) (Fin m) ℝ) :
    Real.sqrt (C*C.transpose).det ≤ (traceNorm C.transpose / 4)^4 := by
  have hG : (C*C.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using C.posSemidef_self_mul_conjTranspose
  have hH : (CFC.sqrt (C*C.transpose)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hd := hG.det_sqrt
  have hd' : (CFC.sqrt (C*C.transpose)).det = Real.sqrt (C*C.transpose).det := by
    simpa only [RCLike.sqrt_real] using hd
  rw [← hd']
  have hu := psd_four_det_le_trace _ hH
  simpa [traceNorm, Matrix.conjTranspose_eq_transpose_of_trivial] using hu

/-- The sharp universal constant, prior to the separate attainment construction. -/
def qubitFourthBound : ℝ := 1 / (192 * Real.sqrt 3)

private lemma scaling_det {m : ℕ} (C : Matrix (Fin 4) (Fin m) ℝ) :
    ((qubitScaling*C)*(qubitScaling*C).transpose).det = 27 * (C*C.transpose).det := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [Matrix.transpose_mul]
  have he : (qubitScaling*C)*(C.transpose*qubitScaling.transpose) =
      qubitScaling*(C*C.transpose)*qubitScaling.transpose := by simp only [Matrix.mul_assoc]
  rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hd : qubitScaling.det * qubitScaling.det = 27 := by
    simp [qubitScaling, Matrix.det_diagonal, Fin.prod_univ_succ]
    ring_nf
    rw [h3]
    norm_num
  calc
    _ = (qubitScaling.det * qubitScaling.det) * (C*C.transpose).det := by ring
    _ = _ := by rw [hd]

/-- For every separable qubit-by-D actual state, with arbitrary finite D,
the full-order actual infinity and finite-p quantities satisfy the universal bound. -/
theorem qubit_fourth_bound_alice {D : ℕ}
    (ρ : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) (hρ : IsSeparable ρ)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b) :
    cmnInf 4 (corr ρ alice b) ≤ qubitFourthBound ∧
    ∀ p : ℝ, 1 ≤ p → cmnP p 4 (corr ρ alice b) ≤ qubitFourthBound := by
  let C := corr ρ alice b
  have ht := scaled_correlation_traceNorm ρ hρ b hb
  have hu := sqrt_gram_det_le_traceNorm (qubitScaling*C)
  have ht0 : 0 ≤ traceNorm (qubitScaling*C).transpose := traceNorm_nonneg _
  have hpow : (traceNorm (qubitScaling*C).transpose/4)^4 ≤ (Real.sqrt 2/4)^4 :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right ht (by norm_num)) 4
  have hs : Real.sqrt ((qubitScaling*C)*(qubitScaling*C).transpose).det ≤ 1/64 := by
    have hs2 : Real.sqrt 2 ^ 4 = 4 := by
      calc
        _ = (Real.sqrt 2 ^ 2)^2 := by ring
        _ = 4 := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    calc
      _ ≤ (Real.sqrt 2/4)^4 := hu.trans hpow
      _ = 1/64 := by rw [div_pow, hs2]; norm_num
  have hG : (C*C.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using C.posSemidef_self_mul_conjTranspose
  have hLG : ((qubitScaling*C)*(qubitScaling*C).transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (qubitScaling*C).posSemidef_self_mul_conjTranspose
  have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1/64)).mpr hs
  rw [Real.sq_sqrt hLG.det_nonneg, scaling_det] at hsquare
  have hb0 : 0 ≤ qubitFourthBound := by unfold qubitFourthBound; positivity
  have hb2 : qubitFourthBound^2 = 1/110592 := by
    norm_num [qubitFourthBound, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hf : Real.sqrt (C*C.transpose).det ≤ qubitFourthBound := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hb0).mp
    rw [Real.sq_sqrt hG.det_nonneg, hb2]
    linarith
  exact ⟨(full_order_norms C).1.trans_le hf,
    fun p hp => ((full_order_norms C).2 p hp).trans_le hf⟩

/-- Complete arbitrary local normalized Hermitian bases, with no FNF hypothesis. -/
theorem qubit_fourth_bound (D : ℕ) (_hD : 2 ≤ D)
    (ρ : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) (hρ : IsSeparable ρ)
    (a : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (ha : IsHermBasis a)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b) :
    cmnInf 4 (corr ρ a b) ≤ qubitFourthBound ∧
    ∀ p : ℝ, 1 ≤ p → cmnP p 4 (corr ρ a b) ≤ qubitFourthBound := by
  have hi := full_order_basisChange_left ρ alice a b alice_basis ha
  norm_num only [Nat.reducePow] at hi
  have hu := qubit_fourth_bound_alice ρ hρ b hb
  constructor
  · rw [hi.1]; exact hu.1
  · intro p hp
    rw [hi.2 p hp]; exact hu.2 p hp

/-- The unrestricted maximum is exactly the stated constant for every D≥4,
with an actual separable density state attaining all the full-order norms. -/
theorem qubit_sharp_maximum (D : ℕ) (hD : 4 ≤ D)
    (a : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (ha : IsHermBasis a)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b) :
    (∀ ρ : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ, IsSeparable ρ →
      cmnInf 4 (corr ρ a b) ≤ qubitFourthBound ∧
      ∀ p : ℝ, 1 ≤ p → cmnP p 4 (corr ρ a b) ≤ qubitFourthBound) ∧
    IsSeparable (CorrelationMinorNormTetrahedron.omega D hD 0) ∧
    IsDensity (CorrelationMinorNormTetrahedron.omega D hD 0) ∧
    cmnInf 4 (corr (CorrelationMinorNormTetrahedron.omega D hD 0) a b) = qubitFourthBound ∧
    ∀ p : ℝ, 1 ≤ p → cmnP p 4 (corr (CorrelationMinorNormTetrahedron.omega D hD 0) a b) = qubitFourthBound := by
  refine ⟨fun ρ hρ => qubit_fourth_bound D (by omega) ρ hρ a ha b hb,
    CorrelationMinorNormTetrahedron.omega_separable D hD 0 (by norm_num) (by norm_num),
    CorrelationMinorNormTetrahedron.omega_density D hD 0 (by norm_num) (by norm_num), ?_⟩
  exact CorrelationMinorNormTetrahedron.tetra_attainment D hD a ha b hb

/-- The precisely defined common-size coherent-pair construction is impossible
at D≥5, while the actual unrestricted maximum is still attained. This makes no
claim about other notions of quantum design or classification of maximizers. -/
theorem coherent_pair_obstruction_with_attainment (D : ℕ) (hD : 5 ≤ D)
    (a : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (ha : IsHermBasis a)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b) :
    (∀ (v : ℕ) (P : Fin v → Matrix (Fin 2) (Fin 2) ℂ)
      (R : Fin v → Matrix (Fin D) (Fin D) ℂ),
      ¬(CorrelationMinorNormDesignObstruction.PureDesign P ∧
        CorrelationMinorNormDesignObstruction.PureDesign R)) ∧
    cmnInf 4 (corr (CorrelationMinorNormTetrahedron.omega D (by omega) 0) a b) = qubitFourthBound ∧
    ∀ p : ℝ, 1 ≤ p → cmnP p 4 (corr (CorrelationMinorNormTetrahedron.omega D (by omega) 0) a b) = qubitFourthBound := by
  refine ⟨fun v P R h => CorrelationMinorNormDesignObstruction.no_coherent_pair D hD ⟨v, P, R, h⟩, ?_⟩
  exact CorrelationMinorNormTetrahedron.tetra_attainment D (by omega) a ha b hb

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormQubitBound
