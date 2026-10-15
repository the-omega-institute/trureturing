/- GID: D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.claim; result=D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.result; claim=D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.claim
   digest: A full-rank qutrit refutes the purification spread lower bound. -/

import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.longLine false
noncomputable section
open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open D5.S3.Quantum.Matrix.CartesianVariance

namespace D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {d : ℕ}

noncomputable def krylovVector (L : E →L[ℂ] E) (v : E) (n : ℕ) : E :=
  InnerProductSpace.gramSchmidtNormed ℂ (fun k : ℕ => (L ^ k) ((‖v‖ : ℂ)⁻¹ • v)) n
noncomputable def spreadComplexity (L : E →L[ℂ] E) (v : E) (t : ℝ) : ℝ :=
  ∑ n : Fin (Module.finrank ℂ E), (n.val : ℝ) *
    Complex.normSq (inner ℂ (krylovVector L v n.val)
      ((NormedSpace.exp ((-(t : ℂ) * Complex.I) • L)) ((‖v‖ : ℂ)⁻¹ • v)))
noncomputable def liouvillianMatrix (H : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.kronecker H 1 - Matrix.kronecker 1 H.transpose
noncomputable def liouvillian (H : Matrix (Fin d) (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d × Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d × Fin d) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (liouvillianMatrix H)
noncomputable def canonicalKet (ρ : Matrix (Fin d) (Fin d) ℂ) := vectorize d (CFC.sqrt ρ)
noncomputable def operatorComplexity (H ρ : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) : ℝ :=
  spreadComplexity (liouvillian H) (vectorize d ρ) t
noncomputable def purificationComplexity (H ρ : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) : ℝ :=
  spreadComplexity (liouvillian H) (canonicalKet ρ) t
def claim : Prop := ∀ (d : ℕ) (ρ H : Matrix (Fin d) (Fin d) ℂ) (t : ℝ),
  ρ.PosDef → Matrix.trace ρ = 1 → H.IsHermitian → 0 ≤ t →
  purificationComplexity H ρ t ≤ operatorComplexity H ρ t

private lemma vectorize_eq_toLp_vec (A : Matrix (Fin d) (Fin d) ℂ) :
    vectorize d A = WithLp.toLp 2 (Matrix.vec A.transpose) := by
  rfl

private lemma liouvillian_ketVec (H A : Matrix (Fin d) (Fin d) ℂ) :
    liouvillian H (vectorize d A) = vectorize d (H * A - A * H) := by
  simp only [liouvillian.eq_1, vectorize_eq_toLp_vec, Matrix.toEuclideanCLM_toLp,
    liouvillianMatrix.eq_1, Matrix.sub_mulVec]
  dsimp only [Matrix.kronecker]
  rw [Matrix.kronecker_mulVec_vec (1 : Matrix (Fin d) (Fin d) ℂ) A.transpose H,
    Matrix.kronecker_mulVec_vec H.transpose A.transpose (1 : Matrix (Fin d) (Fin d) ℂ)]
  simp only [Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one,
    Matrix.transpose_sub, Matrix.transpose_mul]
  rw [← Matrix.vec_sub]

private lemma partialTraceRight_ketVec (A : Matrix (Fin d) (Fin d) ℂ) :
    partialTraceRight (rankOneDensity (fun p => vectorize d A p)) = A * A.conjTranspose := by
  exact D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace2_pure A

private lemma canonicalKet_norm (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htr : Matrix.trace ρ = 1) : ‖canonicalKet ρ‖ = 1 := by
  have hroot : (CFC.sqrt ρ).conjTranspose = CFC.sqrt ρ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian
  have hpartial : partialTraceRight (rankOneDensity (fun p => canonicalKet ρ p)) = ρ := by
    rw [canonicalKet, partialTraceRight_ketVec, hroot, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
  have htrace := trace_partialTraceRight (rankOneDensity (fun p => canonicalKet ρ p))
  rw [hpartial, htr] at htrace
  have hs : inner ℂ (canonicalKet ρ) (canonicalKet ρ) = 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa only [rankOneDensity, Matrix.trace_vecMulVec] using htrace.symm
  have hsreal : ‖canonicalKet ρ‖ ^ 2 = 1 := by
    calc
      ‖canonicalKet ρ‖ ^ 2 = (inner ℂ (canonicalKet ρ) (canonicalKet ρ)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) (canonicalKet ρ)).symm
      _ = 1 := by rw [hs]; rfl
  nlinarith [norm_nonneg (canonicalKet ρ)]

private lemma exp_apply_of_eigenvector (L : E →L[ℂ] E) (x : E) (mu z : ℂ)
    (hx : L x = mu • x) :
    (NormedSpace.exp (z • L)) x = Complex.exp (z * mu) • x := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hp (k : ℕ) : ((z • L) ^ k) x = (z * mu) ^ k • x := by
    by_cases hz : x = 0
    · rw [hz, map_zero, smul_zero]
    · change ((↑((z • L) ^ k) : E →ₗ[ℂ] E)) x = _
      rw [ContinuousLinearMap.toLinearMap_pow]
      apply Module.End.HasEigenvector.pow_apply
      refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hz⟩
      simp only [ContinuousLinearMap.coe_coe, _root_.smul_apply, hx, smul_smul]
  have hsum := (ContinuousLinearMap.apply ℂ E x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • L))
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z * mu)).smul_const x
  rw [← Complex.exp_eq_exp_ℂ] at hscalar
  apply HasSum.unique hsum
  simpa only [ContinuousLinearMap.apply_apply, _root_.smul_apply,
    hp, smul_smul, smul_eq_mul] using hscalar

private lemma exp_pi_div_two_of_cubic (L : E →L[ℂ] E) (x : E)
    (hcubic : (L ^ 3) x = (4 : ℂ) • L x) :
    (NormedSpace.exp ((-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) • L)) x =
      x - (1 / 2 : ℂ) • (L ^ 2) x := by
  let x0 := x - (1 / 4 : ℂ) • (L ^ 2) x
  let xp := (1 / 8 : ℂ) • (L ^ 2) x + (1 / 4 : ℂ) • L x
  let xm := (1 / 8 : ℂ) • (L ^ 2) x - (1 / 4 : ℂ) • L x
  have hpow : L ((L ^ 2) x) = (4 : ℂ) • L x := by
    simpa only [show (3 : ℕ) = 1 + 2 from rfl, pow_succ',
      mul_apply_eq_comp] using hcubic
  have hzero : L x0 = (0 : ℂ) • x0 := by
    simp only [x0, map_sub, map_smul, hpow, smul_smul, zero_smul]
    module
  have hplus : L xp = (2 : ℂ) • xp := by
    simp only [xp, map_add, map_smul, hpow, smul_add, smul_smul]
    change (1 / 8 * 4 : ℂ) • L x + (1 / 4 : ℂ) • (L ^ 2) x = _
    module
  have hminus : L xm = (-2 : ℂ) • xm := by
    simp only [xm, map_sub, map_smul, hpow, smul_sub, smul_smul]
    change (1 / 8 * 4 : ℂ) • L x - (1 / 4 : ℂ) • (L ^ 2) x = _
    module
  have hdecomp : x = x0 + xp + xm := by dsimp [x0, xp, xm]; module
  have heplus : Complex.exp ((-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) * 2) = -1 := by
    rw [show (-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) * 2 =
      -((Real.pi : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have heminus : Complex.exp ((-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) * (-2)) = -1 := by
    rw [show (-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) * (-2) =
      (Real.pi : ℂ) * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
  conv_lhs => rw [hdecomp, map_add, map_add,
    exp_apply_of_eigenvector L x0 0 _ hzero,
    exp_apply_of_eigenvector L xp 2 _ hplus,
    exp_apply_of_eigenvector L xm (-2) _ hminus]
  simp only [mul_zero, Complex.exp_zero, one_smul, heplus, heminus]
  dsimp [x0, xp, xm]
  module

omit [FiniteDimensional ℂ E] in
private lemma krylovVector_three_step (L : E →L[ℂ] E) (v : E)
    (q : Fin 3 → E) (b₁ b₂ : ℝ)
    (hseed : (‖v‖ : ℂ)⁻¹ • v = q 0) (hq : Orthonormal ℂ q)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (h0 : L (q 0) = (b₁ : ℂ) • q 1)
    (h1 : L (q 1) = (b₁ : ℂ) • q 0 + (b₂ : ℂ) • q 2)
    (h2 : L (q 2) = (b₂ : ℂ) • q 1) :
    (∀ j : Fin 3, krylovVector L v j.val = q j) ∧
    (∀ n : ℕ, 3 ≤ n → krylovVector L v n = 0) := by
  let f : ℕ → E := fun k => (L ^ k) ((‖v‖ : ℂ)⁻¹ • v)
  let g := InnerProductSpace.gramSchmidt ℂ f
  have hi (i j : Fin 3) : inner ℂ (q i) (q j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp hq i j
  have hf0 : f 0 = q 0 := by simp [f, hseed]
  have hf1 : f 1 = (b₁ : ℂ) • q 1 := by simpa [f, hseed] using h0
  have hf2 : f 2 = (b₁ ^ 2 : ℂ) • q 0 + ((b₁ * b₂ : ℝ) : ℂ) • q 2 := by
    change L (L ((‖v‖ : ℂ)⁻¹ • v)) = _
    rw [hseed, h0, map_smul, h1, smul_add, smul_smul, smul_smul]
    push_cast
    module
  have hg0 : g 0 = q 0 := by
    simpa only [g, show (0 : ℕ) = ⊥ from rfl, InnerProductSpace.gramSchmidt_bot] using hf0
  have hg1 : g 1 = (b₁ : ℂ) • q 1 := by
    change InnerProductSpace.gramSchmidt ℂ f _ = _
    rw [InnerProductSpace.gramSchmidt_def,
      show Finset.Iio (1 : ℕ) = {0} from rfl, Finset.sum_singleton]
    change f 1 - (ℂ ∙ g 0).starProjection (f 1) = _
    rw [hf1, hg0, Submodule.starProjection_singleton]
    simp [hi]
  have hg2 : g 2 = ((b₁ * b₂ : ℝ) : ℂ) • q 2 := by
    change InnerProductSpace.gramSchmidt ℂ f _ = _
    rw [InnerProductSpace.gramSchmidt_def,
      show Finset.Iio (2 : ℕ) = {0, 1} from rfl]
    simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
      Finset.sum_singleton]
    change f 2 - ((ℂ ∙ g 0).starProjection (f 2) +
      (ℂ ∙ g 1).starProjection (f 2)) = _
    rw [hf2, hg0, hg1, Submodule.starProjection_singleton,
      Submodule.starProjection_singleton]
    simp only [inner_add_right, inner_smul_right, inner_smul_left, hi,
      norm_smul, hq.norm_eq_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hb₁, map_pow, Complex.conj_ofReal, Fin.reduceEq]
    norm_num
  have hfirst : ∀ j : Fin 3, krylovVector L v j.val = q j := by
    intro j
    change (‖g j.val‖ : ℂ)⁻¹ • g j.val = q j
    fin_cases j
    · rw [hg0, hq.norm_eq_one]; simp
    · rw [hg1]
      simp only [norm_smul, hq.norm_eq_one, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hb₁, smul_smul]
      rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hb₁.ne'), one_smul]
      rfl
    · rw [hg2]
      simp only [norm_smul, hq.norm_eq_one, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (mul_pos hb₁ hb₂), smul_smul]
      rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (mul_pos hb₁ hb₂).ne'), one_smul]
      rfl
  refine ⟨hfirst, ?_⟩
  let W := Submodule.span ℂ (Set.range q)
  have hqm (j : Fin 3) : q j ∈ W := Submodule.subset_span (Set.mem_range_self j)
  have hLmem : ∀ y ∈ W, L y ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      fin_cases j
      · change L (q 0) ∈ W
        rw [h0]; exact W.smul_mem _ (hqm 1)
      · change L (q 1) ∈ W
        rw [h1]; exact W.add_mem (W.smul_mem _ (hqm 0)) (W.smul_mem _ (hqm 2))
      · change L (q 2) ∈ W
        rw [h2]; exact W.smul_mem _ (hqm 1)
    | zero => simpa only [map_zero] using W.zero_mem
    | add y z hy hz ihy ihz => simpa only [map_add] using W.add_mem ihy ihz
    | smul c y hy ih => simpa only [map_smul] using W.smul_mem c ih
  have hfmem (n : ℕ) : f n ∈ W := by
    change (L ^ n) ((‖v‖ : ℂ)⁻¹ • v) ∈ W
    rw [hseed]
    change ((↑(L ^ n) : E →ₗ[ℂ] E) (q 0)) ∈ W
    rw [ContinuousLinearMap.toLinearMap_pow]
    exact Module.End.pow_apply_mem_of_forall_mem n hLmem (q 0) (hqm 0)
  intro n hn
  have hgn : g n ∈ W := by
    apply (Submodule.span_le.mpr ?_) (InnerProductSpace.gramSchmidt_mem_span ℂ f le_rfl)
    rintro y ⟨k, hk, rfl⟩
    exact hfmem k
  have horth (j : Fin 3) : inner ℂ (q j) (g n) = 0 := by
    have ho := InnerProductSpace.gramSchmidt_orthogonal ℂ f
      (show j.val ≠ n by omega)
    change inner ℂ (g j.val) (g n) = 0 at ho
    fin_cases j
    · rwa [hg0] at ho
    · rw [hg1, inner_smul_left, Complex.conj_ofReal] at ho
      exact (mul_eq_zero.mp ho).resolve_left (Complex.ofReal_ne_zero.mpr hb₁.ne')
    · rw [hg2, inner_smul_left, Complex.conj_ofReal] at ho
      exact (mul_eq_zero.mp ho).resolve_left
        (Complex.ofReal_ne_zero.mpr (mul_pos hb₁ hb₂).ne')
  have hself : inner ℂ (g n) (g n) = 0 := by
    refine Submodule.span_induction (p := fun y _ => inner ℂ y (g n) = 0)
      ?_ ?_ ?_ ?_ hgn
    · rintro y ⟨j, rfl⟩; exact horth j
    · exact inner_zero_left _
    · intro y z hy hz ihy ihz; rw [inner_add_left, ihy, ihz, add_zero]
    · intro c y hy ih; rw [inner_smul_left, ih, mul_zero]
  have hzero : g n = 0 := inner_self_eq_zero.mp hself
  change (‖g n‖ : ℂ)⁻¹ • g n = 0
  rw [hzero, smul_zero]

private def D : Matrix (Fin 3) (Fin 3) ℂ := diagonalState ![1, 4, 16]
private def S : Matrix (Fin 3) (Fin 3) ℂ := diagonalState ![1, 2, 4]
private def F : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; -1, 0, 0; 0, 0, 0]
private def BD : Matrix (Fin 3) (Fin 3) ℂ := diagonalState ![-92, 87, -16]
private def BS : Matrix (Fin 3) (Fin 3) ℂ := diagonalState ![-22, 19, -4]
private def rhoWitness : Matrix (Fin 3) (Fin 3) ℂ := diagonalState ![1/21, 4/21, 16/21]
private def hWitness : Matrix (Fin 3) (Fin 3) ℂ := !![2, 1, 0; 1, 2, 0; 0, 0, 4]

private lemma rhoWitness_posDef : rhoWitness.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [rhoWitness.eq_1, diagonalState]

private lemma rhoWitness_trace : Matrix.trace rhoWitness = 1 := by
  norm_num [rhoWitness.eq_1, diagonalState, Matrix.trace, Fin.sum_univ_succ]

private lemma hWitness_hermitian : hWitness.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hWitness.eq_1, Matrix.conjTranspose_apply]

private lemma sqrt_rhoWitness : CFC.sqrt rhoWitness = ((Real.sqrt 21 : ℂ)⁻¹) • S := by
  apply CFC.sqrt_unique
  · have hs : (Real.sqrt 21 : ℂ) ^ 2 = 21 := by
      norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
    have hSS : S * S = D := by
      simp only [S.eq_1, D.eq_1, diagonalState, Matrix.diagonal_mul_diagonal]
      apply congrArg Matrix.diagonal
      funext i
      fin_cases i <;> norm_num
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hSS, ← pow_two, inv_pow, hs]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [D.eq_1, rhoWitness.eq_1, diagonalState]
  · have hp : (Matrix.diagonal fun i : Fin 3 => (Real.sqrt 21 : ℂ)⁻¹ *
        ((![(1 : ℝ), 2, 4] i : ℝ) : ℂ)).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro i
      fin_cases i <;> norm_num <;> positivity
    have heq : (Real.sqrt 21 : ℂ)⁻¹ • S = Matrix.diagonal
        (fun i : Fin 3 => (Real.sqrt 21 : ℂ)⁻¹ * ((![(1 : ℝ), 2, 4] i : ℝ) : ℂ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [S.eq_1, diagonalState, Matrix.diagonal_apply]
    rw [heq]
    exact hp.nonneg

private lemma rhoWitness_seed : (‖vectorize 3 rhoWitness‖ : ℂ)⁻¹ • vectorize 3 rhoWitness =
    (Real.sqrt 273 : ℂ)⁻¹ • vectorize 3 D := by
  have hrho : rhoWitness = (1 / 21 : ℂ) • D := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [rhoWitness.eq_1, D.eq_1, diagonalState]
  have hnormD : ‖vectorize 3 D‖ = Real.sqrt 273 := by
    have hi : ‖vectorize 3 D‖ ^ 2 = 273 := by
      rw [D5.S3.Quantum.Matrix.CartesianVariance.vectorize_norm_sq]
      norm_num [RHLinalg.frobSq, D.eq_1, diagonalState, Matrix.trace, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.conjTranspose_apply]
    exact ((Real.sqrt_eq_iff_eq_sq (by norm_num) (norm_nonneg _)).mpr hi.symm).symm
  rw [hrho]
  change (‖(1 / 21 : ℂ) • vectorize 3 D‖ : ℂ)⁻¹ • ((1 / 21 : ℂ) • vectorize 3 D) = _
  rw [norm_smul, hnormD]
  norm_num [smul_smul]
  congr 1
  ring

private lemma purification_seed : (‖canonicalKet rhoWitness‖ : ℂ)⁻¹ •
    canonicalKet rhoWitness = (Real.sqrt 21 : ℂ)⁻¹ • vectorize 3 S := by
  rw [canonicalKet_norm rhoWitness rhoWitness_posDef.posSemidef rhoWitness_trace]
  norm_num only [Complex.ofReal_one, inv_one, one_smul]
  rw [canonicalKet, sqrt_rhoWitness]
  rfl

private def qD : Fin 3 → EuclideanSpace ℂ (Fin 3 × Fin 3) :=
  ![(Real.sqrt 273 : ℂ)⁻¹ • vectorize 3 D, (Real.sqrt 2 : ℂ)⁻¹ • vectorize 3 F,
    (Real.sqrt 16289 : ℂ)⁻¹ • vectorize 3 BD]
private def qS : Fin 3 → EuclideanSpace ℂ (Fin 3 × Fin 3) :=
  ![(Real.sqrt 21 : ℂ)⁻¹ • vectorize 3 S, (Real.sqrt 2 : ℂ)⁻¹ • vectorize 3 F,
    (Real.sqrt 861 : ℂ)⁻¹ • vectorize 3 BS]
private def b1D : ℝ := 3 * Real.sqrt 2 / Real.sqrt 273
private def b2D : ℝ := Real.sqrt 2 * Real.sqrt 16289 / 91
private def b1S : ℝ := Real.sqrt 2 / Real.sqrt 21
private def b2S : ℝ := Real.sqrt 2 * Real.sqrt 861 / 21

private lemma b_squares : b1D ^ 2 = 6/91 ∧ b2D ^ 2 = 358/91 ∧
    b1S ^ 2 = 2/21 ∧ b2S ^ 2 = 82/21 := by
  norm_num [b1D.eq_1, b2D.eq_1, b1S.eq_1, b2S.eq_1, div_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 273),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 16289),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 861)]

private lemma spreadComplexity_three_step_pi_div_two (L : E →L[ℂ] E) (v : E)
    (q : Fin 3 → E) (b₁ b₂ : ℝ) (hdim : 3 ≤ Module.finrank ℂ E)
    (hseed : (‖v‖ : ℂ)⁻¹ • v = q 0) (hq : Orthonormal ℂ q)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (h0 : L (q 0) = (b₁ : ℂ) • q 1)
    (h1 : L (q 1) = (b₁ : ℂ) • q 0 + (b₂ : ℂ) • q 2)
    (h2 : L (q 2) = (b₂ : ℂ) • q 1) (hgap : b₁ ^ 2 + b₂ ^ 2 = 4) :
    spreadComplexity L v (Real.pi / 2) = b₁ ^ 2 * b₂ ^ 2 / 2 := by
  obtain ⟨hfirst, htail⟩ := krylovVector_three_step L v q b₁ b₂ hseed hq hb₁ hb₂ h0 h1 h2
  have hi (i j : Fin 3) : inner ℂ (q i) (q j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp hq i j
  have hp2 : (L ^ 2) (q 0) = (b₁ ^ 2 : ℂ) • q 0 +
      ((b₁ * b₂ : ℝ) : ℂ) • q 2 := by
    change L (L (q 0)) = _
    rw [h0, map_smul, h1, smul_add, smul_smul, smul_smul]
    push_cast
    module
  have hcubic : (L ^ 3) (q 0) = (4 : ℂ) • L (q 0) := by
    change L ((L ^ 2) (q 0)) = _
    rw [hp2, map_add, map_smul, map_smul, h0, h2, smul_smul, smul_smul]
    have hg : (b₁ : ℂ) ^ 2 + (b₂ : ℂ) ^ 2 = 4 := by exact_mod_cast hgap
    push_cast
    trans ((b₁ : ℂ) * ((b₁ : ℂ) ^ 2 + (b₂ : ℂ) ^ 2)) • q 1
    · module
    · rw [hg]; module
  have hevolve : (NormedSpace.exp ((-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) • L))
      ((‖v‖ : ℂ)⁻¹ • v) = (1 - b₁ ^ 2 / 2 : ℂ) • q 0 -
        (((b₁ * b₂ / 2 : ℝ) : ℂ)) • q 2 := by
    rw [hseed, exp_pi_div_two_of_cubic L (q 0) hcubic, hp2]
    push_cast
    module
  unfold spreadComplexity
  rw [hevolve, Finset.sum_eq_single (⟨2, by omega⟩ : Fin (Module.finrank ℂ E))]
  · change 2 * Complex.normSq (inner ℂ (krylovVector L v 2)
      ((1 - b₁ ^ 2 / 2 : ℂ) • q 0 - ((b₁ * b₂ / 2 : ℝ) : ℂ) • q 2)) = _
    have hk2 : krylovVector L v 2 = q 2 := by simpa using hfirst (2 : Fin 3)
    rw [hk2]
    rw [inner_sub_right, inner_smul_right, inner_smul_right, hi 2 0,
      if_neg (by decide), hi 2 2, if_pos rfl]
    simp only [mul_zero, mul_one, zero_sub, Complex.normSq_neg, Complex.normSq_ofReal]
    ring
  · intro n hn hne
    by_cases hz : n.val = 0
    · simp only [hz, Nat.cast_zero, zero_mul]
    by_cases ho : n.val = 1
    · have hk1 : krylovVector L v n.val = q 1 := by simpa [ho] using hfirst (1 : Fin 3)
      rw [hk1]
      rw [inner_sub_right, inner_smul_right, inner_smul_right, hi 1 0,
        if_neg (by decide), hi 1 2, if_neg (by decide)]
      simp only [mul_zero, sub_self, Complex.normSq_zero, mul_zero]
    · have hn2 : n.val ≠ 2 := by
        intro hv
        apply hne
        exact Fin.ext hv
      rw [htail n.val (by omega), inner_zero_left, Complex.normSq_zero, mul_zero]
  · simp

private lemma commutators : hWitness * D - D * hWitness = (3 : ℂ) • F ∧
    hWitness * S - S * hWitness = F ∧
    hWitness * F - F * hWitness = diagonalState ![-2, 2, 0] ∧
    hWitness * BD - BD * hWitness = (179 : ℂ) • F ∧
    hWitness * BS - BS * hWitness = (41 : ℂ) • F := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [hWitness.eq_1, D.eq_1, S.eq_1, F.eq_1, BD.eq_1, BS.eq_1, diagonalState, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ, Matrix.diagonal_apply, Function.flip_def]

private lemma qD_orthonormal : Orthonormal ℂ qD := by
  apply orthonormal_iff_ite.mpr
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [show qD ⟨0, by decide⟩ = (Real.sqrt 273 : ℂ)⁻¹ • vectorize 3 D from
      by rw [qD.eq_1]; rfl,
      show qD ⟨1, by decide⟩ = (Real.sqrt 2 : ℂ)⁻¹ • vectorize 3 F from rfl,
      show qD ⟨2, by decide⟩ = (Real.sqrt 16289 : ℂ)⁻¹ • vectorize 3 BD from rfl] <;>
    rw [inner_smul_left, inner_smul_right, matrix_pairing] <;>
    norm_num [D.eq_1, F.eq_1, BD.eq_1, diagonalState, Matrix.trace, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
    field_simp <;> norm_num [← Complex.ofReal_pow, Real.sq_sqrt]

private lemma qS_orthonormal : Orthonormal ℂ qS := by
  apply orthonormal_iff_ite.mpr
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [show qS ⟨0, by decide⟩ = (Real.sqrt 21 : ℂ)⁻¹ • vectorize 3 S from
      by rw [qS.eq_1]; rfl,
      show qS ⟨1, by decide⟩ = (Real.sqrt 2 : ℂ)⁻¹ • vectorize 3 F from rfl,
      show qS ⟨2, by decide⟩ = (Real.sqrt 861 : ℂ)⁻¹ • vectorize 3 BS from rfl] <;>
    rw [inner_smul_left, inner_smul_right, matrix_pairing] <;>
    norm_num [S.eq_1, F.eq_1, BS.eq_1, diagonalState, Matrix.trace, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
    field_simp <;> norm_num [← Complex.ofReal_pow, Real.sq_sqrt]

private lemma qD_recurrence :
    liouvillian hWitness (qD 0) = (b1D : ℂ) • qD 1 ∧
    liouvillian hWitness (qD 1) = (b1D : ℂ) • qD 0 + (b2D : ℂ) • qD 2 ∧
    liouvillian hWitness (qD 2) = (b2D : ℂ) • qD 1 := by
  refine ⟨?_, ?_, ?_⟩
  · change liouvillian hWitness ((Real.sqrt 273 : ℂ)⁻¹ • vectorize 3 D) =
      (b1D : ℂ) • ((Real.sqrt 2 : ℂ)⁻¹ • vectorize 3 F)
    rw [map_smul, liouvillian_ketVec, commutators.1]
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [qD, b1D.eq_1, vectorize_eq_toLp_vec, F.eq_1, Function.flip_def] <;> field_simp
  · change liouvillian hWitness ((Real.sqrt 2 : ℂ)⁻¹ • vectorize 3 F) =
      (b1D : ℂ) • ((Real.sqrt 273 : ℂ)⁻¹ • vectorize 3 D) +
      (b2D : ℂ) • ((Real.sqrt 16289 : ℂ)⁻¹ • vectorize 3 BD)
    rw [map_smul, liouvillian_ketVec, commutators.2.2.1]
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [qD, b1D.eq_1, b2D.eq_1, vectorize_eq_toLp_vec, D.eq_1, BD.eq_1, diagonalState, Matrix.diagonal_apply] <;>
      field_simp <;> norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  · change liouvillian hWitness ((Real.sqrt 16289 : ℂ)⁻¹ • vectorize 3 BD) =
      (b2D : ℂ) • ((Real.sqrt 2 : ℂ)⁻¹ • vectorize 3 F)
    rw [map_smul, liouvillian_ketVec, commutators.2.2.2.1]
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [qD, b2D.eq_1, vectorize_eq_toLp_vec, F.eq_1, Function.flip_def] <;>
      field_simp <;> norm_num [← Complex.ofReal_pow, Real.sq_sqrt]

private lemma qS_recurrence :
    liouvillian hWitness (qS 0) = (b1S : ℂ) • qS 1 ∧
    liouvillian hWitness (qS 1) = (b1S : ℂ) • qS 0 + (b2S : ℂ) • qS 2 ∧
    liouvillian hWitness (qS 2) = (b2S : ℂ) • qS 1 := by
  refine ⟨?_, ?_, ?_⟩
  · change liouvillian hWitness ((Real.sqrt 21 : ℂ)⁻¹ • vectorize 3 S) =
      (b1S : ℂ) • ((Real.sqrt 2 : ℂ)⁻¹ • vectorize 3 F)
    rw [map_smul, liouvillian_ketVec, commutators.2.1]
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [qS, b1S.eq_1, vectorize_eq_toLp_vec, F.eq_1, Function.flip_def] <;> field_simp
  · change liouvillian hWitness ((Real.sqrt 2 : ℂ)⁻¹ • vectorize 3 F) =
      (b1S : ℂ) • ((Real.sqrt 21 : ℂ)⁻¹ • vectorize 3 S) +
      (b2S : ℂ) • ((Real.sqrt 861 : ℂ)⁻¹ • vectorize 3 BS)
    rw [map_smul, liouvillian_ketVec, commutators.2.2.1]
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [qS, b1S.eq_1, b2S.eq_1, vectorize_eq_toLp_vec, S.eq_1, BS.eq_1, diagonalState, Matrix.diagonal_apply] <;>
      field_simp <;> norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  · change liouvillian hWitness ((Real.sqrt 861 : ℂ)⁻¹ • vectorize 3 BS) =
      (b2S : ℂ) • ((Real.sqrt 2 : ℂ)⁻¹ • vectorize 3 F)
    rw [map_smul, liouvillian_ketVec, commutators.2.2.2.2]
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [qS, b2S.eq_1, vectorize_eq_toLp_vec, F.eq_1, Function.flip_def] <;>
      field_simp <;> norm_num [← Complex.ofReal_pow, Real.sq_sqrt]

private lemma operatorComplexity_witness :
    operatorComplexity hWitness rhoWitness (Real.pi / 2) = (1074 : ℝ) / 8281 := by
  have h := spreadComplexity_three_step_pi_div_two (liouvillian hWitness) (vectorize 3 rhoWitness)
    qD b1D b2D (by simp [finrank_euclideanSpace]) rhoWitness_seed qD_orthonormal
    (by dsimp [b1D]; positivity) (by dsimp [b2D]; positivity)
    qD_recurrence.1 qD_recurrence.2.1 qD_recurrence.2.2
    (by rw [b_squares.1, b_squares.2.1]; norm_num)
  change spreadComplexity _ _ _ = _
  rw [h, b_squares.1, b_squares.2.1]
  norm_num

private lemma purificationComplexity_witness :
    purificationComplexity hWitness rhoWitness (Real.pi / 2) = (82 : ℝ) / 441 := by
  have h := spreadComplexity_three_step_pi_div_two (liouvillian hWitness)
    (canonicalKet rhoWitness) qS b1S b2S (by simp [finrank_euclideanSpace])
    purification_seed qS_orthonormal
    (by dsimp [b1S]; positivity) (by dsimp [b2S]; positivity)
    qS_recurrence.1 qS_recurrence.2.1 qS_recurrence.2.2
    (by rw [b_squares.2.2.1, b_squares.2.2.2]; norm_num)
  change spreadComplexity _ _ _ = _
  rw [h, b_squares.2.2.1, b_squares.2.2.2]
  norm_num

theorem result : ¬ claim := by
  intro h
  have hbound := h 3 rhoWitness hWitness (Real.pi / 2) rhoWitness_posDef rhoWitness_trace
    hWitness_hermitian (le_of_lt Real.pi_div_two_pos)
  rw [purificationComplexity_witness, operatorComplexity_witness] at hbound
  norm_num at hbound

end D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation
