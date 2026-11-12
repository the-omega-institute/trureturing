/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Hermitian coordinates and ordered full-row correlation compounds. -/

import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity

/-! Actual trace-normalized Hermitian coordinates and their correlation geometry. -/

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Matrix Module
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation

namespace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry

variable {n m : ℕ}

lemma hermitian_pair_real (M A : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.IsHermitian) (hA : A.IsHermitian) :
    (((M * A).trace.re : ℝ) : ℂ) = (M * A).trace := by
  exact HermitianMat.inner_eq_trace_rc
    (⟨M, hM⟩ : HermitianMat (Fin n) ℂ) (⟨A, hA⟩ : HermitianMat (Fin n) ℂ)

private lemma hermitian_family_linearIndependent
    (a : Fin m → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a) :
    LinearIndependent ℂ a := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M * a i).trace) hc
  simpa only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.zero_mul, Matrix.trace_zero, ha.2.2, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using he

private def normalizedComplexBasis
    (a : Fin m → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a) :
    Basis (Fin m) ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank' a (hermitian_family_linearIndependent a ha)
    (by simp [Module.finrank_matrix, ha.2.1, pow_two])

private lemma normalizedComplexBasis_apply
    (a : Fin m → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a) (i : Fin m) :
    normalizedComplexBasis a ha i = a i := by
  simp [normalizedComplexBasis]

/-- Actual normalized coordinates. This is the existing Hermitian real trace
inner product, not a second state or norm structure. -/
def coordinates (a : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => (M * a i).trace.re)

private lemma complex_coordinate_expansion
    (a : Fin m → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    M = ∑ i, (M * a i).trace • a i := by
  let b := normalizedComplexBasis a ha
  have hb (i : Fin m) : b i = a i := normalizedComplexBasis_apply a ha i
  have he := b.sum_repr M
  have hcoeff (i : Fin m) : b.repr M i = (M * a i).trace := by
    have hh := congrArg (fun N : Matrix (Fin n) (Fin n) ℂ => (N * a i).trace) he
    simpa only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
      hb, ha.2.2, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh
  calc
    M = ∑ i, b.repr M i • b i := he.symm
    _ = _ := by simp only [hcoeff, hb]

/-- Completeness follows from the full n²-sized trace-dual family. Every actual
Hermitian matrix is reconstructed with real coordinates, without an FNF premise. -/
theorem coordinate_reconstruction
    (a : Fin m → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    M = ∑ i, (((coordinates a M) i : ℝ) : ℂ) • a i := by
  calc
    M = ∑ i, (M * a i).trace • a i := complex_coordinate_expansion a ha M
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (((coordinates a M) i : ℝ) : ℂ) = (M * a i).trace from
        hermitian_pair_real M (a i) hM (ha.1 i)]

/-- Parseval at the exact trace-product normalization used by Peled. -/
theorem coordinates_inner
    (a : Fin m → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a)
    (M N : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    ⟪coordinates a M, coordinates a N⟫_ℝ = (M * N).trace.re := by
  have he := congrArg (fun P : Matrix (Fin n) (Fin n) ℂ => (P * N).trace.re)
    (coordinate_reconstruction a ha M hM)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, coordinates, WithLp.ofLp_toLp]
  rw [he]
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.trace_mul_comm (a i) N]
  simp [coordinates, mul_comm]

theorem coordinates_purity
    (a : Fin m → Matrix (Fin n) (Fin n) ℂ) (ha : IsHermBasis a)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    ‖coordinates a M‖ ^ 2 = (M * M).trace.re := by
  rw [← real_inner_self_eq_norm_sq]
  exact coordinates_inner a ha M M hM hM

open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- Any actual finite convex mixture of product densities is a density. -/
theorem separable_density {da db : ℕ}
    (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ) (hρ : IsSeparable ρ) : IsDensity ρ := by
  obtain ⟨v, w, A, B, hw, hsum, hab, heq⟩ := hρ
  rw [heq]
  constructor
  · exact Matrix.posSemidef_sum _ (fun j _ =>
      ((hab j).1.1.kronecker (hab j).2.1).smul (Complex.zero_le_real.mpr (hw j)))
  · simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_kronecker,
      (hab _).1.2, (hab _).2.2, mul_one]
    simpa [Complex.real_smul] using congrArg (fun x : ℝ => (x : ℂ)) hsum

/-- The general local density-purity bound is reused from the actual Hermitian
trace inner product, in arbitrary finite dimension. -/
theorem density_purity_bounds (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsDensity M) :
    0 ≤ (M * M).trace.re ∧ (M * M).trace.re ≤ 1 := by
  let H : HermitianMat (Fin n) ℂ := ⟨M, hM.1.isHermitian⟩
  have hH : 0 ≤ H := HermitianMat.zero_le_iff.mpr hM.1
  have ht : H.trace = 1 := by
    rw [HermitianMat.trace_eq_re_trace]
    change M.trace.re = 1
    rw [hM.2]
    rfl
  have hu := HermitianMat.inner_le_mul_trace hH hH
  have hn : 0 ≤ ⟪H, H⟫_ℝ := real_inner_self_nonneg
  rw [ht, one_mul, HermitianMat.inner_eq_re_trace] at hu
  rw [HermitianMat.inner_eq_re_trace] at hn
  exact ⟨hn, hu⟩

theorem density_purity_dimension_lower (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsDensity M) :
    1 / (n : ℝ) ≤ (M * M).trace.re := by
  let H : HermitianMat (Fin n) ℂ := ⟨M, hM.1.isHermitian⟩
  have ht : H.trace = 1 := by
    rw [HermitianMat.trace_eq_re_trace]
    change M.trace.re = 1
    rw [hM.2]
    rfl
  have hc := abs_real_inner_le_norm H (1 : HermitianMat (Fin n) ℂ)
  rw [HermitianMat.inner_one, ht, abs_one] at hc
  have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hc
  have hnorm : ‖H‖ ^ 2 = (M * M).trace.re := by
    rw [← real_inner_self_eq_norm_sq, HermitianMat.inner_eq_re_trace]
    rfl
  rw [mul_pow, hnorm, HermitianMat.norm_one, Fintype.card_fin,
    Real.sq_sqrt (Nat.cast_nonneg _)] at hs
  apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
  nlinarith

lemma corr_product_entry {da db ma mb : ℕ}
    (A : Matrix (Fin da) (Fin da) ℂ) (B : Matrix (Fin db) (Fin db) ℂ)
    (a : Fin ma → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin mb → Matrix (Fin db) (Fin db) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ha : ∀ i, (a i).IsHermitian) (hb : ∀ j, (b j).IsHermitian)
    (i : Fin ma) (j : Fin mb) :
    corr (A ⊗ₖ B) a b i j = coordinates a A i * coordinates b B j := by
  unfold corr
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    ← hermitian_pair_real A (a i) hA (ha i),
    ← hermitian_pair_real B (b j) hB (hb j)]
  simp [coordinates]

/-- The actual correlation of any finite product-density mixture is a real
weighted sum of the corresponding actual Hermitian coordinate outer products. -/
theorem correlation_finite_decomposition {da db ma mb v : ℕ}
    (w : Fin v → ℝ)
    (A : Fin v → Matrix (Fin da) (Fin da) ℂ)
    (B : Fin v → Matrix (Fin db) (Fin db) ℂ)
    (a : Fin ma → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin mb → Matrix (Fin db) (Fin db) ℂ)
    (hA : ∀ k, (A k).IsHermitian) (hB : ∀ k, (B k).IsHermitian)
    (ha : ∀ i, (a i).IsHermitian) (hb : ∀ j, (b j).IsHermitian) :
    corr (∑ k, ((w k : ℝ) : ℂ) • (A k ⊗ₖ B k)) a b =
      ∑ k, w k • Matrix.vecMulVec (coordinates a (A k)).ofLp (coordinates b (B k)).ofLp := by
  ext i j
  simp only [corr, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
    Matrix.trace_smul, Complex.re_sum, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hp := corr_product_entry (A k) (B k) a b (hA k) (hB k) ha hb i j
  unfold corr at hp
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using congrArg (fun x : ℝ => w k * x) hp


/-- The sole full row subset, always with its inherited increasing order. -/
def fullRows (n : ℕ) : {r : Finset (Fin n) // r.card = n} :=
  ⟨Finset.univ, by simp⟩

private lemma fullRows_unique (r : {r : Finset (Fin n) // r.card = n}) :
    r = fullRows n := by
  apply Subtype.ext
  exact Finset.eq_univ_of_card r.val (by simpa using r.property)

private lemma fullRows_embedding :
    ⇑((fullRows n).val.orderEmbOfFin (fullRows n).property) = id := by
  symm
  exact Finset.orderEmbOfFin_unique (fullRows n).property
    (fun _ => Finset.mem_univ _) strictMono_id

private lemma full_compound_outer (C : Matrix (Fin n) (Fin m) ℝ) :
    compound n C = Matrix.vecMulVec (Pi.single (fullRows n) 1)
      (fun s => (C.submatrix id (s.val.orderEmbOfFin s.property)).det) := by
  classical
  ext r s
  rw [fullRows_unique r]
  simp only [compound, Matrix.vecMulVec_apply, Pi.single_eq_same, one_mul,
    fullRows_embedding]

/-- Increasing Cauchy--Binet gives the exact squared length of the sole full-order
compound row, including zero determinants and rank-deficient rectangular matrices. -/
theorem full_order_energy (C : Matrix (Fin n) (Fin m) ℝ) :
    ∑ s : {s : Finset (Fin m) // s.card = n},
      (C.submatrix id (s.val.orderEmbOfFin s.property)).det ^ 2 =
      (C * C.transpose).det := by
  rw [cauchyBinet C C.transpose]
  apply Finset.sum_congr rfl
  intro s _
  have ht : C.transpose.submatrix (s.val.orderEmbOfFin s.property) id =
      (C.submatrix id (s.val.orderEmbOfFin s.property)).transpose := rfl
  rw [ht, Matrix.det_transpose, pow_two]

/-- At full smaller-side order every actual Schatten norm is the same square-root
determinant. The infinity norm is the Euclidean operator norm, not an entry maximum. -/
theorem full_order_norms (C : Matrix (Fin n) (Fin m) ℝ) :
    cmnInf n C = Real.sqrt (C * C.transpose).det ∧
    ∀ p : ℝ, 1 ≤ p → cmnP p n C = Real.sqrt (C * C.transpose).det := by
  constructor
  · unfold cmnInf
    rw [full_compound_outer, single_row_opnorm, full_order_energy]
  · intro p hp
    unfold cmnP
    rw [full_compound_outer, single_row_schatten _ _ p (by linarith), full_order_energy]

/-- In the square case the full-order quantity is the absolute determinant. -/
theorem square_full_order_norms (C : Matrix (Fin n) (Fin n) ℝ) :
    cmnInf n C = |C.det| ∧ ∀ p : ℝ, 1 ≤ p → cmnP p n C = |C.det| := by
  have hd : Real.sqrt (C * C.transpose).det = |C.det| := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← pow_two, Real.sqrt_sq_eq_abs]
  simpa only [hd] using full_order_norms C

/-- The actual real change between two complete normalized Hermitian bases. -/
def basisChange (a₀ a₁ : Fin m → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => coordinates a₀ (a₁ i) j

/-- Complete normalized Hermitian basis changes are real orthogonal. -/
theorem basisChange_orthogonal (a₀ a₁ : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (h₀ : IsHermBasis a₀) (h₁ : IsHermBasis a₁) :
    basisChange a₀ a₁ * (basisChange a₀ a₁).transpose = 1 := by
  ext i k
  have hp := coordinates_inner a₀ h₀ (a₁ i) (a₁ k) (h₁.1 i) (h₁.1 k)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hp
  simp only [star_trivial, dotProduct] at hp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, basisChange]
  rw [show (∑ j, coordinates a₀ (a₁ i) j * coordinates a₀ (a₁ k) j) =
      (a₁ i * a₁ k).trace.re by simpa only [mul_comm] using hp,
    h₁.2.2]
  by_cases h : i = k <;> simp [h, Matrix.one_apply]

/-- The actual correlation transforms by this real orthogonal matrix. -/
theorem correlation_basisChange_left {da db ma mb : ℕ}
    (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a₀ a₁ : Fin ma → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin mb → Matrix (Fin db) (Fin db) ℂ)
    (h₀ : IsHermBasis a₀) (h₁ : IsHermBasis a₁) :
    corr ρ a₁ b = basisChange a₀ a₁ * corr ρ a₀ b := by
  ext i k
  change (ρ * (a₁ i ⊗ₖ b k)).trace.re = _
  nth_rw 1 [coordinate_reconstruction a₀ h₀ (a₁ i) (h₁.1 i)]
  have hsum : (∑ j, ((coordinates a₀ (a₁ i) j : ℝ) : ℂ) • a₀ j) ⊗ₖ b k =
      ∑ j, ((coordinates a₀ (a₁ i) j : ℝ) : ℂ) • (a₀ j ⊗ₖ b k) := by
    ext r s
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Finset.sum_mul, smul_eq_mul, mul_assoc]
  rw [hsum]
  simp only [Matrix.mul_sum,
    Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
    Matrix.mul_apply, basisChange, corr, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Full-order quantities are invariant under the actual complete local Alice
basis change; this proof uses orthogonality and actual row-Gram determinants. -/
theorem full_order_basisChange_left {da db mb : ℕ}
    (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a₀ a₁ : Fin (da^2) → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin mb → Matrix (Fin db) (Fin db) ℂ)
    (h₀ : IsHermBasis a₀) (h₁ : IsHermBasis a₁) :
    cmnInf (da^2) (corr ρ a₁ b) = cmnInf (da^2) (corr ρ a₀ b) ∧
    ∀ p : ℝ, 1 ≤ p → cmnP p (da^2) (corr ρ a₁ b) = cmnP p (da^2) (corr ρ a₀ b) := by
  let O := basisChange a₀ a₁
  let C := corr ρ a₀ b
  have ho : O * O.transpose = 1 := basisChange_orthogonal a₀ a₁ h₀ h₁
  have hod := congrArg Matrix.det ho
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hod
  have hg : ((O*C)*(O*C).transpose).det = (C*C.transpose).det := by
    rw [Matrix.transpose_mul]
    have he : (O*C)*(C.transpose*O.transpose) = O*(C*C.transpose)*O.transpose := by
      simp only [Matrix.mul_assoc]
    rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    calc
      _ = (O.det * O.det) * (C*C.transpose).det := by ring
      _ = _ := by rw [hod, one_mul]
  rw [correlation_basisChange_left ρ a₀ a₁ b h₀ h₁]
  change cmnInf (da^2) (O*C) = cmnInf (da^2) C ∧ _
  constructor
  · rw [(full_order_norms (O*C)).1, (full_order_norms C).1, hg]
  · intro p hp
    rw [(full_order_norms (O*C)).2 p hp, (full_order_norms C).2 p hp, hg]

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry
