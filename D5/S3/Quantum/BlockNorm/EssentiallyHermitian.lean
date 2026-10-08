/- GID: D5/S3/Quantum/BlockNorm/EssentiallyHermitian
   generality: G
   mirror-B: D5/B/S3/Quantum/BlockNorm/EssentiallyHermitian
   mirror-E: none(waiver:analytic-matrix-inequality)
   anchors: []
   utility: none
   digest: The positive-completion norm bound forces an essentially Hermitian matrix. -/
/-
result: proof_shape: content; escape_witness: result
admission_basis: open-problem-resolution (#13752; Proved)
Direct frozen dependencies: none; same-delivery dependency: SpikeEdgeEstimate.
Private declarations (name: shape [live consumer]; content witness follows =):
apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart: bind-only [exists_orthonormalBasis_apply_eq_smul_of_isStarNormal]; exists_orthonormalBasis_apply_eq_smul_of_isStarNormal: bind-only [exists_mem_unitaryGroup_star_mul_mul_eq_diagonal]; isStarNormal_toEuclideanLin: bind-only [exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (instance inference)].
exists_mem_unitaryGroup_star_mul_mul_eq_diagonal: bind-only [normal_projected_outer_essentially]; kd_hermitian: bind-only [edge_symmetry]; j_star: bind-only [shifted_psd_iff].
j_square: bind-only [shifted_psd_iff]; j_conjugation: bind-only [shifted_psd_iff]; reflect_positive_shift: bind-only [shifted_psd_iff].
shift_nonneg: bind-only [shifted_psd_iff]; shifted_psd_iff: bind-only [edge_symmetry]; lower_shift_iff: bind-only [edge_symmetry].
edge_symmetry: bind-only [edge_symmetry_forces_defect_zero]; first_coefficient_zero: bind-only [edge_symmetry_forces_defect_zero]; escape_witness: none; second_coefficient_zero: bind-only [edge_symmetry_forces_pairing_zero]; escape_witness: none.
centered_outer_eq_implies_affine_real: content=centered_outer_eq_implies_affine_real [diagonal_projected_implies_affine]; unitary_affine_reconstruction: bind-only [normal_projected_outer_essentially]; outer_covariance: bind-only [projected_conjugation].
dot_unitary: bind-only [projected_outer_eq_unitary]; projected_conjugation: bind-only [projected_outer_eq_unitary]; projected_outer_eq_unitary: bind-only [normal_projected_outer_essentially].
unit_dot_iff_norm: bind-only [normal_unit_projected_essentially]; flat_projected: bind-only [diagonal_projected_implies_affine]; diagonal_projected_implies_affine: content=centered_outer_eq_implies_affine_real [normal_projected_outer_essentially].
normal_projected_outer_essentially: content=centered_outer_eq_implies_affine_real [normal_unit_projected_essentially]; normal_unit_projected_essentially: content=centered_outer_eq_implies_affine_real [result]; edge_symmetry_forces_defect_zero: content=SpikeEdgeEstimate.positive_spike_enclosure [completion_bound_norm_eq].
completion_bound_norm_eq: content=SpikeEdgeEstimate.positive_spike_enclosure [completion_bound_normal]; completion_bound_normal: content=SpikeEdgeEstimate.positive_spike_enclosure [result]; outer_pairing_trace: bind-only [zero_pairing_outer_equal].
zero_pairing_outer_equal: bind-only [trace_square_defect]; projected_orth: bind-only [trace_square_defect]; projected_action: bind-only [sandwich_annihilates].
projected_pairing: bind-only [trace_square_defect]; sandwich_annihilates: bind-only [completion_bound_projected_outer]; annihilates_sandwich: bind-only [trace_square_defect].
trace_square_defect: bind-only [completion_bound_projected_outer]; edge_symmetry_forces_pairing_zero: content=SpikeEdgeEstimate.positive_spike_enclosure [completion_bound_projected_outer]; completion_bound_projected_outer: content=SpikeEdgeEstimate.positive_spike_enclosure [result].
Information-escape registration is paused under CLAUDE.md §3.9.
-/
import D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
/-! The normal-operator and normal-matrix diagonalization proofs are adapted from
the TauCeti contributors, commit 7c8d7117e41432d613582fc600dcb0a3be7dba30,
under Apache-2.0. Copyright (c) 2026 The Tau Ceti contributors.
The license is available at https://www.apache.org/licenses/LICENSE-2.0. -/
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Module Module.End ComplexStarModule
namespace LinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
/-- On a joint eigenspace of the real and imaginary parts of `T`, where `ℜ T` acts by `a` and
`ℑ T` by `b`, the operator `T` acts by `a + i b`. Normality is not needed here; finite
dimensionality only enters because the adjoint, hence `ℜ T` and `ℑ T`, is defined on
finite-dimensional spaces. -/
private theorem apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart (T : E →ₗ[ℂ] E)
    {a b : ℂ} {v : E} (ha : v ∈ eigenspace (ℜ T : E →ₗ[ℂ] E) a)
    (hb : v ∈ eigenspace (ℑ T : E →ₗ[ℂ] E) b) :
    T v = (a + Complex.I * b) • v := by
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [add_apply, smul_apply, mem_eigenspace_iff.mp ha, mem_eigenspace_iff.mp hb, add_smul,
    mul_smul]
/-- **The spectral theorem for normal operators.** A normal operator on a finite-dimensional
complex inner product space has an orthonormal basis of eigenvectors. The basis may be indexed by
any finite type whose cardinality is the dimension of the space. -/
private theorem exists_orthonormalBasis_apply_eq_smul_of_isStarNormal (T : E →ₗ[ℂ] E) [IsStarNormal T]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℂ E) :
    ∃ (b : OrthonormalBasis ι ℂ E) (μ : ι → ℂ), ∀ i, T (b i) = μ i • b i := by
  classical
  -- The real and imaginary parts of `T` are self-adjoint and commute because `T` is normal.
  have hA : (ℜ T : E →ₗ[ℂ] E).IsSymmetric := (isSymmetric_iff_isSelfAdjoint _).mpr (ℜ T).2
  have hB : (ℑ T : E →ₗ[ℂ] E).IsSymmetric := (isSymmetric_iff_isSelfAdjoint _).mpr (ℑ T).2
  have hV := IsSymmetric.directSum_isInternal_of_commute hA hB (Commute.realPart_imaginaryPart T)
  have hO := IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB
  -- Only finitely many joint eigenspaces are nonzero, and they still decompose the space.
  let V : ℂ × ℂ → Submodule ℂ E := fun p =>
    eigenspace (ℜ T : E →ₗ[ℂ] E) p.2 ⊓ eigenspace (ℑ T : E →ₗ[ℂ] E) p.1
  let J := {p : ℂ × ℂ // V p ≠ ⊥}
  let _ : Fintype J := hV.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hVJ : DirectSum.IsInternal fun p : J => V p := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hOJ := hO.comp (Subtype.val_injective (p := fun p => V p ≠ ⊥))
  -- An orthonormal basis subordinate to the joint eigenspaces diagonalizes `T`.
  let b := hVJ.subordinateOrthonormalBasis rfl hOJ
  let p : Fin (finrank ℂ E) → J := fun j => hVJ.subordinateOrthonormalBasisIndex rfl j hOJ
  let e : ι ≃ Fin (finrank ℂ E) := Fintype.equivFinOfCardEq hι
  refine ⟨b.reindex e.symm, fun i => (p (e i)).1.2 + Complex.I * (p (e i)).1.1, fun i => ?_⟩
  have hmem := hVJ.subordinateOrthonormalBasis_subordinate rfl (e i) hOJ
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
  exact apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart T (Submodule.mem_inf.mp hmem).1
    (Submodule.mem_inf.mp hmem).2
end LinearMap
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The operator of a normal matrix on `EuclideanSpace 𝕜 n` is normal. -/
private instance isStarNormal_toEuclideanLin {𝕜 : Type*} [RCLike 𝕜] (A : Matrix n n 𝕜) [IsStarNormal A] :
    IsStarNormal (toEuclideanLin A) where
  star_comm_self := by
    have h : Aᴴ * A = A * Aᴴ := star_comm_self' A
    rw [commute_iff_eq, LinearMap.star_eq_adjoint, ← toEuclideanLin_conjTranspose_eq_adjoint,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← toLpLin_mul_same, ← toLpLin_mul_same, h]
/-- **The spectral theorem for normal matrices.** A normal complex matrix is unitarily
diagonalizable: there is a unitary matrix `U` with `star U * A * U` diagonal. -/
theorem exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (A : Matrix n n ℂ) [IsStarNormal A] :
    ∃ U ∈ unitaryGroup n ℂ, ∃ d : n → ℂ, star U * A * U = diagonal d := by
  obtain ⟨b, μ, hb⟩ := LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal
    (toEuclideanLin A) (ι := n) finrank_euclideanSpace.symm
  -- `U` is the change of basis from the eigenbasis `b` to the standard basis `s`.
  set s := (EuclideanSpace.basisFun n ℂ).toBasis
  have hU : s.toMatrix b.toBasis ∈ unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b
  refine ⟨_, hU, μ, ?_⟩
  -- Its inverse `star U` is the change of basis the other way.
  have hstar : star (s.toMatrix b.toBasis) = b.toBasis.toMatrix s := by
    rw [← Matrix.mul_one (star _), ← s.toMatrix_mul_toMatrix_flip b.toBasis, ← Matrix.mul_assoc,
      (mem_unitaryGroup_iff'.mp hU), Matrix.one_mul]
  -- So `star U * A * U` is the matrix of `A` in the eigenbasis, which is diagonal.
  have hA : A = LinearMap.toMatrix s s (toEuclideanLin A) := by
    rw [toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  rw [hstar, hA, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  by_cases h : i = j <;> simp [LinearMap.toMatrix_apply, hb, h]
end Matrix
namespace D5.S3.Quantum.BlockNorm.EssentiallyHermitian
open Matrix InnerProductSpace
open D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate
section
open Matrix
def EssentiallyHermitian {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (α β : ℂ) (H : Matrix (Fin n) (Fin n) ℂ),
    H.IsHermitian ∧ X = α • H + β • 1
def CompletionBound {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    (Matrix.fromBlocks A X Xᴴ B).PosSemidef →
    ‖Matrix.fromBlocks A X Xᴴ B‖ ≤ ‖A + B‖
def claim : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ X : Matrix (Fin n) (Fin n) ℂ,
    CompletionBound X → EssentiallyHermitian X
private theorem kd_hermitian {n : ℕ} (X D : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.IsHermitian) : (K X D).IsHermitian :=
  hD.fromBlocks rfl hD.neg
private theorem j_star (n : ℕ) : ((Matrix.fromBlocks 1 0 0 (-1)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ᴴ = (Matrix.fromBlocks 1 0 0 (-1)) := by
  simp [ fromBlocks_conjTranspose]
private theorem j_square (n : ℕ) : ((Matrix.fromBlocks 1 0 0 (-1)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) * (Matrix.fromBlocks 1 0 0 (-1)) = 1 := by
  simp [ fromBlocks_multiply, ← fromBlocks_one]
private theorem j_conjugation {n : ℕ} (X D : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.fromBlocks 1 0 0 (-1)) * K X D * (Matrix.fromBlocks 1 0 0 (-1)) = -(K X (-D)) := by
  simp [ K, fromBlocks_multiply, fromBlocks_neg]
private theorem reflect_positive_shift {n : ℕ} [NeZero n]
    (X D : Matrix (Fin n) (Fin n) ℂ) (hb : CompletionBound X)
    (c : ℝ) (hc : 0 ≤ c) (hp : (c • 1 + K X D).PosSemidef) :
    (c • 1 - K X D).PosSemidef := by
  have hm : c • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) + K X D =
      fromBlocks (c • 1 + D) X Xᴴ (c • 1 - D) := by
    ext i j <;> cases i <;> cases j <;> simp [K, fromBlocks, Matrix.one_apply, sub_eq_add_neg]
  have hn := hb (c • 1 + D) (c • 1 - D) (hm ▸ hp)
  have hs : (c • (1 : Matrix (Fin n) (Fin n) ℂ) + D) + (c • 1 - D) = (2*c) • 1 := by
    module
  rw [← hm, hs] at hn
  have hnorm : ‖(2*c) • (1 : Matrix (Fin n) (Fin n) ℂ)‖ = 2*c := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [hnorm] at hn
  have hlo := (CStarAlgebra.norm_le_iff_le_algebraMap _ (by positivity : 0 ≤ 2*c) hp.nonneg).mp hn
  rw [Matrix.le_iff] at hlo
  rw [Algebra.algebraMap_eq_smul_one] at hlo
  have heq : (2*c) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) -
      (c • 1 + K X D) = c • 1 - K X D := by module
  rw [heq] at hlo
  exact hlo
private theorem shift_nonneg {n : ℕ} [NeZero n]
    (X D : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (hp : (c • 1 + K X D).PosSemidef) : 0 ≤ c := by
  have hl := (Complex.nonneg_iff.mp (hp.diag_nonneg (i := Sum.inl (0 : Fin n)))).1
  have hr := (Complex.nonneg_iff.mp (hp.diag_nonneg (i := Sum.inr (0 : Fin n)))).1
  simp [K, fromBlocks, Matrix.one_apply] at hl hr
  linarith
private theorem shifted_psd_iff {n : ℕ} [NeZero n]
    (X D : Matrix (Fin n) (Fin n) ℂ) (hb : CompletionBound X) (c : ℝ) :
    (c • 1 + K X D).PosSemidef ↔ (c • 1 - K X D).PosSemidef := by
  constructor
  · intro hp
    exact reflect_positive_shift X D hb c (shift_nonneg X D c hp) hp
  · intro hp
    have heq : (Matrix.fromBlocks 1 0 0 (-1)) * (c • 1 - K X D) * ((Matrix.fromBlocks 1 0 0 (-1)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ᴴ = c • 1 + K X (-D) := by
      rw [j_star, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
        mul_one, j_square, j_conjugation]
      simp
    have hp' := hp.mul_mul_conjTranspose_same ((Matrix.fromBlocks 1 0 0 (-1)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    rw [heq] at hp'
    have hm := reflect_positive_shift X (-D) hb c (shift_nonneg X (-D) c hp') hp'
    have heq' : (Matrix.fromBlocks 1 0 0 (-1)) * (c • 1 - K X (-D)) * ((Matrix.fromBlocks 1 0 0 (-1)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ᴴ = c • 1 + K X D := by
      rw [j_star, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
        mul_one, j_square, j_conjugation]
      simp
    have hm' := hm.mul_mul_conjTranspose_same ((Matrix.fromBlocks 1 0 0 (-1)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    rwa [heq'] at hm'
private theorem lower_shift_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (c : ℝ) :
    (c • 1 + K).PosSemidef ↔ ∀ x ∈ spectrum ℝ K, -c ≤ x := by
  have h := algebraMap_le_iff_le_spectrum (r := -c)
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hK)
  rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h
  have heq : K - (-c) • (1 : Matrix ι ι ℂ) = c • 1 + K := by module
  rwa [heq] at h
private theorem edge_symmetry {n : ℕ} [NeZero n]
    (X D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian)
    (hb : CompletionBound X) : edgeMax (K X D) + edgeMin (K X D) = 0 := by
  have hK := kd_hermitian X D hD
  have hsa := Matrix.isHermitian_iff_isSelfAdjoint.mp hK
  have hne := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) (K X D) hsa
  have hmax := (spectrum.isCompact (𝕜 := ℝ) (K X D)).isGreatest_sSup hne
  have hmin := (spectrum.isCompact (𝕜 := ℝ) (K X D)).isLeast_sInf hne
  have hl : ((-edgeMin (K X D)) • 1 + K X D).PosSemidef := by
    apply (lower_shift_iff _ hK _).mpr
    intro x hx
    simpa [edgeMin] using hmin.2 hx
  have hr := (shifted_psd_iff X D hb (-edgeMin (K X D))).mp hl
  have hle := (upper_shift_iff _ hK _).mp hr _ hmax.1
  have hu : (edgeMax (K X D) • 1 - K X D).PosSemidef := by
    apply (upper_shift_iff _ hK _).mpr
    exact hmax.2
  have hv := (shifted_psd_iff X D hb (edgeMax (K X D))).mpr hu
  have hge := (lower_shift_iff _ hK _).mp hv _ hmin.1
  change edgeMax (K X D) ≤ -edgeMin (K X D) at hle
  change -edgeMax (K X D) ≤ edgeMin (K X D) at hge
  linarith
end
section
private theorem first_coefficient_zero (T c a : ℝ) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hbound : ∀ t : ℝ, T ≤ t → 0 < t → |a/t| ≤ c/t^3) : a=0 := by
  by_contra ha
  have hapos : 0 < |a| := abs_pos.mpr ha
  let t := T+2+c/|a|
  have htc : 0 ≤ c/|a| := div_nonneg hc hapos.le
  have htT : T ≤ t := by dsimp [t]; linarith
  have ht1 : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 < t := by linarith
  have hb := hbound t htT ht0
  rw [abs_div,abs_of_pos ht0] at hb
  have hb' : |a| *t^2 ≤ c := by
    have hm := (div_le_div_iff₀ ht0 (by positivity : 0 < t^3)).mp hb
    nlinarith [show 0 < t^2 by positivity]
  have heq : t*|a|=(T+2)*|a|+c := by dsimp [t]; field_simp
  have hp : 0 < (T+2)*|a| := mul_pos (by linarith) hapos
  have hm := mul_le_mul_of_nonneg_right ht1 (by positivity : 0 ≤ t*|a|)
  nlinarith
private theorem second_coefficient_zero (T c b : ℝ) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hbound : ∀ t : ℝ, T ≤ t → 0 < t → |b/t^2| ≤ c/t^3) : b=0 := by
  by_contra hb
  have hbpos : 0 < |b| := abs_pos.mpr hb
  let t := T+2+c/|b|
  have htc : 0 ≤ c/|b| := div_nonneg hc hbpos.le
  have htT : T ≤ t := by dsimp [t]; linarith
  have ht0 : 0 < t := by dsimp [t]; linarith
  have hh := hbound t htT ht0
  rw [abs_div,abs_of_nonneg (sq_nonneg t)] at hh
  have hle : |b| *t ≤ c := by
    have hm := (div_le_div_iff₀ (by positivity : 0 < t^2) (by positivity : 0 < t^3)).mp hh
    nlinarith [show 0 < t^2 by positivity]
  have heq : t*|b|=(T+2)*|b|+c := by dsimp [t]; field_simp
  have hp : 0 < (T+2)*|b| := mul_pos (by linarith) hbpos
  nlinarith
end
section
private theorem centered_outer_eq_implies_affine_real {ι : Type*} (z : ι → ℂ) (m : ℂ)
    (h : ∀ i j, (z i-m)*star (z j-m) = star (z i-m)*(z j-m)) :
    ∃ (α β : ℂ) (r : ι → ℝ), ∀ i, z i = α*(r i : ℂ)+β := by
  by_cases hc : ∀ i, z i = m
  · exact ⟨0,m,fun _ => 0,fun i => by simp [hc i]⟩
  · push_neg at hc
    obtain ⟨j,hj⟩ := hc
    have hj0 : z j-m ≠ 0 := sub_ne_zero.mpr hj
    refine ⟨z j-m,m,fun i => ((z i-m)/(z j-m)).re,?_⟩
    intro i
    have heq : star ((z i-m)/(z j-m)) = (z i-m)/(z j-m) := by
      rw [show star ((z i-m)/(z j-m)) = star (z i-m)/star (z j-m) from
        map_div₀ (starRingEnd ℂ) (z i-m) (z j-m)]
      apply (div_eq_div_iff (star_ne_zero.mpr hj0) hj0).mpr
      simpa [mul_comm] using (h i j).symm
    have hr := Complex.conj_eq_iff_re.mp heq
    rw [hr]
    field_simp
    ring
private theorem unitary_affine_reconstruction {n : ℕ}
    (U X : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) (α β : ℂ)
    (r : Fin n → ℝ) (hU : U*Uᴴ = 1)
    (hz : ∀ i, z i = α*(r i : ℂ)+β)
    (hX : X = U*diagonal z*Uᴴ) : EssentiallyHermitian X := by
  let R : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (r i : ℂ))
  have hR : R.IsHermitian := by
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    ext i
    simp
  refine ⟨α,β,U*R*Uᴴ,Matrix.isHermitian_mul_mul_conjTranspose U hR,?_⟩
  have hd : diagonal z = α • R + β • 1 := by
    ext i j
    simp [R,Matrix.diagonal_apply,Matrix.one_apply]
    split_ifs with hij
    · subst j; exact hz i
    · simp
  rw [hX,hd,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_smul_comm,
    smul_mul_assoc,mul_one,hU]
private def ProjectedOuterEq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ v : Fin n → ℂ, star v ⬝ᵥ v = 1 →
    (Matrix.vecMulVec ((1-(Matrix.vecMulVec v (star v))) *ᵥ (X *ᵥ v)) (star ((1-(Matrix.vecMulVec v (star v))) *ᵥ (X *ᵥ v)))) = (Matrix.vecMulVec ((1-(Matrix.vecMulVec v (star v))) *ᵥ (Xᴴ *ᵥ v)) (star ((1-(Matrix.vecMulVec v (star v))) *ᵥ (Xᴴ *ᵥ v))))
private theorem outer_covariance {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    (Matrix.vecMulVec (U *ᵥ v) (star (U *ᵥ v))) = U*(Matrix.vecMulVec v (star v))*Uᴴ := by
  simp only [ star_mulVec, mul_vecMulVec, vecMulVec_mul]
private theorem dot_unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ*U=1) (v : Fin n → ℂ) :
    star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hU, vecMul_one]
private theorem projected_conjugation {n : ℕ} (U X : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ*U=1) (v : Fin n → ℂ) :
    Uᴴ *ᵥ ((1-(Matrix.vecMulVec (U *ᵥ v) (star (U *ᵥ v)))) *ᵥ (X *ᵥ (U *ᵥ v))) =
      (1-(Matrix.vecMulVec v (star v))) *ᵥ ((Uᴴ*X*U) *ᵥ v) := by
  rw [outer_covariance]
  simp only [mulVec_mulVec]
  congr 1
  simp only [← mul_assoc, mul_sub, sub_mul, mul_one, hU, one_mul]
private theorem projected_outer_eq_unitary {n : ℕ} (U X : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ*U=1) (hX : ProjectedOuterEq X) : ProjectedOuterEq (Uᴴ*X*U) := by
  intro v hv
  have hh := hX (U *ᵥ v) (by rwa [dot_unitary U hU])
  apply_fun (fun M => Uᴴ*M*U) at hh
  have hcov : ∀ v : Fin n → ℂ, Uᴴ*(Matrix.vecMulVec v (star v))*U = (Matrix.vecMulVec (Uᴴ *ᵥ v) (star (Uᴴ *ᵥ v))) := by
    intro v
    simpa only [conjTranspose_conjTranspose] using (outer_covariance Uᴴ v).symm
  rw [hcov, hcov, projected_conjugation U X hU v,
    projected_conjugation U Xᴴ hU v] at hh
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc] using hh
private theorem unit_dot_iff_norm {n : ℕ} (v : Fin n → ℂ) :
    star v ⬝ᵥ v = 1 ↔ ‖WithLp.toLp 2 v‖ = 1 := by
  have hn : ((‖WithLp.toLp 2 v‖^2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
    have hs := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
      (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))).symm
    convert hs using 1
    · norm_cast
    · exact dotProduct_comm _ _
  rw [← hn]
  norm_cast
  constructor
  · intro h; nlinarith [norm_nonneg (WithLp.toLp 2 v)]
  · intro h; simp [h]
private theorem flat_projected {n : ℕ} (z : Fin n → ℂ) (c : ℝ) :
    (1-(Matrix.vecMulVec (fun _ : Fin n => (c : ℂ)) (star (fun _ : Fin n => (c : ℂ))))) *ᵥ
        (diagonal z *ᵥ (fun _ => (c : ℂ))) =
      fun i => (z i-(c : ℂ)^2*∑ j, z j)*(c : ℂ) := by
  rw [sub_mulVec, one_mulVec]
  ext i
  simp only [ vecMulVec_mulVec, mulVec_diagonal, Pi.sub_apply,
    MulOpposite.smul_eq_mul_unop, Pi.smul_apply]
  simp only [dotProduct, Pi.star_apply, mulVec_diagonal, MulOpposite.unop_op,
    Complex.star_def, Complex.conj_ofReal, ← Finset.mul_sum, ← Finset.sum_mul]
  ring
private theorem diagonal_projected_implies_affine {n : ℕ} (hn : 1 ≤ n) (z : Fin n → ℂ)
    (h : ProjectedOuterEq (diagonal z)) :
    ∃ (α β : ℂ) (r : Fin n → ℝ), ∀ i, z i = α*(r i : ℂ)+β := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  let c : ℝ := (Real.sqrt n)⁻¹
  have hcp : 0 < c := by dsimp [c]; positivity
  have hcsq : (n : ℝ)*c^2 = 1 := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hnp.le]
    exact mul_inv_cancel₀ hnp.ne'
  have hv : star (fun _ : Fin n => (c : ℂ)) ⬝ᵥ (fun _ => (c : ℂ)) = 1 := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_cast
    nlinarith [hcsq]
  have hh := h _ hv
  rw [flat_projected, diagonal_conjTranspose, flat_projected] at hh
  let m : ℂ := (c : ℂ)^2*∑ j, z j
  have hms : (c : ℂ)^2*∑ j, star (z j) = star m := by
    simp [m, star_mul, star_pow, mul_comm]
  simp only [Pi.star_apply] at hh
  rw [hms] at hh
  apply centered_outer_eq_implies_affine_real z m
  intro i j
  have hij := congrFun (congrFun hh i) j
  change ((z i-m)*(c : ℂ))*star ((z j-m)*(c : ℂ)) =
      ((star (z i)-star m)*(c : ℂ))*star ((star (z j)-star m)*(c : ℂ)) at hij
  have hcreal : star (c : ℂ) = (c : ℂ) := by simp
  simp only [star_mul, star_sub, star_star, hcreal] at hij
  have hc0 : (c : ℂ)^2 ≠ 0 := by exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hcp.ne')
  apply mul_right_cancel₀ hc0
  simp only [star_sub]
  linear_combination hij
private theorem normal_projected_outer_essentially {n : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStarNormal X)
    (hp : ProjectedOuterEq X) : EssentiallyHermitian X := by
  letI : IsStarNormal X := hX
  obtain ⟨U,hU,z,hz⟩ := Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal X
  change Uᴴ*X*U = diagonal z at hz
  have hUl : Uᴴ*U=1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUr : U*Uᴴ=1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hd := projected_outer_eq_unitary U X hUl hp
  rw [hz] at hd
  obtain ⟨α,β,r,hr⟩ := diagonal_projected_implies_affine hn z hd
  have hrec : X = U*diagonal z*Uᴴ := by
    rw [← hz]
    simp only [mul_assoc]
    rw [← mul_assoc U Uᴴ, hUr, one_mul, mul_one]
  exact unitary_affine_reconstruction U X z α β r hUr hr hrec
private theorem normal_unit_projected_essentially {n : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStarNormal X)
    (hp : ∀ v : Fin n → ℂ, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖=1 →
      (Matrix.vecMulVec ((1-(Matrix.vecMulVec v (star v))) *ᵥ (X *ᵥ v)) (star ((1-(Matrix.vecMulVec v (star v))) *ᵥ (X *ᵥ v)))) = (Matrix.vecMulVec ((1-(Matrix.vecMulVec v (star v))) *ᵥ (Xᴴ *ᵥ v)) (star ((1-(Matrix.vecMulVec v (star v))) *ᵥ (Xᴴ *ᵥ v))))) :
    EssentiallyHermitian X := by
  apply normal_projected_outer_essentially hn X hX
  intro v hv
  exact hp v ((unit_dot_iff_norm v).mp hv)
end
section
private theorem edge_symmetry_forces_defect_zero {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (hb : CompletionBound X)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖=1) : defect1 X v=0 := by
  let L := max 1 ‖K X 0‖
  have hL : 1 ≤ L := le_max_left _ _
  have hEn : ‖K X 0‖ ≤ L := le_max_right _ _
  apply first_coefficient_zero (96*L) (1782*L^4) (defect1 X v) (by linarith) (by positivity)
  intro t ht ht0
  have hh := edge_sum_bound X 0 v t L hv (Matrix.isHermitian_zero) (by simp) hL hEn ht
  have hD : (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+0).IsHermitian := ((outer_hermitian v).smul (isSelfAdjoint_iff.mpr rfl)).add Matrix.isHermitian_zero
  have he : edgeMax (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+0))+edgeMin (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+0))=0 :=
    edge_symmetry X _ hD hb
  rw [he] at hh
  simpa [defect2] using hh
private theorem completion_bound_norm_eq {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (hb : CompletionBound X)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖toEuclideanCLM (𝕜 := ℂ) X v‖=‖toEuclideanCLM (𝕜 := ℂ) Xᴴ v‖ := by
  by_cases hv : v=0
  · simp [hv]
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let k := ((‖v‖⁻¹ : ℝ) : ℂ) • v
  have hk : ‖k‖=1 := by simp [k,norm_smul,hnv]
  have hd := edge_symmetry_forces_defect_zero X hb k hk
  have heq : ‖toEuclideanCLM (𝕜 := ℂ) X k‖=‖toEuclideanCLM (𝕜 := ℂ) Xᴴ k‖ := by
    dsimp [defect1] at hd
    nlinarith [norm_nonneg (toEuclideanCLM (𝕜 := ℂ) X k),norm_nonneg (toEuclideanCLM (𝕜 := ℂ) Xᴴ k)]
  simp only [k,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_norm] at heq
  exact (mul_left_cancel₀ (inv_ne_zero hnv)) heq
private theorem completion_bound_normal {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (hb : CompletionBound X) : IsStarNormal X := by
  let T := toEuclideanCLM (𝕜 := ℂ) X
  have ht : toEuclideanCLM (𝕜 := ℂ) Xᴴ=T.adjoint := by
    have hs : toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (star X) =
        star (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) :=
      map_star (R := Matrix (Fin n) (Fin n) ℂ)
        (S := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
        (toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) X
    simpa only [T,Matrix.star_eq_conjTranspose,ContinuousLinearMap.star_eq_adjoint] using hs
  letI : IsStarNormal T := ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mpr (fun v => by
    rw [← ht]; exact completion_bound_norm_eq X hb v)
  apply (isStarNormal_iff X).mpr
  rw [commute_iff_eq]
  have hm : toEuclideanCLM (𝕜 := ℂ) (star X*X)=toEuclideanCLM (𝕜 := ℂ) (X*star X) := by
    simp only [map_mul,Matrix.star_eq_conjTranspose,ht]
    exact star_comm_self' T
  exact (toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).injective hm
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem outer_pairing_trace (S : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) :
    ((Matrix.vecMulVec (u).ofLp (star (u).ofLp))*S).trace=⟪u,toEuclideanCLM (𝕜 := ℂ) S u⟫_ℂ := by
  rw [Matrix.trace_mul_comm]
  simp only [mul_vecMulVec,trace_vecMulVec,
    EuclideanSpace.inner_eq_star_dotProduct,ofLp_toEuclideanCLM]
private theorem zero_pairing_outer_equal (u w : EuclideanSpace ℂ ι)
    (hz : (⟪u,toEuclideanCLM (𝕜 := ℂ) ((Matrix.vecMulVec (u).ofLp (star (u).ofLp))-(Matrix.vecMulVec (w).ofLp (star (w).ofLp))) u⟫_ℂ).re-
      (⟪w,toEuclideanCLM (𝕜 := ℂ) ((Matrix.vecMulVec (u).ofLp (star (u).ofLp))-(Matrix.vecMulVec (w).ofLp (star (w).ofLp))) w⟫_ℂ).re=0) : (Matrix.vecMulVec (u).ofLp (star (u).ofLp))=(Matrix.vecMulVec (w).ofLp (star (w).ofLp)) := by
  let S := (Matrix.vecMulVec (u).ofLp (star (u).ofLp))-(Matrix.vecMulVec (w).ofLp (star (w).ofLp))
  have hS : S.IsHermitian := (outer_hermitian u).sub (outer_hermitian w)
  have he : (S*S).trace=⟪u,toEuclideanCLM (𝕜 := ℂ) S u⟫_ℂ-
      ⟪w,toEuclideanCLM (𝕜 := ℂ) S w⟫_ℂ := by
    change (((Matrix.vecMulVec (u).ofLp (star (u).ofLp))-(Matrix.vecMulVec (w).ofLp (star (w).ofLp)))*S).trace = _
    rw [sub_mul,trace_sub,outer_pairing_trace,outer_pairing_trace]
  have hr : ((Sᴴ*S).trace).re=0 := by rw [hS.eq,he,Complex.sub_re]; exact hz
  have hp := (Matrix.posSemidef_conjTranspose_mul_self S).trace_nonneg
  have hi : ((Sᴴ*S).trace).im=0 := (Complex.nonneg_iff.mp hp).2.symm
  have htr : (Sᴴ*S).trace=0 := by apply Complex.ext <;> simp [hr,hi]
  have hs0 : S=0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr
  exact sub_eq_zero.mp hs0
private def projected (v z : EuclideanSpace ℂ ι) := z-⟪v,z⟫_ℂ • v
private theorem projected_orth (v z : EuclideanSpace ℂ ι) (hv : ‖v‖=1) :
    ⟪v,projected v z⟫_ℂ=0 := by
  simp only [projected,inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K,hv]
  norm_num
private theorem projected_action (v z : EuclideanSpace ℂ ι) :
    toEuclideanCLM (𝕜 := ℂ) (1-(Matrix.vecMulVec (v).ofLp (star (v).ofLp))) z=projected v z := by
  rw [map_sub]
  simp [outer_action,projected]
private theorem projected_pairing (S : Matrix ι ι ℂ) (v z : EuclideanSpace ℂ ι)
    (hS : S.IsHermitian) (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0) :
    ⟪projected v z,toEuclideanCLM (𝕜 := ℂ) S (projected v z)⟫_ℂ=
      ⟪z,toEuclideanCLM (𝕜 := ℂ) S z⟫_ℂ := by
  let T := toEuclideanCLM (𝕜 := ℂ) S
  have hs : (T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).IsSymmetric := by
    intro a b
    exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hS) a b
  have hz : ⟪v,T z⟫_ℂ=0 := by
    have he := (hs v z).symm
    change ⟪v,T z⟫_ℂ=⟪T v,z⟫_ℂ at he
    rw [he,hSv,inner_zero_left]
  change ⟪v,toEuclideanCLM (𝕜 := ℂ) S z⟫_ℂ=0 at hz
  simp only [projected,map_sub,map_smul,hSv,smul_zero,sub_zero,
    inner_sub_left,inner_smul_left,hz,mul_zero,sub_zero]
private theorem sandwich_annihilates (S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖=1) (hS : S=(1-(Matrix.vecMulVec (v).ofLp (star (v).ofLp)))*S*(1-(Matrix.vecMulVec (v).ofLp (star (v).ofLp)))) :
    toEuclideanCLM (𝕜 := ℂ) S v=0 := by
  have hQv : toEuclideanCLM (𝕜 := ℂ) (1-(Matrix.vecMulVec (v).ofLp (star (v).ofLp))) v=0 := by
    rw [projected_action]
    simp only [projected,inner_self_eq_norm_sq_to_K,hv]
    norm_num
  conv_lhs => rw [hS]
  simp only [map_mul,mul_apply_eq_comp,hQv,map_zero]
private theorem annihilates_sandwich (S : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι)
    (hS : S.IsHermitian) (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0) :
    S=(1-(Matrix.vecMulVec (v).ofLp (star (v).ofLp)))*S*(1-(Matrix.vecMulVec (v).ofLp (star (v).ofLp))) := by
  let T := toEuclideanCLM (𝕜 := ℂ) S
  have hs : (T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).IsSymmetric := by
    intro a b
    exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hS) a b
  have hi (z : EuclideanSpace ℂ ι) : ⟪v,T z⟫_ℂ=0 := by
    have he := (hs v z).symm
    change ⟪v,T z⟫_ℂ=⟪T v,z⟫_ℂ at he
    rw [he,hSv,inner_zero_left]
  have hm : toEuclideanCLM (𝕜 := ℂ) S=
      toEuclideanCLM (𝕜 := ℂ) ((1-(Matrix.vecMulVec (v).ofLp (star (v).ofLp)))*S*(1-(Matrix.vecMulVec (v).ofLp (star (v).ofLp)))) := by
    ext z
    simp only [map_mul,mul_apply_eq_comp]
    rw [projected_action,projected_action]
    simp only [projected,map_sub,map_smul,hSv,smul_zero,sub_zero]
    have hh : ⟪v,toEuclideanCLM (𝕜 := ℂ) S z⟫_ℂ=0 := hi z
    simp only [hh,zero_smul,sub_zero]
  exact (toEuclideanCLM (n := ι) (𝕜 := ℂ)).injective hm
private theorem trace_square_defect (X : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖=1) :
    let u := projected v (toEuclideanCLM (𝕜 := ℂ) X v)
    let w := projected v (toEuclideanCLM (𝕜 := ℂ) Xᴴ v)
    let S := (Matrix.vecMulVec (u).ofLp (star (u).ofLp))-(Matrix.vecMulVec (w).ofLp (star (w).ofLp))
    S=(1-(Matrix.vecMulVec (v).ofLp (star (v).ofLp)))*S*(1-(Matrix.vecMulVec (v).ofLp (star (v).ofLp))) ∧ defect2 X S v=((S*S).trace).re ∧
      (defect2 X S v=0 ↔ (Matrix.vecMulVec (u).ofLp (star (u).ofLp))=(Matrix.vecMulVec (w).ofLp (star (w).ofLp))) := by
  dsimp only
  let u := projected v (toEuclideanCLM (𝕜 := ℂ) X v)
  let w := projected v (toEuclideanCLM (𝕜 := ℂ) Xᴴ v)
  let S := (Matrix.vecMulVec (u).ofLp (star (u).ofLp))-(Matrix.vecMulVec (w).ofLp (star (w).ofLp))
  have hS : S.IsHermitian := (outer_hermitian u).sub (outer_hermitian w)
  have hu : ⟪u,v⟫_ℂ=0 := by rw [← inner_conj_symm,projected_orth v _ hv]; simp
  have hw : ⟪w,v⟫_ℂ=0 := by rw [← inner_conj_symm,projected_orth v _ hv]; simp
  have hSv : toEuclideanCLM (𝕜 := ℂ) S v=0 := by
    simp only [S,map_sub,_root_.sub_apply,outer_action,hu,hw,zero_smul,sub_self]
  have he : (S*S).trace=⟪u,toEuclideanCLM (𝕜 := ℂ) S u⟫_ℂ-
      ⟪w,toEuclideanCLM (𝕜 := ℂ) S w⟫_ℂ := by
    change (((Matrix.vecMulVec (u).ofLp (star (u).ofLp))-(Matrix.vecMulVec (w).ofLp (star (w).ofLp)))*S).trace = _
    rw [sub_mul,trace_sub,outer_pairing_trace,outer_pairing_trace]
  have hdef : defect2 X S v=((S*S).trace).re := by
    rw [he,Complex.sub_re]
    dsimp only [defect2,u,w]
    rw [projected_pairing S v _ hS hSv,projected_pairing S v _ hS hSv]
  refine ⟨annihilates_sandwich S v hS hSv,hdef,?_⟩
  constructor
  · intro hzero
    apply zero_pairing_outer_equal u w
    dsimp only [defect2] at hzero
    rw [← projected_pairing S v (toEuclideanCLM (𝕜 := ℂ) X v) hS hSv,
      ← projected_pairing S v (toEuclideanCLM (𝕜 := ℂ) Xᴴ v) hS hSv] at hzero
    exact hzero
  · intro hequal
    have hS0 : S=0 := sub_eq_zero.mpr hequal
    change defect2 X S v=0
    rw [hS0]
    simp [defect2]
private theorem edge_symmetry_forces_pairing_zero {n : ℕ} [NeZero n]
    (X S : Matrix (Fin n) (Fin n) ℂ) (hb : CompletionBound X)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖=1)
    (hS : S.IsHermitian) (hSv : toEuclideanCLM (𝕜 := ℂ) S v=0) : defect2 X S v=0 := by
  let L := max 1 ‖K X S‖
  have hL : 1 ≤ L := le_max_left _ _
  have hEn : ‖K X S‖ ≤ L := le_max_right _ _
  have ha := edge_symmetry_forces_defect_zero X hb v hv
  apply second_coefficient_zero (96*L) (1782*L^4) (defect2 X S v) (by linarith) (by positivity)
  intro t ht ht0
  have hh := edge_sum_bound X S v t L hv hS hSv hL hEn ht
  have hD : (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S).IsHermitian := ((outer_hermitian v).smul (isSelfAdjoint_iff.mpr rfl)).add hS
  have he : edgeMax (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))+edgeMin (K X (t • (Matrix.vecMulVec (v).ofLp (star (v).ofLp))+S))=0 :=
    edge_symmetry X _ hD hb
  simpa only [he,ha,zero_div,zero_add,zero_sub,abs_neg] using hh
private theorem completion_bound_projected_outer {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (hb : CompletionBound X)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖=1) :
    (Matrix.vecMulVec ((projected v (toEuclideanCLM (𝕜 := ℂ) X v))).ofLp (star ((projected v (toEuclideanCLM (𝕜 := ℂ) X v))).ofLp))=
      (Matrix.vecMulVec ((projected v (toEuclideanCLM (𝕜 := ℂ) Xᴴ v))).ofLp (star ((projected v (toEuclideanCLM (𝕜 := ℂ) Xᴴ v))).ofLp)) := by
  let u := projected v (toEuclideanCLM (𝕜 := ℂ) X v)
  let w := projected v (toEuclideanCLM (𝕜 := ℂ) Xᴴ v)
  let S := (Matrix.vecMulVec (u).ofLp (star (u).ofLp))-(Matrix.vecMulVec (w).ofLp (star (w).ofLp))
  have hS : S.IsHermitian := (outer_hermitian u).sub (outer_hermitian w)
  have hcert := trace_square_defect X v hv
  have hSv : toEuclideanCLM (𝕜 := ℂ) S v=0 :=
    sandwich_annihilates S v hv hcert.1
  have hb0 := edge_symmetry_forces_pairing_zero X S hb v hv hS hSv
  exact hcert.2.2.mp hb0
theorem result : claim := by
  intro n hn X hb
  letI : NeZero n := ⟨by omega⟩
  have hNormal := completion_bound_normal X hb
  apply normal_unit_projected_essentially hn X hNormal
  intro v hv
  let vE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  have hh := completion_bound_projected_outer X hb vE hv
  rw [← projected_action,← projected_action] at hh
  exact hh
end
end D5.S3.Quantum.BlockNorm.EssentiallyHermitian
