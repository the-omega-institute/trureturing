/- GID: D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The noisy qutrit Werner–Holevo channel has a GKSL logarithm only at zero noise. -/

import D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
import D5.S3.Quantum.Dynamics.DissipatorSpectralDiskRefutation
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity

/-! The noisy qutrit Werner–Holevo channel is a GKSL exponential exactly at zero noise
on the interval `[0, 2 / 3]`. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator

attribute [local instance] LieRing.ofAssociativeRing

open D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace (trace_standard)

namespace D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding

/-- The noisy Werner–Holevo map on qutrit matrices. -/
def wernerHolevo (x : ℝ) :
    Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  (1 - (x : ℂ)) • LinearMap.id -
    ((x : ℂ) / 2) • (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ).toLinearMap +
    ((x : ℂ) / 2) • (Matrix.traceLinearMap (Fin 3) ℂ ℂ).smulRight 1

/-- A generator with a Hermitian Hamiltonian and finitely many GKSL jump matrices. -/
def IsGKSLGenerator (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) : Prop :=
  ∃ (m : ℕ) (H : Matrix (Fin 3) (Fin 3) ℂ)
    (V : Fin m → Matrix (Fin 3) (Fin 3) ℂ), H.IsHermitian ∧
      ∀ X, G X = -Complex.I • (H * X - X * H) +
        ∑ k, (V k * X * (V k)ᴴ - (1 / 2 : ℂ) •
          ((V k)ᴴ * V k * X + X * ((V k)ᴴ * V k)))

/-- The ordinary exponential in the matrix-unit basis, transported back to matrices. -/
def generatorExp (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) :
    Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  (LinearMap.toMatrixAlgEquiv (Matrix.stdBasis ℂ (Fin 3) (Fin 3))).symm
    (NormedSpace.exp
      (LinearMap.toMatrixAlgEquiv (Matrix.stdBasis ℂ (Fin 3) (Fin 3)) G))

/-- Embeddability on the source's remaining parameter interval. -/
def claim : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc 0 (2 / 3 : ℝ) →
    ((∃ G, IsGKSLGenerator G ∧ generatorExp G = wernerHolevo x) ↔ x = 0)

private def symmetricProjection : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  (1 / 2 : ℂ) • (LinearMap.id +
    (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ).toLinearMap) -
    (1 / 3 : ℂ) • (Matrix.traceLinearMap (Fin 3) ℂ ℂ).smulRight 1

private def antisymmetricProjection : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  (1 / 2 : ℂ) • (LinearMap.id -
    (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ).toLinearMap)

private def symmetricTrace (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) : ℝ :=
  (LinearMap.trace ℂ _ (G.comp symmetricProjection)).re

private def antisymmetricTrace (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) : ℝ :=
  (LinearMap.trace ℂ _ (G.comp antisymmetricProjection)).re

private theorem zero_gksl :
    IsGKSLGenerator (0 : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) := by
  refine ⟨0, 0, Fin.elim0, Matrix.isHermitian_zero, ?_⟩
  intro X
  simp

private theorem wernerHolevo_zero : wernerHolevo 0 = LinearMap.id := by
  unfold wernerHolevo
  simp

private theorem generatorExp_zero :
    generatorExp (0 : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) = LinearMap.id := by
  unfold generatorExp
  simp only [map_zero, NormedSpace.exp_zero, map_one]
  rfl

private theorem generatorExp_injective
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) :
    Function.Injective (generatorExp G) := by
  have hunit : IsUnit (generatorExp G) :=
    (Matrix.isUnit_exp _).map
      (LinearMap.toMatrixAlgEquiv (Matrix.stdBasis ℂ (Fin 3) (Fin 3))).symm.toMonoidHom
  exact ((Module.End.isUnit_iff _).mp hunit).1

private theorem exponential_eigenvector (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ))
    (v : Matrix (Fin 3) (Fin 3) ℂ) (μ : ℂ) (hv : G v = μ • v) :
    generatorExp G v = Complex.exp μ • v := by
  let b := Matrix.stdBasis ℂ (Fin 3) (Fin 3)
  have heig : LinearMap.toMatrix b b G *ᵥ b.repr v = μ • b.repr v := by
    rw [LinearMap.toMatrix_mulVec_repr, hv, map_smul]
    rfl
  have he := D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity.exp_mulVec_of_eigenvector
    (LinearMap.toMatrix b b G) (b.repr v) μ heig
  apply b.equivFun.injective
  change ⇑(b.repr (generatorExp G v)) = ⇑(b.repr (Complex.exp μ • v))
  rw [← LinearMap.toMatrix_mulVec_repr b b, map_smul]
  have hmatrix : LinearMap.toMatrix b b (generatorExp G) =
      NormedSpace.exp (LinearMap.toMatrix b b G) :=
    (LinearMap.toMatrixAlgEquiv b).apply_symm_apply _
  rw [hmatrix]
  exact he

private theorem projected_log_trace
    (G P : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ))
    (hP : IsIdempotentElem P) (hcomm : Commute G P)
    (b : ℝ) (hb : 0 < b) (hexp : generatorExp G * P = (b : ℂ) • P) :
    (LinearMap.trace ℂ _ (G * P)).re = (LinearMap.trace ℂ _ P).re * Real.log b := by
  let W := LinearMap.range P
  let i : W →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ := W.subtype
  let p : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] W := P.rangeRestrict
  let F : Module.End ℂ W := p.comp (G.comp i)
  have hPi (v : W) : P (v : Matrix (Fin 3) (Fin 3) ℂ) = v :=
    (LinearMap.IsIdempotentElem.isProj_range P hP).map_id v v.property
  have hGi (v : W) : G (v : Matrix (Fin 3) (Fin 3) ℂ) = (F v : Matrix (Fin 3) (Fin 3) ℂ) := by
    change G v = P (G v)
    have hh := congrArg (fun T : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) => T v) hcomm.eq
    simpa only [Module.End.mul_apply, hPi] using hh
  have hroot (μ : ℂ) (hμ : μ ∈ F.charpoly.roots) : μ.re = Real.log b := by
    have heig : F.HasEigenvalue μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly F μ).mpr
        (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hv0 : (v : Matrix (Fin 3) (Fin 3) ℂ) ≠ 0 := by
      intro hz
      exact hv.2 (Subtype.ext hz)
    have hGeig : G (v : Matrix (Fin 3) (Fin 3) ℂ) = μ • (v : Matrix (Fin 3) (Fin 3) ℂ) := by
      rw [hGi]
      exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv.1)
    have he := exponential_eigenvector G (v : Matrix (Fin 3) (Fin 3) ℂ) μ hGeig
    have hbv := congrArg (fun T : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) => T v) hexp
    change generatorExp G (P v) = (b : ℂ) • P v at hbv
    rw [hPi] at hbv
    have hs : Complex.exp μ = (b : ℂ) := smul_left_injective ℂ hv0 (he.symm.trans hbv)
    have hn := congrArg norm hs
    rw [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at hn
    exact (Real.log_exp μ.re).symm.trans (congrArg Real.log hn)
  have hsplit : F.charpoly.Splits := IsAlgClosed.splits _
  have htr : (LinearMap.trace ℂ W F).re = (Module.finrank ℂ W : ℝ) * Real.log b := by
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits hsplit]
    change Complex.reAddGroupHom F.charpoly.roots.sum = _
    rw [map_multiset_sum]
    have hm : F.charpoly.roots.map Complex.reAddGroupHom =
        F.charpoly.roots.map (fun _ => Real.log b) := by
      apply Multiset.map_congr rfl
      intro μ hμ
      exact hroot μ hμ
    rw [hm]
    simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
    rw [← hsplit.natDegree_eq_card_roots, LinearMap.charpoly_natDegree]
  have hcyc : LinearMap.trace ℂ _ (G * P) = LinearMap.trace ℂ W F := by
    have hc := LinearMap.trace_comp_comm' p (G.comp i)
    change LinearMap.trace ℂ _ ((G.comp W.subtype).comp P.rangeRestrict) = _ at hc
    rw [LinearMap.comp_assoc, LinearMap.subtype_comp_rangeRestrict] at hc
    exact hc
  rw [hcyc, htr, (LinearMap.IsIdempotentElem.isProj_range P hP).trace]
  simp only [Complex.natCast_re]
  rfl

private theorem endpoint_kernel :
    ∃ X : Matrix (Fin 3) (Fin 3) ℂ,
      X ≠ 0 ∧ wernerHolevo (2 / 3) X = 0 := by
  refine ⟨Matrix.single 0 0 1 - Matrix.single 1 1 1, ?_, ?_⟩
  · intro h
    have := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℂ => X 0 0) h
    norm_num [Matrix.single] at this
  · ext i j
    unfold wernerHolevo Matrix.transposeLinearEquiv
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.trace, Matrix.single, Matrix.one_apply]

private theorem endpoint_not_exp
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) :
    generatorExp G ≠ wernerHolevo (2 / 3) := by
  intro h
  obtain ⟨X, hX, hkill⟩ := endpoint_kernel
  apply hX
  apply generatorExp_injective G
  rw [h, hkill, map_zero]

private def hamiltonianMap (H : Matrix (Fin 3) (Fin 3) ℂ) :
    Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  -Complex.I • LieAlgebra.ad ℂ (Matrix (Fin 3) (Fin 3) ℂ) H

private def dissipatorMap (V : Matrix (Fin 3) (Fin 3) ℂ) :
    Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) where
  toFun := D5.S3.Quantum.Dynamics.DissipatorSpectralDiskRefutation.dissipator V
  map_add' X Y := by
    simp only [D5.S3.Quantum.Dynamics.DissipatorSpectralDiskRefutation.dissipator,
      Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  map_smul' c X := by
    simp [D5.S3.Quantum.Dynamics.DissipatorSpectralDiskRefutation.dissipator,
      smul_smul, mul_comm, smul_sub]

private theorem sector_trace_hamiltonian (H : Matrix (Fin 3) (Fin 3) ℂ) :
    symmetricTrace (hamiltonianMap H) - 5 * antisymmetricTrace (hamiltonianMap H) = 0 := by
  unfold symmetricTrace antisymmetricTrace
  rw [trace_standard, trace_standard]
  unfold symmetricProjection antisymmetricProjection hamiltonianMap Matrix.transposeLinearEquiv
  simp [LieAlgebra.ad_apply, Ring.lie_def, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.single, Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  ring

private theorem sector_trace_dissipator (V : Matrix (Fin 3) (Fin 3) ℂ) :
    symmetricTrace (dissipatorMap V) - 5 * antisymmetricTrace (dissipatorMap V) =
      2 * (Complex.normSq (V 0 0 - V 1 1) + Complex.normSq (V 0 0 - V 2 2) +
        Complex.normSq (V 1 1 - V 2 2)) +
      3 * (Complex.normSq (V 0 1 + V 1 0) + Complex.normSq (V 0 2 + V 2 0) +
        Complex.normSq (V 1 2 + V 2 1)) := by
  unfold symmetricTrace antisymmetricTrace
  rw [trace_standard, trace_standard]
  unfold symmetricProjection antisymmetricProjection dissipatorMap
    D5.S3.Quantum.Dynamics.DissipatorSpectralDiskRefutation.dissipator Matrix.transposeLinearEquiv
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single,
    Matrix.one_apply, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  norm_num [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide,
    Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty]
  ring

private theorem gksl_trace_inequality
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (hG : IsGKSLGenerator G) :
    0 ≤ symmetricTrace G - 5 * antisymmetricTrace G := by
  obtain ⟨m, H, V, _, hform⟩ := hG
  have hG : G = hamiltonianMap H + ∑ k, dissipatorMap (V k) := by
    ext X i j
    unfold hamiltonianMap dissipatorMap
    simpa [LieAlgebra.ad_apply, Ring.lie_def,
      D5.S3.Quantum.Dynamics.DissipatorSpectralDiskRefutation.dissipator,
      Matrix.mul_assoc] using congrArg (fun Y => Y i j) (hform X)
  rw [hG]
  have hS : symmetricTrace (hamiltonianMap H + ∑ k, dissipatorMap (V k)) =
      symmetricTrace (hamiltonianMap H) + ∑ k, symmetricTrace (dissipatorMap (V k)) := by
    unfold symmetricTrace
    change (LinearMap.trace ℂ _
      ((hamiltonianMap H + ∑ k, dissipatorMap (V k)) * symmetricProjection)).re = _
    simp only [add_mul, Finset.sum_mul,
      map_add, map_sum, Complex.add_re, Complex.re_sum]
    simp only [Module.End.mul_eq_comp]
  have hA : antisymmetricTrace (hamiltonianMap H + ∑ k, dissipatorMap (V k)) =
      antisymmetricTrace (hamiltonianMap H) + ∑ k, antisymmetricTrace (dissipatorMap (V k)) := by
    unfold antisymmetricTrace
    change (LinearMap.trace ℂ _
      ((hamiltonianMap H + ∑ k, dissipatorMap (V k)) * antisymmetricProjection)).re = _
    simp only [add_mul, Finset.sum_mul,
      map_add, map_sum, Complex.add_re, Complex.re_sum]
    simp only [Module.End.mul_eq_comp]
  rw [hS, hA]
  have hham := sector_trace_hamiltonian H
  have hsum : 0 ≤ ∑ k, (symmetricTrace (dissipatorMap (V k)) -
      5 * antisymmetricTrace (dissipatorMap (V k))) := by
    apply Finset.sum_nonneg
    intro k _
    rw [sector_trace_dissipator]
    linarith [Complex.normSq_nonneg (V k 0 0 - V k 1 1),
      Complex.normSq_nonneg (V k 0 0 - V k 2 2),
      Complex.normSq_nonneg (V k 1 1 - V k 2 2),
      Complex.normSq_nonneg (V k 0 1 + V k 1 0),
      Complex.normSq_nonneg (V k 0 2 + V k 2 0),
      Complex.normSq_nonneg (V k 1 2 + V k 2 1)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linarith

private theorem generatorExp_commute
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) : Commute G (generatorExp G) := by
  unfold generatorExp
  apply (LinearMap.toMatrixAlgEquiv (Matrix.stdBasis ℂ (Fin 3) (Fin 3))).injective
  simp only [map_mul, AlgEquiv.apply_symm_apply]
  exact (Commute.refl _).exp_right.eq

private theorem gksl_trace_zero
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (hG : IsGKSLGenerator G)
    (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix.trace (G X) = 0 := by
  obtain ⟨m, H, V, _, hform⟩ := hG
  rw [hform]
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_sum,
    Matrix.trace_mul_comm H X, sub_self, smul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.trace_mul_cycle (V k) X (V k)ᴴ, Matrix.trace_mul_comm X ((V k)ᴴ * V k)]
  ring

private theorem wernerHolevo_one (x : ℝ) :
    wernerHolevo x (1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
  ext i j
  unfold wernerHolevo Matrix.transposeLinearEquiv
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.trace, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

private theorem generator_unital (x : ℝ) (hx : x ≠ 0)
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (hG : IsGKSLGenerator G)
    (hexp : generatorExp G = wernerHolevo x) : G 1 = 0 := by
  have hc := generatorExp_commute G
  rw [hexp] at hc
  have hfixed : wernerHolevo x (G 1) = G 1 := by
    have hh := congrArg (fun F : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) => F 1) hc.eq
    simpa only [Module.End.mul_apply, wernerHolevo_one] using hh.symm
  have ht := gksl_trace_zero G hG 1
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  ext i j
  have hij := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℂ => X i j) hfixed
  have hji := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℂ => X j i) hfixed
  change (1 - (x : ℂ)) * G 1 i j - ((x : ℂ) / 2) * G 1 j i +
    ((x : ℂ) / 2) * (Matrix.trace (G 1) * (1 : Matrix (Fin 3) (Fin 3) ℂ) i j) =
      G 1 i j at hij
  change (1 - (x : ℂ)) * G 1 j i - ((x : ℂ) / 2) * G 1 i j +
    ((x : ℂ) / 2) * (Matrix.trace (G 1) * (1 : Matrix (Fin 3) (Fin 3) ℂ) j i) =
      G 1 j i at hji
  rw [ht, zero_mul, mul_zero, add_zero] at hij hji
  have hz : (x : ℂ) * G 1 i j = 0 := by
    linear_combination (-4 / 3 : ℂ) * hij + (2 / 3 : ℂ) * hji
  exact (mul_eq_zero.mp hz).resolve_left hxC

private theorem generator_transpose (x : ℝ) (hx : x ≠ 0)
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (hG : IsGKSLGenerator G)
    (hexp : generatorExp G = wernerHolevo x) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    G Xᵀ = (G X)ᵀ := by
  have hc := generatorExp_commute G
  rw [hexp] at hc
  have hh := congrArg (fun F : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) => F X) hc.eq
  have h1 := generator_unital x hx G hG hexp
  have ht := gksl_trace_zero G hG X
  ext i j
  have hij := congrArg (fun Y : Matrix (Fin 3) (Fin 3) ℂ => Y i j) hh
  unfold wernerHolevo Matrix.transposeLinearEquiv at hij
  simp [ht, h1] at hij
  exact hij.resolve_right hx

private theorem generator_projection_commute (x : ℝ) (hx : x ≠ 0)
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (hG : IsGKSLGenerator G)
    (hexp : generatorExp G = wernerHolevo x) :
    Commute G symmetricProjection ∧ Commute G antisymmetricProjection := by
  have h1 := generator_unital x hx G hG hexp
  have ht := gksl_trace_zero G hG
  have hT := generator_transpose x hx G hG hexp
  constructor
  · ext X i j
    unfold symmetricProjection Matrix.transposeLinearEquiv
    simp [h1, ht, hT]
  · ext X i j
    unfold antisymmetricProjection Matrix.transposeLinearEquiv
    simp [hT]

private theorem symmetricProjection_idempotent : IsIdempotentElem symmetricProjection := by
  ext X i j
  unfold symmetricProjection Matrix.transposeLinearEquiv
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.trace, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

private theorem antisymmetricProjection_idempotent : IsIdempotentElem antisymmetricProjection := by
  ext X i j
  unfold antisymmetricProjection Matrix.transposeLinearEquiv
  fin_cases i <;> fin_cases j <;> norm_num <;> ring

private theorem symmetricProjection_trace : LinearMap.trace ℂ _ symmetricProjection = 5 := by
  rw [trace_standard]
  unfold symmetricProjection Matrix.transposeLinearEquiv
  norm_num [Matrix.trace, Fin.sum_univ_succ, Matrix.single, Matrix.one_apply]
  norm_num [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide,
    Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty]

private theorem antisymmetricProjection_trace :
    LinearMap.trace ℂ _ antisymmetricProjection = 3 := by
  rw [trace_standard]
  unfold antisymmetricProjection Matrix.transposeLinearEquiv
  norm_num [Fin.sum_univ_succ, Matrix.single]

private theorem wernerHolevo_symmetricProjection (x : ℝ) :
    wernerHolevo x * symmetricProjection = (1 - 3 * (x : ℂ) / 2) • symmetricProjection := by
  ext X i j
  unfold wernerHolevo symmetricProjection Matrix.transposeLinearEquiv
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.trace, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

private theorem wernerHolevo_antisymmetricProjection (x : ℝ) :
    wernerHolevo x * antisymmetricProjection = (1 - (x : ℂ) / 2) • antisymmetricProjection := by
  ext X i j
  unfold wernerHolevo antisymmetricProjection Matrix.transposeLinearEquiv
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.trace, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

private theorem spectral_traces (x : ℝ) (hx : 0 < x) (hx' : x < 2 / 3)
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ))
    (hG : IsGKSLGenerator G) (hexp : generatorExp G = wernerHolevo x) :
    symmetricTrace G = 5 * Real.log (1 - 3 * x / 2) ∧
      antisymmetricTrace G = 3 * Real.log (1 - x / 2) := by
  obtain ⟨hS, hA⟩ := generator_projection_commute x hx.ne' G hG hexp
  have hb : 0 < 1 - 3 * x / 2 := by linarith
  have hc : 0 < 1 - x / 2 := by linarith
  have hES : generatorExp G * symmetricProjection =
      ((1 - 3 * x / 2 : ℝ) : ℂ) • symmetricProjection := by
    rw [hexp, wernerHolevo_symmetricProjection]
    push_cast
    rfl
  have hEA : generatorExp G * antisymmetricProjection =
      ((1 - x / 2 : ℝ) : ℂ) • antisymmetricProjection := by
    rw [hexp, wernerHolevo_antisymmetricProjection]
    push_cast
    rfl
  have hTS := projected_log_trace G symmetricProjection symmetricProjection_idempotent
    hS (1 - 3 * x / 2) hb hES
  have hTA := projected_log_trace G antisymmetricProjection antisymmetricProjection_idempotent
    hA (1 - x / 2) hc hEA
  rw [symmetricProjection_trace] at hTS
  rw [antisymmetricProjection_trace] at hTA
  constructor
  · unfold symmetricTrace
    simpa [Module.End.mul_eq_comp] using hTS
  · unfold antisymmetricTrace
    simpa [Module.End.mul_eq_comp] using hTA

private theorem strict_log_inequality (x : ℝ) (hx : 0 < x) (hx' : x < 2 / 3) :
    5 * Real.log (1 - 3 * x / 2) < 15 * Real.log (1 - x / 2) := by
  have hb : 0 < 1 - 3 * x / 2 := by linarith
  have hpow : 1 - 3 * x / 2 < (1 - x / 2) ^ 3 := by
    have h := one_add_mul_self_lt_rpow_one_add
      (s := -(x / 2)) (p := (3 : ℕ)) (by linarith) (by linarith) (by norm_num)
    rw [Real.rpow_natCast] at h
    simpa only [Nat.cast_ofNat, mul_neg,
      ← mul_div_assoc, ← sub_eq_add_neg] using h
  have hlog := Real.log_lt_log hb hpow
  rw [Real.log_pow] at hlog
  linarith

private theorem interior_not_exp (x : ℝ) (hx : 0 < x) (hx' : x < 2 / 3)
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (hG : IsGKSLGenerator G) :
    generatorExp G ≠ wernerHolevo x := by
  intro hexp
  obtain ⟨hS, hA⟩ := spectral_traces x hx hx' G hG hexp
  have hpos := gksl_trace_inequality G hG
  rw [hS, hA] at hpos
  have hneg := strict_log_inequality x hx hx'
  linarith

/-- Exactly zero noise is the exponential of a GKSL generator on `[0, 2/3]`. -/
theorem result : claim := by
  intro x hx
  constructor
  · rintro ⟨G, hG, hexp⟩
    by_contra hzero
    have hpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · exact interior_not_exp x hpos hlt G hG hexp
    · subst x
      exact endpoint_not_exp G hexp
  · intro hzero
    subst x
    exact ⟨0, zero_gksl, generatorExp_zero.trans wernerHolevo_zero.symm⟩

end D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding
