/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unitary Weyl displacements, basis transport, and occupation splitting. -/

import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockOccupation
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace

namespace D5.S3.Quantum.Analysis.NullConeGravity.CCRFockWeyl

open CCRFockOccupation

private theorem norm_linearCombination_eq {J X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (v : J → X) (w : J → Y) (hgram : ∀ i j, ⟪w i, w j⟫_ℂ = ⟪v i, v j⟫_ℂ)
    (c : J →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖ := by
  have h : ⟪Finsupp.linearCombination ℂ w c, Finsupp.linearCombination ℂ w c⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ v c, Finsupp.linearCombination ℂ v c⟫_ℂ := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hgram]
  simp only [inner_self_eq_norm_sq_to_K] at h
  have hs : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
      ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
    norm_nonneg (Finsupp.linearCombination ℂ v c)]

private def extendGram {J X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (v : J → X) (w : J → Y) (hgram : ∀ i j, ⟪w i, w j⟫_ℂ = ⟪v i, v j⟫_ℂ)
    (hv : Dense (Submodule.span ℂ (Set.range v) : Set X))
    (hw : Dense (Submodule.span ℂ (Set.range w) : Set Y)) : X ≃ₗᵢ[ℂ] Y :=
  (LinearEquiv.refl ℂ (J →₀ ℂ)).extendOfIsometry
    (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w)
    (by simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hv)
    (by simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hw)
    (norm_linearCombination_eq v w hgram)

private theorem extendGram_apply {J X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (v : J → X) (w : J → Y) (hgram : ∀ i j, ⟪w i, w j⟫_ℂ = ⟪v i, v j⟫_ℂ)
    (hv : Dense (Submodule.span ℂ (Set.range v) : Set X))
    (hw : Dense (Submodule.span ℂ (Set.range w) : Set Y)) (j : J) :
    extendGram v w hgram hv hw (v j) = w j := by
  unfold extendGram
  simpa only [LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul] using
    LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (J →₀ ℂ))
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w)
      (by simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hv)
      (by simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hw)
      (norm_linearCombination_eq v w hgram) (Finsupp.single j 1)

variable {I I₁ I₂ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem fockExponential_ext {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (b : HilbertBasis I ℂ H) (f g : BosonFock I →L[ℂ] Y)
    (h : ∀ z, f (fockExponential b z) = g (fockExponential b z)) : f = g := by
  apply ContinuousLinearMap.ext
  refine (fockExponential_dense_span b).induction ?_ (isClosed_eq f.continuous g.continuous)
  exact LinearMap.eqOn_span (f := f.toLinearMap) (g := g.toLinearMap)
    (by rintro x ⟨z, rfl⟩; exact h z)

private def weylExponent (z w : H) : ℂ :=
  -(‖z‖ : ℂ) ^ 2 / 2 - ⟪z, w⟫_ℂ

private def weylImage (b : HilbertBasis I ℂ H) (z w : H) : BosonFock I :=
  Complex.exp (weylExponent z w) • fockExponential b (z + w)

private theorem inner_self_complex (z : H) :
    ⟪z, z⟫_ℂ = (‖z‖ : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K z

private theorem weylImage_inner (b : HilbertBasis I ℂ H) (z u v : H) :
    ⟪weylImage b z u, weylImage b z v⟫_ℂ = ⟪fockExponential b u, fockExponential b v⟫_ℂ := by
  simp only [weylImage, inner_smul_left, inner_smul_right, fockExponential_inner,
    ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [weylExponent, map_sub, map_div₀, map_neg, map_pow, map_ofNat, Complex.conj_ofReal,
    inner_conj_symm, inner_add_left, inner_add_right, inner_self_complex]
  ring

private theorem weylImage_dense (b : HilbertBasis I ℂ H) (z : H) :
    Dense (Submodule.span ℂ (Set.range (weylImage b z)) : Set (BosonFock I)) := by
  apply (fockExponential_dense_span b).mono
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, rfl⟩
  let c := Complex.exp (weylExponent z (w - z))
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have hmem : weylImage b z (w - z) ∈ Submodule.span ℂ (Set.range (weylImage b z)) :=
    Submodule.subset_span ⟨w - z, rfl⟩
  have hw : z + (w - z) = w := by abel
  have hm := Submodule.smul_mem _ c⁻¹ hmem
  change c⁻¹ • (c • fockExponential b (z + (w - z))) ∈ _ at hm
  change fockExponential b w ∈ Submodule.span ℂ (Set.range (weylImage b z))
  simpa only [hw, smul_smul, inv_mul_cancel₀ hc, one_smul] using hm

/-- Unitary displacement for the complex inner product conjugate-linear in its first argument. -/
def fockWeyl (b : HilbertBasis I ℂ H) (z : H) : BosonFock I ≃ₗᵢ[ℂ] BosonFock I :=
  extendGram (fockExponential b) (weylImage b z) (weylImage_inner b z)
    (fockExponential_dense_span b) (weylImage_dense b z)

theorem fockWeyl_exponential (b : HilbertBasis I ℂ H) (z w : H) :
    fockWeyl b z (fockExponential b w) =
      Complex.exp (-(‖z‖ : ℂ) ^ 2 / 2 - ⟪z, w⟫_ℂ) • fockExponential b (z + w) :=
  extendGram_apply _ _ _ _ _ w

theorem fockWeyl_zero (b : HilbertBasis I ℂ H) :
    fockWeyl b 0 = LinearIsometryEquiv.refl ℂ (BosonFock I) := by
  have h := fockExponential_ext b (fockWeyl b 0).toContinuousLinearEquiv.toContinuousLinearMap
    (ContinuousLinearMap.id ℂ (BosonFock I)) (fun w => by
      change fockWeyl b 0 (fockExponential b w) = fockExponential b w
      simp [fockWeyl_exponential])
  apply LinearIsometryEquiv.ext
  intro ψ
  exact DFunLike.congr_fun h ψ

private theorem weylExponent_add (z w u : H) :
    weylExponent w u + weylExponent z (w + u) =
      -(Complex.I * (⟪z, w⟫_ℂ).im) + weylExponent (z + w) u := by
  have him : (⟪w, z⟫_ℂ - ⟪z, w⟫_ℂ) / 2 = -(Complex.I * (⟪z, w⟫_ℂ).im) := by
    have hre : (⟪w, z⟫_ℂ).re = (⟪z, w⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) w z
    have him : (⟪w, z⟫_ℂ).im = -(⟪z, w⟫_ℂ).im := inner_im_symm (𝕜 := ℂ) w z
    apply Complex.ext <;> simp [Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.mul_re, Complex.mul_im, hre, him]
    ring
  simp only [weylExponent, ← inner_self_complex, inner_add_left, inner_add_right]
  linear_combination him

/-- With `σ(z,w) = 2 * Im ⟪z,w⟫`, the multiplier is `exp(-iσ(z,w)/2)`. -/
theorem fockWeyl_mul (b : HilbertBasis I ℂ H) (z w : H) (ψ : BosonFock I) :
    fockWeyl b z (fockWeyl b w ψ) =
      Complex.exp (-(Complex.I * (⟪z, w⟫_ℂ).im)) • fockWeyl b (z + w) ψ := by
  let lhs := (fockWeyl b z).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fockWeyl b w).toContinuousLinearEquiv.toContinuousLinearMap
  let rhs := Complex.exp (-(Complex.I * (⟪z, w⟫_ℂ).im)) •
    (fockWeyl b (z + w)).toContinuousLinearEquiv.toContinuousLinearMap
  have h := fockExponential_ext b lhs rhs (fun u => by
    change fockWeyl b z (fockWeyl b w (fockExponential b u)) =
      Complex.exp (-(Complex.I * (⟪z, w⟫_ℂ).im)) • fockWeyl b (z + w) (fockExponential b u)
    simp only [fockWeyl_exponential, map_smul, smul_smul, ← Complex.exp_add, add_assoc]
    change Complex.exp (weylExponent w u + weylExponent z (w + u)) •
      fockExponential b (z + (w + u)) =
        Complex.exp (-(Complex.I * (⟪z, w⟫_ℂ).im) + weylExponent (z + w) u) •
          fockExponential b (z + (w + u))
    rw [weylExponent_add])
  exact DFunLike.congr_fun h ψ

theorem fockWeyl_symm (b : HilbertBasis I ℂ H) (z : H) :
    (fockWeyl b z).symm = fockWeyl b (-z) := by
  apply LinearIsometryEquiv.ext
  intro ψ
  apply (fockWeyl b z).injective
  rw [LinearIsometryEquiv.apply_symm_apply, fockWeyl_mul]
  simp [inner_neg_right, ← Complex.ofReal_pow, fockWeyl_zero]

theorem fockWeyl_vacuum_inner (b : HilbertBasis I ℂ H) (z : H) :
    ⟪fockVacuum I, fockWeyl b z (fockVacuum I)⟫_ℂ = Complex.exp (-(‖z‖ : ℂ) ^ 2 / 2) := by
  rw [← fockExponential_zero b, fockWeyl_exponential, inner_smul_right, fockExponential_inner]
  simp

theorem fockWeyl_strongContinuous (b : HilbertBasis I ℂ H) (ψ : BosonFock I) :
    Continuous (fun z => fockWeyl b z ψ) := by
  have hspan : ∀ ξ ∈ Submodule.span ℂ (Set.range (fockExponential b)),
      Continuous (fun z => fockWeyl b z ξ) := by
    intro ξ hξ
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hξ
    · rintro _ ⟨w, rfl⟩
      simp only [fockWeyl_exponential]
      exact (by fun_prop : Continuous (fun z : H => Complex.exp (-(‖z‖ : ℂ) ^ 2 / 2 - ⟪z, w⟫_ℂ))).smul
        ((fockExponential_continuous b).comp (by fun_prop))
    · simpa only [map_zero] using (continuous_const : Continuous (fun _ : H => (0 : BosonFock I)))
    · intro x y _ _ hx hy
      simpa only [map_add] using hx.fun_add hy
    · intro c x _ hx
      simpa only [map_smul] using continuous_const.fun_smul hx
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨ξ, hξ, hmem⟩ := Metric.dense_iff.mp (fockExponential_dense_span b) ψ
    (ε / 3) (by positivity)
  change dist ξ ψ < ε / 3 at hξ
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (hspan ξ hmem).continuousAt (ε / 3)
    (by positivity)
  refine ⟨δ, hδ, fun w hw => ?_⟩
  have h₁ := dist_triangle (fockWeyl b w ψ) (fockWeyl b w ξ) (fockWeyl b z ψ)
  have h₂ := dist_triangle (fockWeyl b w ξ) (fockWeyl b z ξ) (fockWeyl b z ψ)
  rw [(fockWeyl b w).isometry.dist_eq, dist_comm ψ ξ] at h₁
  rw [(fockWeyl b z).isometry.dist_eq] at h₂
  have h₃ : dist (fockWeyl b w ξ) (fockWeyl b z ξ) < ε / 3 := hnear hw
  linarith

/-- Transport between occupation models associated to two bases of the same one-particle space. -/
def fockBasisChange (b₁ : HilbertBasis I₁ ℂ H) (b₂ : HilbertBasis I₂ ℂ H) :
    BosonFock I₁ ≃ₗᵢ[ℂ] BosonFock I₂ :=
  extendGram (fockExponential b₁) (fockExponential b₂) (by simp [fockExponential_inner])
    (fockExponential_dense_span b₁) (fockExponential_dense_span b₂)

theorem fockBasisChange_exponential (b₁ : HilbertBasis I₁ ℂ H) (b₂ : HilbertBasis I₂ ℂ H) (z : H) :
    fockBasisChange b₁ b₂ (fockExponential b₁ z) = fockExponential b₂ z :=
  extendGram_apply _ _ _ _ _ z

theorem fockBasisChange_weyl (b₁ : HilbertBasis I₁ ℂ H) (b₂ : HilbertBasis I₂ ℂ H)
    (z : H) (ψ : BosonFock I₁) :
    fockBasisChange b₁ b₂ (fockWeyl b₁ z ψ) = fockWeyl b₂ z (fockBasisChange b₁ b₂ ψ) := by
  let U := (fockBasisChange b₁ b₂).toContinuousLinearEquiv.toContinuousLinearMap
  let W₁ := (fockWeyl b₁ z).toContinuousLinearEquiv.toContinuousLinearMap
  let W₂ := (fockWeyl b₂ z).toContinuousLinearEquiv.toContinuousLinearMap
  have h := fockExponential_ext b₁ (U.comp W₁) (W₂.comp U) (fun w => by
    change fockBasisChange b₁ b₂ (fockWeyl b₁ z (fockExponential b₁ w)) =
      fockWeyl b₂ z (fockBasisChange b₁ b₂ (fockExponential b₁ w))
    simp only [fockWeyl_exponential, fockBasisChange_exponential, map_smul])
  exact DFunLike.congr_fun h ψ

section SumSplit

private abbrev occupationUnsplit :
    Occupation I₂ × Occupation I₁ ≃ Occupation (I₁ ⊕ I₂) :=
  (Equiv.prodComm _ _).trans Finsupp.sumFinsuppEquivProdFinsupp.symm

private theorem lp_norm_sq {J E : Type*} [NormedAddCommGroup E]
    (v : lp (fun _ : J => E) 2) : ‖v‖ ^ 2 = ∑' j, ‖v j‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Nat.cast_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v

private theorem lp_summable_norm_sq {J E : Type*} [NormedAddCommGroup E]
    (v : lp (fun _ : J => E) 2) : Summable (fun j => ‖v j‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Nat.cast_ofNat, Real.rpow_two] using
    (lp.memℓp v).summable (by norm_num)

private theorem memℓp_two_of_summable {J E : Type*} [NormedAddCommGroup E]
    {v : J → E} (h : Summable (fun j => ‖v j‖ ^ 2)) : Memℓp v 2 :=
  memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Nat.cast_ofNat, Real.rpow_two] using h)

private theorem split_summable (ψ : BosonFock (I₁ ⊕ I₂)) :
    Summable (fun α : Occupation I₂ × Occupation I₁ => ‖ψ (occupationUnsplit α)‖ ^ 2) :=
  occupationUnsplit.summable_iff.mpr (lp_summable_norm_sq ψ)

private def fockSplitFiber (ψ : BosonFock (I₁ ⊕ I₂)) (β : Occupation I₂) : BosonFock I₁ :=
  ⟨fun α => ψ (α.sumElim β),
    memℓp_two_of_summable (((summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp
      (split_summable ψ)).1 β)⟩

private def fockSplitTo (ψ : BosonFock (I₁ ⊕ I₂)) :
    lp (fun _ : Occupation I₂ => BosonFock I₁) 2 :=
  ⟨fockSplitFiber ψ, memℓp_two_of_summable (by
    simp_rw [lp_norm_sq]
    exact ((summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp (split_summable ψ)).2)⟩

private def fockSplitFrom (ψ : lp (fun _ : Occupation I₂ => BosonFock I₁) 2) :
    BosonFock (I₁ ⊕ I₂) :=
  ⟨fun α => ψ (occupationUnsplit.symm α).1 (occupationUnsplit.symm α).2,
    memℓp_two_of_summable (occupationUnsplit.summable_iff.mp (by
      simp only [Function.comp_def, Equiv.symm_apply_apply]
      refine (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
        ⟨fun β => lp_summable_norm_sq (ψ β), ?_⟩
      simpa only [← lp_norm_sq] using lp_summable_norm_sq ψ))⟩

/-- Split each occupation into its left and right occupations, with the right occupation
indexing the outer Hilbert sum. -/
def fockSumSplit (I₁ I₂ : Type*) :
    BosonFock (I₁ ⊕ I₂) ≃ₗᵢ[ℂ] lp (fun _ : Occupation I₂ => BosonFock I₁) 2 where
  toFun := fockSplitTo
  invFun := fockSplitFrom
  left_inv ψ := by
    apply lp.ext
    funext α
    change ψ (occupationUnsplit (occupationUnsplit.symm α)) = ψ α
    rw [Equiv.apply_symm_apply]
  right_inv ψ := by
    apply lp.ext
    funext β
    apply lp.ext
    funext α
    change ψ (occupationUnsplit.symm (occupationUnsplit (β, α))).1
      (occupationUnsplit.symm (occupationUnsplit (β, α))).2 = ψ β α
    rw [Equiv.symm_apply_apply]
  map_add' ψ χ := by
    apply lp.ext
    funext β
    apply lp.ext
    funext α
    rfl
  map_smul' c ψ := by
    apply lp.ext
    funext β
    apply lp.ext
    funext α
    rfl
  norm_map' ψ := by
    suffices h : ‖fockSplitTo ψ‖ ^ 2 = ‖ψ‖ ^ 2 by
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
    rw [lp_norm_sq, lp_norm_sq ψ]
    simp_rw [fockSplitTo, lp_norm_sq]
    have hs := split_summable ψ
    exact (hs.tsum_prod' (fun β => lp_summable_norm_sq (fockSplitFiber ψ β))).symm.trans
      (occupationUnsplit.tsum_eq (fun α => ‖ψ α‖ ^ 2))

/-- The entry at a left and a right occupation is the entry at their disjoint union. -/
theorem fockSumSplit_apply (ψ : BosonFock (I₁ ⊕ I₂)) (β : Occupation I₂) (α : Occupation I₁) :
    fockSumSplit I₁ I₂ ψ β α = ψ (α.sumElim β) := rfl

variable {K K₁ : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]

/-- Restrict the one-particle coordinates to the left index set and reconstruct in the left space. -/
def fockOneParticleLeft (b : HilbertBasis (I₁ ⊕ I₂) ℂ K) (b₁ : HilbertBasis I₁ ℂ K₁)
    (z : K) : K₁ :=
  b₁.repr.symm ⟨fun i => b.repr z (Sum.inl i),
    memℓp_two_of_summable ((lp_summable_norm_sq (b.repr z)).comp_injective Sum.inl_injective)⟩

theorem fockOneParticleLeft_repr (b : HilbertBasis (I₁ ⊕ I₂) ℂ K) (b₁ : HilbertBasis I₁ ℂ K₁)
    (z : K) (i : I₁) : b₁.repr (fockOneParticleLeft b b₁ z) i = b.repr z (Sum.inl i) := by
  simp [fockOneParticleLeft]

private theorem fockOneParticleLeft_add (b : HilbertBasis (I₁ ⊕ I₂) ℂ K)
    (b₁ : HilbertBasis I₁ ℂ K₁) (z w : K) :
    fockOneParticleLeft b b₁ (z + w) =
      fockOneParticleLeft b b₁ z + fockOneParticleLeft b b₁ w := by
  apply b₁.repr.injective
  apply lp.ext
  funext i
  simp only [map_add, lp.coeFn_add, Pi.add_apply, fockOneParticleLeft_repr]

private theorem fockOneParticleLeft_inner (b : HilbertBasis (I₁ ⊕ I₂) ℂ K)
    (b₁ : HilbertBasis I₁ ℂ K₁) (z : K) (hz : ∀ j : I₂, b.repr z (Sum.inr j) = 0) (w : K) :
    ⟪fockOneParticleLeft b b₁ z, fockOneParticleLeft b b₁ w⟫_ℂ = ⟪z, w⟫_ℂ := by
  rw [← b.repr.inner_map_map, lp.inner_eq_tsum]
  let f : I₁ ⊕ I₂ → ℂ := fun i => ⟪b.repr z i, b.repr w i⟫_ℂ
  have hleft : HasSum (f ∘ Sum.inl) ⟪fockOneParticleLeft b b₁ z, fockOneParticleLeft b b₁ w⟫_ℂ := by
    rw [← b₁.repr.inner_map_map]
    simpa only [f, Function.comp_def, fockOneParticleLeft_repr] using
      lp.hasSum_inner (b₁.repr (fockOneParticleLeft b b₁ z)) (b₁.repr (fockOneParticleLeft b b₁ w))
  have hright : HasSum (f ∘ Sum.inr) 0 := by
    simp [f, Function.comp_def, hz]
  simpa only [f, add_zero] using (hleft.sum hright).tsum_eq.symm

private theorem fockOneParticleLeft_norm (b : HilbertBasis (I₁ ⊕ I₂) ℂ K)
    (b₁ : HilbertBasis I₁ ℂ K₁) (z : K) (hz : ∀ j : I₂, b.repr z (Sum.inr j) = 0) :
    ‖fockOneParticleLeft b b₁ z‖ = ‖z‖ := by
  have h := fockOneParticleLeft_inner b b₁ z hz z
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact_mod_cast h

private def fockRightCoeff (b : HilbertBasis (I₁ ⊕ I₂) ℂ K) (z : K) (β : Occupation I₂) : ℂ :=
  ∏ j ∈ β.support, (b.repr z (Sum.inr j)) ^ (β j) / (Real.sqrt ((β j).factorial : ℝ) : ℂ)

private theorem fockSumSplit_exponential (b : HilbertBasis (I₁ ⊕ I₂) ℂ K)
    (b₁ : HilbertBasis I₁ ℂ K₁) (z : K) (β : Occupation I₂) :
    fockSumSplit I₁ I₂ (fockExponential b z) β =
      fockRightCoeff b z β • fockExponential b₁ (fockOneParticleLeft b b₁ z) := by
  apply lp.ext
  funext α
  rw [fockSumSplit_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, fockExponential_apply,
    fockRightCoeff, fockOneParticleLeft_repr, Finsupp.sumElim_support, Finset.prod_disjSum,
    Finsupp.sumElim_inl, Finsupp.sumElim_inr]
  exact mul_comm _ _

/-- A displacement supported on the left acts on each left Fock vector in the occupation split. -/
theorem fockSumSplit_weyl (b : HilbertBasis (I₁ ⊕ I₂) ℂ K) (b₁ : HilbertBasis I₁ ℂ K₁)
    (z : K) (hz : ∀ j : I₂, b.repr z (Sum.inr j) = 0)
    (ψ : BosonFock (I₁ ⊕ I₂)) (β : Occupation I₂) :
    fockSumSplit I₁ I₂ (fockWeyl b z ψ) β =
      fockWeyl b₁ (fockOneParticleLeft b b₁ z) (fockSumSplit I₁ I₂ ψ β) := by
  let fiber : BosonFock (I₁ ⊕ I₂) →L[ℂ] BosonFock I₁ :=
    (lp.evalCLM ℂ (fun _ : Occupation I₂ => BosonFock I₁) 2 β).comp
      (fockSumSplit I₁ I₂).toLinearIsometry.toContinuousLinearMap
  let leftAction := (fockWeyl b₁ (fockOneParticleLeft b b₁ z)).toLinearIsometry.toContinuousLinearMap
  let fullAction := (fockWeyl b z).toLinearIsometry.toContinuousLinearMap
  have h : fiber.comp fullAction = leftAction.comp fiber := by
    apply fockExponential_ext b
    intro w
    change fockSumSplit I₁ I₂ (fockWeyl b z (fockExponential b w)) β =
      fockWeyl b₁ (fockOneParticleLeft b b₁ z) (fockSumSplit I₁ I₂ (fockExponential b w) β)
    rw [fockWeyl_exponential, map_smul]
    change (_ : ℂ) • fockSumSplit I₁ I₂ (fockExponential b (z + w)) β = _
    rw [fockSumSplit_exponential b b₁ (z + w) β, fockSumSplit_exponential b b₁ w β, map_smul,
      fockWeyl_exponential, fockOneParticleLeft_inner b b₁ z hz,
      fockOneParticleLeft_norm b b₁ z hz, fockOneParticleLeft_add]
    have hright : fockRightCoeff b (z + w) β = fockRightCoeff b w β := by
      simp [fockRightCoeff, map_add, hz]
    rw [hright, smul_comm]
  exact DFunLike.congr_fun h ψ

end SumSplit

end D5.S3.Quantum.Analysis.NullConeGravity.CCRFockWeyl
