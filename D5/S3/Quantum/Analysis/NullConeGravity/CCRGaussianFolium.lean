/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian folium membership from the restriction of a pure Fock squeeze. -/

import D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState
import D5.S3.Quantum.Analysis.NullConeGravity.CCRConjugation
import D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianExtension
import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockOccupation
import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockWeyl
import D5.S3.Quantum.Analysis.NullConeGravity.CCRSqueezeInfinite
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondEq71Trace4D
import Mathlib.Data.Finsupp.Encodable

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace.Completion ContinuousLinearMap HilbertSchmidt NullConeGravity

namespace D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianFolium

open CCRWeylState CCRGaussianExtension CCRFockOccupation CCRFockWeyl CCRSqueezeInfinite

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {S A : Type*} [AddCommGroup S] [Module ℝ S]
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {σ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ}

private theorem countable_basis {K J : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [TopologicalSpace.SeparableSpace K]
    (b : HilbertBasis J ℂ K) : Countable J := by
  let : InnerProductSpace ℝ K := InnerProductSpace.rclikeToReal ℂ K
  let s : J → Set K := fun i => Metric.ball (b i) (1 / 2)
  have hd : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hdist : dist (b i) (b j) < 1 := by
      have h1 := Metric.mem_ball.mp hzi
      have h2 := Metric.mem_ball.mp hzj
      rw [dist_comm] at h1
      linarith [dist_triangle (b i) z (b j)]
    have ho : ⟪b i, b j⟫_ℝ = 0 := by
      change (⟪b i, b j⟫_ℂ).re = 0
      rw [b.orthonormal.2 hij]
      rfl
    have hs := norm_sub_sq_eq_norm_sq_add_norm_sq_real ho
    rw [b.orthonormal.1 i, b.orthonormal.1 j, ← dist_eq_norm] at hs
    nlinarith [dist_nonneg (x := b i) (y := b j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)

private theorem exists_splitBasis (E : Submodule ℂ H) [CompleteSpace E]
    {J K : Type*} (b : HilbertBasis J ℂ E) (c : HilbertBasis K ℂ Eᗮ) :
    ∃ d : HilbertBasis (J ⊕ K) ℂ H,
      (∀ i, d (Sum.inl i) = (b i : H)) ∧ (∀ i, d (Sum.inr i) = (c i : H)) := by
  classical
  let v : J ⊕ K → H := Sum.elim (fun i => (b i : H)) (fun i => (c i : H))
  have ho : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i <;> cases j
    · simpa [v] using (orthonormal_iff_ite.mp b.orthonormal _ _)
    · simp only [v, Sum.elim_inl, Sum.elim_inr, Sum.inl_ne_inr, ite_false]
      exact (E.mem_orthogonal _).mp (c _).property _ (b _).property
    · simp only [v, Sum.elim_inl, Sum.elim_inr, Sum.inr_ne_inl, ite_false]
      exact (E.mem_orthogonal' _).mp (c _).property _ (b _).property
    · simpa [v] using (orthonormal_iff_ite.mp c.orthonormal _ _)
  have ht : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hleft : E.orthogonalProjectionOnto x = 0 := by
      apply b.repr.injective
      ext i
      rw [map_zero, lp.coeFn_zero, Pi.zero_apply, HilbertBasis.repr_apply_apply,
        E.inner_orthogonalProjectionOnto_eq_of_mem_left]
      exact ((Submodule.span ℂ (Set.range v)).mem_orthogonal x).mp hx _
        (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    have hright : Eᗮ.orthogonalProjectionOnto x = 0 := by
      apply c.repr.injective
      ext i
      rw [map_zero, lp.coeFn_zero, Pi.zero_apply, HilbertBasis.repr_apply_apply,
        Eᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left]
      exact ((Submodule.span ℂ (Set.range v)).mem_orthogonal x).mp hx _
        (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
    have he := E.starProjection_add_starProjection_orthogonal x
    simpa [Submodule.starProjection_apply, hleft, hright] using he.symm
  let d := HilbertBasis.mkOfOrthogonalEqBot ho ht
  exact ⟨d, fun i => congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot ho ht) (Sum.inl i),
    fun i => congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot ho ht) (Sum.inr i)⟩

private theorem gns_cyclic_dense (W : WeylSystem (A := A) σ)
    (ω : A →ₚ[ℂ] ℂ) (hω : ω 1 = 1) :
    Dense (Submodule.span ℂ (Set.range (fun f => (ω.toPreGNS (W.weyl f) : ω.GNS))) :
      Set ω.GNS) := by
  let T : A →L[ℂ] ω.PreGNS := ω.toPreGNS.toLinearMap.mkContinuous 1 (fun a => by
    rw [one_mul, PositiveLinearMap.preGNS_norm_def']
    apply (Real.sqrt_le_iff).mpr
    refine ⟨norm_nonneg _, (state_norm_le ω hω _).trans_eq ?_⟩
    simp [CStarRing.norm_star_mul_self, pow_two])
  let C : A →L[ℂ] ω.GNS := UniformSpace.Completion.toComplL.comp T
  have hd : DenseRange C :=
    UniformSpace.Completion.denseRange_coe.comp ω.toPreGNS.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)
  have h := hd.dense_image C.continuous W.dense_span
  change Dense (C.toLinearMap '' (Submodule.span ℂ (Set.range W.weyl) : Set A)) at h
  rw [← Submodule.map_coe, Submodule.map_span, ← Set.range_comp] at h
  exact h

private theorem gns_inner (ω : A →ₚ[ℂ] ℂ) (a b : A) :
    ⟪(ω.toPreGNS a : ω.GNS), (ω.toPreGNS b : ω.GNS)⟫_ℂ = ω (star a * b) := by
  rw [UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]
  simp

private theorem gns_action (ω : A →ₚ[ℂ] ℂ) (a b : A) :
    ω.gnsStarAlgHom a (ω.toPreGNS b : ω.GNS) = (ω.toPreGNS (a * b) : ω.GNS) := by
  change ω.gnsNonUnitalStarAlgHom a (ω.toPreGNS b : ω.GNS) = _
  simp [PositiveLinearMap.leftMulMapPreGNS]

private theorem gram_unitary {J X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (v : J → X) (w : J → Y) (hg : ∀ i j, ⟪w i, w j⟫_ℂ = ⟪v i, v j⟫_ℂ)
    (hv : Dense (Submodule.span ℂ (Set.range v) : Set X))
    (hw : Dense (Submodule.span ℂ (Set.range w) : Set Y)) :
    ∃ U : X ≃ₗᵢ[ℂ] Y, ∀ j, U (v j) = w j := by
  let V := Finsupp.linearCombination ℂ v
  let W := Finsupp.linearCombination ℂ w
  have hV : DenseRange V := by
    simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination, V] using hv
  have hW : DenseRange W := by
    simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination, W] using hw
  have hn (a : J →₀ ℂ) : ‖W a‖ = ‖V a‖ := by
    have he : ⟪W a, W a⟫_ℂ = ⟪V a, V a⟫_ℂ := by
      simp only [V, W, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner,
        inner_sum, inner_smul_left, inner_smul_right, hg]
    simp only [inner_self_eq_norm_sq_to_K] at he
    have hs : ‖W a‖ ^ 2 = ‖V a‖ ^ 2 := by exact_mod_cast he
    nlinarith [norm_nonneg (W a), norm_nonneg (V a)]
  let U := (LinearEquiv.refl ℂ (J →₀ ℂ)).extendOfIsometry V W hV hW hn
  refine ⟨U, fun j => ?_⟩
  simpa only [U, V, W, LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul] using
    LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (J →₀ ℂ)) V W hV hW hn (Finsupp.single j 1)

private theorem fock_gns_equiv {K J : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (W : WeylSystem (A := A) σ) (ω : A →ₚ[ℂ] ℂ) (hω : ω 1 = 1)
    (z : S →ₗ[ℝ] K) (b : HilbertBasis J ℂ K)
    (hd : Dense (Submodule.span ℂ (Set.range z) : Set K))
    (hs : ∀ f g, σ f g = 2 * (⟪z f, z g⟫_ℂ).im)
    (hc : ∀ f, ω (W.weyl f) = Complex.exp (-(‖z f‖ : ℂ) ^ 2 / 2)) :
    ∃ U : ω.GNS ≃ₗᵢ[ℂ] BosonFock J, ∀ f x,
      U (ω.gnsStarAlgHom (W.weyl f) x) = fockWeyl b (z f) (U x) := by
  let v (f : S) : ω.GNS := ω.toPreGNS (W.weyl f)
  let w (f : S) := fockWeyl b (z f) (fockVacuum J)
  have hp (f g : S) : Complex.exp (-(Complex.I * (σ f g : ℂ)) / 2) =
      Complex.exp (-(Complex.I * (⟪z f, z g⟫_ℂ).im)) := by
    rw [hs, Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 1
    ring
  have hmul (f g : S) : fockWeyl b (z f) (w g) =
      Complex.exp (-(Complex.I * (σ f g : ℂ)) / 2) • w (f + g) := by
    change fockWeyl b (z f) (fockWeyl b (z g) (fockVacuum J)) = _
    rw [hp, fockWeyl_mul]
    simp only [w, map_add]
  have hg (f g : S) : ⟪w f, w g⟫_ℂ = ⟪v f, v g⟫_ℂ := by
    rw [gns_inner, W.weyl_star, W.weyl_mul, map_smul, hc]
    have hi := (fockWeyl b (z f)).symm.inner_map_map (w f) (w g)
    have hwf : (fockWeyl b (z f)).symm (w f) = fockVacuum J := (fockWeyl b (z f)).symm_apply_apply _
    rw [hwf, fockWeyl_symm, ← map_neg z, hmul, inner_smul_right] at hi
    unfold w at hi
    rw [fockWeyl_vacuum_inner] at hi
    simpa only [smul_eq_mul] using hi.symm
  have hw : Dense (Submodule.span ℂ (Set.range w) : Set (BosonFock J)) := by
    have hh := fockExponential_dense_span_of_dense_real b z.range (by simpa [LinearMap.coe_range] using hd)
    apply hh.mono
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨f, rfl⟩ := hx
    have hf : w f ∈ Submodule.span ℂ (Set.range w) := Submodule.subset_span ⟨f, rfl⟩
    have he : w f = Complex.exp (-(‖z f‖ : ℂ) ^ 2 / 2) • fockExponential b (z f) := by
      change fockWeyl b (z f) (fockVacuum J) = _
      rw [← fockExponential_zero b, fockWeyl_exponential]
      simp
    rw [he] at hf
    have hh := (Submodule.span ℂ (Set.range w)).smul_mem (Complex.exp (-(‖z f‖ : ℂ) ^ 2 / 2))⁻¹ hf
    rw [smul_smul, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_smul] at hh
    exact hh
  obtain ⟨U, hU⟩ := gram_unitary v w hg (gns_cyclic_dense W ω hω) hw
  refine ⟨U, fun f => ?_⟩
  let F := U.toLinearIsometry.toContinuousLinearMap.comp (ω.gnsStarAlgHom (W.weyl f))
  let G := (fockWeyl b (z f)).toLinearIsometry.toContinuousLinearMap.comp U.toLinearIsometry.toContinuousLinearMap
  have he : F = G := by
    apply ContinuousLinearMap.ext
    refine (gns_cyclic_dense W ω hω).induction ?_ (isClosed_eq F.continuous G.continuous)
    apply LinearMap.eqOn_span (f := F.toLinearMap) (g := G.toLinearMap)
    rintro x ⟨g, rfl⟩
    change U (ω.gnsStarAlgHom (W.weyl f) (v g)) = fockWeyl b (z f) (U (v g))
    change U (ω.gnsStarAlgHom (W.weyl f) (ω.toPreGNS (W.weyl g) : ω.GNS)) = _
    rw [gns_action, W.weyl_mul, map_smul, UniformSpace.Completion.coe_smul, map_smul]
    change _ • U (v (f + g)) = fockWeyl b (z f) (U (v g))
    rw [hU, hU, hmul]
  exact fun x => DFunLike.congr_fun he x

private theorem restrict_vector [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H)
    (W : WeylSystem (A := A) σ) (ωRef ωTarget : A →ₚ[ℂ] ℂ) (hω : ωRef 1 = 1)
    (z : S →ₗ[ℝ] H) (hs : ∀ f g, σ f g = 2 * (⟪z f, z g⟫_ℂ).im)
    (hc : ∀ f, ωRef (W.weyl f) = Complex.exp (-(‖z f‖ : ℂ) ^ 2 / 2))
    (ψ : BosonFock I) (hψ : ‖ψ‖ = 1)
    (he : ∀ f, ⟪ψ, fockWeyl b (z f) ψ⟫_ℂ = ωTarget (W.weyl f)) :
    Excitability ωTarget ωRef := by
  classical
  let E := (Submodule.span ℂ (Set.range z)).topologicalClosure
  let : CompleteSpace E := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let zE : S →ₗ[ℝ] E := z.codRestrict (E.restrictScalars ℝ) (fun f =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, rfl⟩))
  have hd : Dense (Submodule.span ℂ (Set.range zE) : Set E) := by
    let P := E.orthogonalProjectionOnto
    have hP : (P.toLinearMap : H → E) ∘ z = zE := by
      funext f
      exact E.orthogonalProjectionOnto_mem_subspace_eq_self (zE f)
    have hh := image_closure_subset_closure_image P.continuous
      (s := (Submodule.span ℂ (Set.range z) : Set H))
    intro x
    have hx : x ∈ P '' (E : Set H) := by
      exact ⟨(x : H), x.property, E.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
    rw [← Submodule.topologicalClosure_coe] at hh
    change P '' (E : Set H) ⊆ closure (P.toLinearMap '' (Submodule.span ℂ (Set.range z) : Set H)) at hh
    rw [← Submodule.map_coe, Submodule.map_span, ← Set.range_comp, hP] at hh
    exact hh hx
  obtain ⟨J, bE, _⟩ := exists_hilbertBasis ℂ E
  obtain ⟨K, bEp, _⟩ := exists_hilbertBasis ℂ Eᗮ
  let : Countable K := countable_basis bEp
  obtain ⟨d, hleft, hright⟩ := exists_splitBasis E bE bEp
  let Ψ := fockBasisChange b d ψ
  let Φ := fockSumSplit J K Ψ
  have hzero (f : S) (i : K) : d.repr (z f) (Sum.inr i) = 0 := by
    rw [HilbertBasis.repr_apply_apply, hright]
    exact (E.mem_orthogonal' _).mp (bEp i).property _ (zE f).property
  have hcoord (f : S) : fockOneParticleLeft d bE (z f) = zE f := by
    apply bE.repr.injective
    ext i
    rw [fockOneParticleLeft_repr, HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, hleft]
    rfl
  obtain ⟨U, hU⟩ := fock_gns_equiv W ωRef hω zE bE hd hs hc
  have hn : HasSum (fun β : Occupation K => ‖Φ β‖ ^ 2) (1 : ℝ) := by
    have hh := lp.hasSum_norm (p := 2) (by norm_num) Φ
    simpa [Φ, Ψ, hψ, Real.rpow_natCast] using hh
  have hcoeff (f : S) :
      HasSum (fun β : Occupation K => ⟪Φ β, fockWeyl bE (zE f) (Φ β)⟫_ℂ)
        (ωTarget (W.weyl f)) := by
    have hh := lp.hasSum_inner (𝕜 := ℂ) Φ (fockSumSplit J K (fockWeyl d (z f) Ψ))
    have heval : ⟪Φ, fockSumSplit J K (fockWeyl d (z f) Ψ)⟫_ℂ =
        ωTarget (W.weyl f) := by
      change ⟪fockSumSplit J K Ψ, fockSumSplit J K (fockWeyl d (z f) Ψ)⟫_ℂ = _
      rw [(fockSumSplit J K).inner_map_map, ← fockBasisChange_weyl,
        (fockBasisChange b d).inner_map_map, he]
    rw [heval] at hh
    simpa only [Φ, fockSumSplit_weyl d bE _ (hzero f), hcoord] using hh
  obtain ⟨j, hj⟩ := Countable.exists_injective_nat (Occupation K)
  let χ : ℕ → BosonFock J := Function.extend j (fun β => Φ β) 0
  have hχ (β : Occupation K) : χ (j β) = Φ β := hj.extend_apply _ _ _
  have hχ0 (n : ℕ) (hn : n ∉ Set.range j) : χ n = 0 := Function.extend_apply' _ _ _ hn
  apply excitability_of_unitary_intertwining W ωTarget ωRef U
    (fun f => (fockWeyl bE (zE f)).toLinearIsometry.toContinuousLinearMap) hU χ
  · apply (hj.hasSum_iff (fun n hn => by simp [hχ0 n hn])).mp
    simpa [Function.comp_def, hχ] using hn
  · intro f
    apply HasSum.tsum_eq
    apply (hj.hasSum_iff (fun n hn => by simp [hχ0 n hn])).mp
    simpa [Function.comp_def, hχ] using hcoeff f

variable [TopologicalSpace.SeparableSpace H]

/-- Hilbert–Schmidt covariance-root comparison implies folium membership even for mixed
Gaussian states and arbitrary symplectic radical. -/
theorem gaussian_mutual_excitable_of_sqrt_hs
    (W : WeylSystem (A := A) σ) (ωRef ωTarget : A →ₚ[ℂ] ℂ)
    (Γ : RealConjugation H) (e : S →ₗ[ℝ] H)
    (he : ∀ f, Γ.toLinearIsometryEquiv (e f) = e f)
    (_hd : Dense (Submodule.span ℂ (Set.range e) : Set H))
    (Q R : H →L[ℂ] H) (hQ : 0 ≤ Q) (hker : Q.ker = ⊥)
    (hq : ∀ x, Γ.toLinearIsometryEquiv (Q x) = Q (Γ.toLinearIsometryEquiv x))
    (hR : R.adjoint = -R) (hr : ∀ x, Γ.toLinearIsometryEquiv (R x) = R (Γ.toLinearIsometryEquiv x))
    (h₁ : 0 ≤ 1 - Complex.I • R) (h₂ : 0 ≤ Q - Complex.I • R)
    (hωRef : ωRef 1 = 1) (hωTarget : ωTarget 1 = 1)
    (hs : ∀ f g, σ f g = -2 * (⟪e f, R (e g)⟫_ℂ).re)
    (hRef : ∀ f, ωRef (W.weyl f) = Complex.exp (-(‖e f‖ ^ 2 : ℂ) / 2))
    (hTarget : ∀ f, ωTarget (W.weyl f) = Complex.exp (-((⟪e f, Q (e f)⟫_ℂ).re : ℂ) / 2))
    (hHS : IsHilbertSchmidt (CFC.sqrt (Q - Complex.I • R) - CFC.sqrt (1 - Complex.I • R))) :
    Excitability ωTarget ωRef ∧ Excitability ωRef ωTarget := by
  obtain ⟨p₁, p₂, u₁, u₂, r₁, r₂, hinner₁, hinner₂, w, b, r, _, hrs, hcov⟩ :=
    commonPureExtension Γ hQ hker hq hR hr h₁ h₂ hHS
  let D₁ := doubleCovariance 1 R
  let D₂ := doubleCovariance Q R
  let l₁ := pureExtension Γ D₁ p₁ u₁ r₁
  let l₂ := pureExtension Γ D₂ p₂ u₂ r₂
  let eR : S →ₗ[ℝ] realSubspace Γ := e.codRestrict _ he
  let i := (phaseEmbedding Γ R hr).comp eR
  let z₁ := l₁.toLinearMap.comp i
  let z₂ := l₂.toLinearMap.comp i
  have realR (f g : S) : (⟪e f, R (e g)⟫_ℂ).im = 0 := by
    have hh := real_inner Γ (eR f) ⟨R (e g), by
      change Γ.toLinearIsometryEquiv (R (e g)) = _
      rw [hr, he]⟩
    exact congrArg Complex.im hh
  have realQ (f g : S) : (⟪e f, Q (e g)⟫_ℂ).im = 0 := by
    have hh := real_inner Γ (eR f) ⟨Q (e g), by
      change Γ.toLinearIsometryEquiv (Q (e g)) = _
      rw [hq, he]⟩
    exact congrArg Complex.im hh
  have realOne (f g : S) : (⟪e f, e g⟫_ℂ).im = 0 := by
    exact congrArg Complex.im (real_inner Γ (eR f) (eR g))
  have hσ₁ (f g : S) : σ f g = 2 * (⟪z₁ f, z₁ g⟫_ℂ).im := by
    rw [hs]
    change _ = 2 * (⟪l₁ (phaseEmbedding Γ R hr (eR f)), l₁ (phaseEmbedding Γ R hr (eR g))⟫_ℂ).im
    rw [hinner₁]
    change -2 * (⟪e f, R (e g)⟫_ℂ).re = 2 * (⟪e f, e g⟫_ℂ - Complex.I * ⟪e f, R (e g)⟫_ℂ).im
    simp [Complex.mul_im, realOne f g]
  have hσ₂ (f g : S) : σ f g = 2 * (⟪z₂ f, z₂ g⟫_ℂ).im := by
    rw [hs]
    change _ = 2 * (⟪l₂ (phaseEmbedding Γ R hr (eR f)), l₂ (phaseEmbedding Γ R hr (eR g))⟫_ℂ).im
    rw [hinner₂]
    change -2 * (⟪e f, R (e g)⟫_ℂ).re = 2 * (⟪e f, Q (e g)⟫_ℂ - Complex.I * ⟪e f, R (e g)⟫_ℂ).im
    simp [Complex.mul_im, realQ f g]
  have hn₁ (f : S) : ‖z₁ f‖ ^ 2 = ‖e f‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    change (⟪l₁ (phaseEmbedding Γ R hr (eR f)), l₁ (phaseEmbedding Γ R hr (eR f))⟫_ℂ).re = _
    rw [hinner₁]
    change (⟪e f, e f⟫_ℂ - Complex.I * ⟪e f, R (e f)⟫_ℂ).re = _
    simp [Complex.mul_re, realR f f, inner_self_eq_norm_sq_to_K]
  have hn₂ (f : S) : ‖z₂ f‖ ^ 2 = (⟪e f, Q (e f)⟫_ℂ).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    change (⟪l₂ (phaseEmbedding Γ R hr (eR f)), l₂ (phaseEmbedding Γ R hr (eR f))⟫_ℂ).re = _
    rw [hinner₂]
    change (⟪e f, Q (e f)⟫_ℂ - Complex.I * ⟪e f, R (e f)⟫_ℂ).re = _
    simp [Complex.mul_re, realR f f]
  have hc₁ (f : S) : ωRef (W.weyl f) = Complex.exp (-(‖z₁ f‖ : ℂ) ^ 2 / 2) := by
    rw [hRef]
    have h := congrArg Complex.ofReal (hn₁ f)
    push_cast at h
    rw [h]
  have hc₂ (f : S) : ωTarget (W.weyl f) = Complex.exp (-(‖z₂ f‖ : ℂ) ^ 2 / 2) := by
    rw [hTarget, ← hn₂, Complex.ofReal_pow]
  constructor
  · apply restrict_vector (complexHilbertBasis Γ b) W ωRef ωTarget hωRef z₁ hσ₁ hc₁
      (infiniteSqueeze r hrs) (infiniteSqueeze_norm r hrs)
    intro f
    rw [infiniteSqueeze_weyl_inner, hc₂]
    have hh := hcov (z₁ f)
    change ‖l₂ (l₁.symm (l₁ (i f)))‖ ^ 2 = _ at hh
    rw [l₁.symm_apply_apply] at hh
    change ‖z₂ f‖ ^ 2 = _ at hh
    simp only [← HilbertBasis.repr_apply_apply] at hh
    rw [← hh, Complex.ofReal_pow]
  · obtain ⟨_, _, _, hu, hroot, hinv⟩ := covariance_coercive hQ hker h₁ h₂ hHS
    have hdiff := doubleCovariance_sub_hs hroot
      (defectRoot_sub_hs Γ hQ hu hq hR hr h₁ h₂ hinv hHS)
    have hrev : IsHilbertSchmidt (D₁ - D₂) := by
      have hh := isHilbertSchmidt_smul (-1 : ℂ) hdiff
      convert hh using 1
      simp [D₁, D₂]
    obtain ⟨w', b', r', _, hrs', hcov'⟩ := exists_squeeze_eigenbasis Γ D₂ D₁ p₂ p₁ u₂ u₁ r₂ r₁ hrev
    apply restrict_vector (complexHilbertBasis Γ b') W ωTarget ωRef hωTarget z₂ hσ₂ hc₂
      (infiniteSqueeze r' hrs') (infiniteSqueeze_norm r' hrs')
    intro f
    rw [infiniteSqueeze_weyl_inner, hc₁]
    have hh := hcov' (z₂ f)
    change ‖l₁ (l₂.symm (l₂ (i f)))‖ ^ 2 = _ at hh
    rw [l₂.symm_apply_apply] at hh
    change ‖z₁ f‖ ^ 2 = _ at hh
    simp only [← HilbertBasis.repr_apply_apply] at hh
    rw [← hh, Complex.ofReal_pow]

/-- The one-sided Gaussian folium sufficiency implication. -/
theorem gaussian_excitable_of_sqrt_hs
    (W : WeylSystem (A := A) σ) (ωRef ωTarget : A →ₚ[ℂ] ℂ)
    (Γ : RealConjugation H) (e : S →ₗ[ℝ] H)
    (he : ∀ f, Γ.toLinearIsometryEquiv (e f) = e f)
    (hd : Dense (Submodule.span ℂ (Set.range e) : Set H))
    (Q R : H →L[ℂ] H) (hQ : 0 ≤ Q) (hker : Q.ker = ⊥)
    (hq : ∀ x, Γ.toLinearIsometryEquiv (Q x) = Q (Γ.toLinearIsometryEquiv x))
    (hR : R.adjoint = -R) (hr : ∀ x, Γ.toLinearIsometryEquiv (R x) = R (Γ.toLinearIsometryEquiv x))
    (h₁ : 0 ≤ 1 - Complex.I • R) (h₂ : 0 ≤ Q - Complex.I • R)
    (hωRef : ωRef 1 = 1) (hωTarget : ωTarget 1 = 1)
    (hs : ∀ f g, σ f g = -2 * (⟪e f, R (e g)⟫_ℂ).re)
    (hRef : ∀ f, ωRef (W.weyl f) = Complex.exp (-(‖e f‖ ^ 2 : ℂ) / 2))
    (hTarget : ∀ f, ωTarget (W.weyl f) = Complex.exp (-((⟪e f, Q (e f)⟫_ℂ).re : ℂ) / 2))
    (hHS : IsHilbertSchmidt (CFC.sqrt (Q - Complex.I • R) - CFC.sqrt (1 - Complex.I • R))) :
    Excitability ωTarget ωRef :=
  (gaussian_mutual_excitable_of_sqrt_hs W ωRef ωTarget Γ e he hd Q R hQ hker hq hR hr
    h₁ h₂ hωRef hωTarget hs hRef hTarget hHS).1

section RealData

variable (Γ : RealConjugation H)

/-- The canonical inclusion of the real fixed form. -/
def fixedInclusion : realSubspace Γ →ₗ[ℝ] H := (realSubspace Γ).subtype

def realCovariance (Q : H →L[ℂ] H) :
    realSubspace Γ →ₗ[ℝ] realSubspace Γ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => (⟪(f : H), Q (g : H)⟫_ℂ).re)
    (by intros; simp [inner_add_left, Complex.add_re])
    (by intros; simp [← Complex.coe_smul, inner_smul_left, Complex.mul_re])
    (by intros; simp [inner_add_right, Complex.add_re])
    (by intros; simp [← Complex.coe_smul, inner_smul_right, Complex.mul_re])

def realSymplecticForm (R : H →L[ℂ] H) :
    realSubspace Γ →ₗ[ℝ] realSubspace Γ →ₗ[ℝ] ℝ :=
  (-2 : ℝ) • realCovariance Γ R

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The complex span of the fixed form is the whole complex Hilbert space. -/
theorem fixedInclusion_dense :
    Dense (Submodule.span ℂ (Set.range (fixedInclusion Γ)) : Set H) := by
  suffices h : Submodule.span ℂ (Set.range (fixedInclusion Γ)) = ⊤ by
    rw [h, Submodule.top_coe]
    exact dense_univ
  apply top_unique
  intro x _
  have hr : realPart Γ x ∈ Submodule.span ℂ (Set.range (fixedInclusion Γ)) :=
    Submodule.subset_span ⟨⟨_, realPart_mem Γ x⟩, rfl⟩
  have hi : imagPart Γ x ∈ Submodule.span ℂ (Set.range (fixedInclusion Γ)) :=
    Submodule.subset_span ⟨⟨_, imagPart_mem Γ x⟩, rfl⟩
  rw [real_imag_decomposition Γ x]
  exact Submodule.add_mem _ hr (Submodule.smul_mem _ Complex.I hi)

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
private theorem fixedInner_im (T : H →L[ℂ] H)
    (hT : ∀ x, Γ.toLinearIsometryEquiv (T x) = T (Γ.toLinearIsometryEquiv x))
    (f g : realSubspace Γ) :
    (⟪(f : H), T (g : H)⟫_ℂ).im = 0 := by
  have he := conj_inner Γ (f : H) (T (g : H))
  rw [f.property, hT, g.property] at he
  have hi := congrArg Complex.im he
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- The restricted pure inner product has the required Weyl phase and covariance norm. -/
theorem extensionPhaseNorm (Q R : H →L[ℂ] H)
    (hQ : ∀ x, Γ.toLinearIsometryEquiv (Q x) = Q (Γ.toLinearIsometryEquiv x))
    (hR : ∀ x, Γ.toLinearIsometryEquiv (R x) = R (Γ.toLinearIsometryEquiv x))
    (z : realSubspace Γ →ₗ[ℝ] H)
    (hz : ∀ f g, ⟪z f, z g⟫_ℂ =
      ⟪(f : H), Q (g : H)⟫_ℂ - Complex.I * ⟪(f : H), R (g : H)⟫_ℂ) :
    (∀ f g, realSymplecticForm Γ R f g = 2 * (⟪z f, z g⟫_ℂ).im) ∧
    (∀ f, ‖z f‖ ^ 2 = realCovariance Γ Q f f) := by
  constructor
  · intro f g
    change -2 * (⟪(f : H), R (g : H)⟫_ℂ).re = _
    rw [hz, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      fixedInner_im Γ Q hQ f g]
    ring
  · intro f
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hz]
    change (⟪(f : H), Q (f : H)⟫_ℂ - Complex.I * ⟪(f : H), R (f : H)⟫_ℂ).re =
      (⟪(f : H), Q (f : H)⟫_ℂ).re
    rw [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      fixedInner_im Γ R hR f f]
    ring

end RealData

end D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianFolium
