/- GID: D5/S3/Fourier/Asymptotics/ActualSpectralSeries
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/ActualSpectralSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct actual compact kernel eigenfamilies and complete spectral series on the same noise. -/

import D5.S3.Fourier.Asymptotics.SameNoiseSecondChaos
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section
namespace D5.S3.Fourier.Asymptotics.ActualSpectralSeries

universe uX

set_option autoImplicit false

variable {X : Type uX} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]
section IntegralOperator

variable (T : Lp ℝ 2 (μ.prod μ) →L[ℝ] (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
variable (hT : ∀ K f, (fun x => T K f x) =ᵐ[μ]
  (fun x => ∫ y, K (x, y) * f y ∂μ))
include hT

/-- Fubini identifies the actual integral operator with the kernel pairing. -/
theorem integral_operator_pairing (K : Lp ℝ 2 (μ.prod μ)) (f g : Lp ℝ 2 μ) :
    ⟪T K f, g⟫ = ⟪SameNoiseSecondChaos.rankOne μ g f, K⟫ := by
  have hi := L2.integrable_inner (𝕜 := ℝ) (SameNoiseSecondChaos.rankOne μ g f) K
  have hip : Integrable (fun z : X × X => K z * (g z.1 * f z.2)) (μ.prod μ) := by
    apply hi.congr
    filter_upwards [SameNoiseSecondChaos.rankOne_coe μ g f] with z hz
    simp [Real.inner_apply, hz]
  rw [L2.inner_def, L2.inner_def]
  simp only [Real.inner_apply]
  calc
    (∫ x, T K f x * g x ∂μ) =
        ∫ x, ∫ y, K (x, y) * (g x * f y) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hT K f] with x hx
      rw [hx, ← integral_mul_const]
      congr 1
      funext y
      ring
    _ = ∫ z, K z * (g z.1 * f z.2) ∂μ.prod μ := (integral_prod _ hip).symm
    _ = ∫ z, SameNoiseSecondChaos.rankOne μ g f z * K z ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [SameNoiseSecondChaos.rankOne_coe μ g f] with z hz
      rw [hz]
      ring

/-- No actual L2 kernel is lost by passage to its integral operator. -/
theorem integral_operator_injective : Function.Injective T := by
  intro K L hKL
  have hzero : T (K-L) = 0 := by rw [map_sub, hKL, sub_self]
  apply sub_eq_zero.mp
  apply SameNoiseSecondChaos.rankOne_total μ
  intro f g
  rw [← integral_operator_pairing μ T hT (K-L) g f, hzero]
  simp

/-- Diagonal kernels give genuine rank-one operators on the original Hilbert space. -/
theorem integral_operator_diagonal (f g : Lp ℝ 2 μ) :
    T (SameNoiseSecondChaos.rankOne μ f f) g = ⟪f,g⟫ • f := by
  apply ext_inner_right ℝ
  intro h
  rw [integral_operator_pairing μ T hT,
    SameNoiseSecondChaos.rankOne_inner, real_inner_smul_left]
  simp only [real_inner_comm]
  ring

/-- Symmetry of the product-space kernel gives symmetry of its actual integral operator. -/
theorem integral_operator_symmetric (K : SameNoiseSecondChaos.symmetricKernel μ) :
    (T K.val).IsSymmetric := by
  intro f g
  change ⟪T K.val f, g⟫ = ⟪f, T K.val g⟫
  conv_rhs => rw [real_inner_comm]
  rw [integral_operator_pairing μ T hT, integral_operator_pairing μ T hT]
  have hK : SameNoiseSecondChaos.kernelFlip μ K.val = K.val := by
    have hh := K.property
    change SameNoiseSecondChaos.kernelFlip μ K.val - K.val = 0 at hh
    exact sub_eq_zero.mp hh
  have hh := (SameNoiseSecondChaos.kernelFlip μ).inner_map_map
    (SameNoiseSecondChaos.rankOne μ g f) K.val
  rw [SameNoiseSecondChaos.kernelFlip_rankOne, hK] at hh
  exact hh.symm

/-- Finite-rank approximation in the actual kernel norm makes every symmetric kernel operator
compact; compactness is an output, not an input. -/
theorem integral_operator_compact (K : SameNoiseSecondChaos.symmetricKernel μ) :
    IsCompactOperator (T K.val) := by
  let S : SameNoiseSecondChaos.symmetricKernel μ →L[ℝ]
      (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) := T.comp (SameNoiseSecondChaos.symmetricKernel μ).subtypeL
  refine (SameNoiseSecondChaos.finiteKernelMap_dense μ).induction_on K
    (p := fun K => IsCompactOperator (S K))
    (isClosed_setOfPred_isCompactOperator.preimage S.continuous) ?_
  intro c
  classical
  have hd (f : Lp ℝ 2 μ) : IsCompactOperator
      (T (SameNoiseSecondChaos.rankOne μ f f)) := by
    let A : Lp ℝ 2 μ →L[ℝ] ℝ := innerSL ℝ f
    let B : ℝ →L[ℝ] Lp ℝ 2 μ := ContinuousLinearMap.smulRight
      (ContinuousLinearMap.id ℝ ℝ) f
    have he : T (SameNoiseSecondChaos.rankOne μ f f) = B.comp A := by
      apply ContinuousLinearMap.ext
      intro g
      exact integral_operator_diagonal μ T hT f g
    rw [he]
    exact (isCompactOperator_of_locallyCompactSpace_rng B).comp_clm A
  change IsCompactOperator (T (SameNoiseSecondChaos.finiteKernelMap μ c).val)
  simp only [SameNoiseSecondChaos.finiteKernelMap, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    SameNoiseSecondChaos.diagonalKernel]
  change (∑ f ∈ c.support, c f • T (SameNoiseSecondChaos.rankOne μ f f)) ∈
    compactOperator (RingHom.id ℝ) (Lp ℝ 2 μ) (Lp ℝ 2 μ)
  apply Submodule.sum_mem
  intro f hf
  exact (hd f).smul (c f)


set_option maxHeartbeats 300000 in
/-- Assemble full eigenspace Hilbert bases on the original L2. The zero eigenspace is retained,
so the construction also covers nullspace and the zero operator. -/
theorem integral_operator_eigenbasis [MeasurableSpace.CountablyGenerated X]
    (K : SameNoiseSecondChaos.symmetricKernel μ) :
    ∃ (ι : Type uX) (_ : Countable ι) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (c : ι → ℝ),
      ∀ i, T K.val (b i) = c i • b i := by
  classical
  let A := T K.val
  have hcompact := integral_operator_compact μ T hT K
  have hsym := integral_operator_symmetric μ T hT K
  let V := fun a : ℝ => Module.End.eigenspace A.toLinearMap a
  letI : ∀ a : ℝ, CompleteSpace (V a) := fun a =>
    (ContinuousLinearMap.isClosed_eigenspace A a).completeSpace_coe
  have hbas (a : ℝ) : ∃ (s : Set (V a)) (_ : HilbertBasis s ℝ (V a)), True := by
    by_cases ha : a = 0
    · obtain ⟨s,b,hb⟩ := exists_hilbertBasis ℝ (V a)
      exact ⟨s,b,trivial⟩
    · letI : FiniteDimensional ℝ (V a) :=
        ContinuousLinearMap.finite_dimensional_eigenspace hcompact a ha
      let ob := stdOrthonormalBasis ℝ (V a)
      let eqv := Equiv.ofInjective ob ob.orthonormal.linearIndependent.injective
      exact ⟨Set.range ob, (ob.reindex eqv).toHilbertBasis, trivial⟩
  choose s b hb using hbas
  let ι := Σ a : ℝ, s a
  let e : ι → Lp ℝ 2 μ := fun i => (b i.1 i.2).val
  have he : Orthonormal ℝ e := by
    constructor
    · intro i
      exact (b i.1).orthonormal.1 i.2
    · rintro ⟨a,i⟩ ⟨a',j⟩ hij
      by_cases h : a = a'
      · subst a'
        have hne : i ≠ j := fun heq => hij (by subst j; rfl)
        exact (b a).orthonormal.2 hne
      · exact hsym.orthogonalFamily_eigenspaces h (b a i) (b a' j)
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : SecondCountableTopology (Lp ℝ 2 μ) := inferInstance
  have hc : Countable ι := by
    have hd : Pairwise (fun i j : ι =>
        Disjoint (Metric.ball (e i) (1/4 : ℝ)) (Metric.ball (e j) (1/4 : ℝ))) := by
      intro i j hij
      apply Metric.ball_disjoint_ball
      have hh : ‖e i-e j‖^2 = 2 := by
        rw [norm_sub_sq_real, he.1 i, he.1 j, he.2 hij]
        norm_num
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (e i-e j)]
    exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
      (fun i => ⟨e i, Metric.mem_ball_self (by norm_num)⟩)
  have htotal : (Submodule.span ℝ (Set.range e))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxe (i : ι) : ⟪x,e i⟫ = 0 := by
      have hh := hx (e i) (Submodule.subset_span (Set.mem_range_self i))
      simpa only [real_inner_comm] using hh
    have hxV : x ∈ (⨆ a : ℝ, V a)ᗮ := by
      rw [← Submodule.iInf_orthogonal]
      simp only [Submodule.mem_iInf]
      intro a v hv
      let F : V a →L[ℝ] ℝ := (innerSL ℝ x).comp (V a).subtypeL
      have hs := ((b a).hasSum_repr ⟨v,hv⟩).map F F.continuous
      have hz (j : s a) : F (b a j) = 0 := hxe ⟨a,j⟩
      have hh : F ⟨v,hv⟩ = 0 := by
        have hh := hs.tsum_eq
        simpa only [Function.comp_def, map_smul, hz, smul_zero, tsum_zero] using hh.symm
      simpa only [F, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
        Submodule.subtypeL_apply, real_inner_comm] using hh
    have hh := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hsym
    change (⨆ a : ℝ, V a)ᗮ = ⊥ at hh
    rwa [hh] at hxV
  let B := HilbertBasis.mkOfOrthogonalEqBot he htotal
  refine ⟨ι, hc, B, fun i => i.1, ?_⟩
  intro i
  change A (B i) = i.1 • B i
  have hB : (B : ι → Lp ℝ 2 μ) = e := HilbertBasis.coe_mkOfOrthogonalEqBot he htotal
  rw [congrFun hB i]
  exact Module.End.mem_eigenspace_iff.mp (b i.1 i.2).property


end IntegralOperator

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable (W : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 P)
variable (hW : ∀ f : Lp ℝ 2 μ,
  HasLaw (fun ω => W f ω) (gaussianReal 0 (‖f‖ ^ 2).toNNReal) P)

/-- The diagonal kernels belonging to an orthonormal family are themselves orthonormal in the
actual symmetric product-space Hilbert space. -/
theorem diagonal_orthonormal {ι : Type*} (e : ι → Lp ℝ 2 μ)
    (he : Orthonormal ℝ e) :
    Orthonormal ℝ (fun i => SameNoiseSecondChaos.diagonalKernel μ (e i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    have hn := he.1 i
    simp only [SameNoiseSecondChaos.diagonalKernel]
    rw [Submodule.coe_inner, SameNoiseSecondChaos.rankOne_inner]
    simpa [hn]
  · simp only [SameNoiseSecondChaos.diagonalKernel]
    rw [Submodule.coe_inner, SameNoiseSecondChaos.rankOne_inner]
    have hh := (orthonormal_iff_ite.mp he) i j
    simpa [hij] using hh

section KernelSeries
variable (T : Lp ℝ 2 (μ.prod μ) →L[ℝ] (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
variable (hT : ∀ K f, (fun x => T K f x) =ᵐ[μ]
  (fun x => ∫ y, K (x, y) * f y ∂μ))
include hT

/-- The complete eigenbasis determines the actual kernel, not only its operator. Bessel supplies
the kernel-norm convergent series, and injectivity identifies its limit with the original K. -/
theorem kernel_hasSum_of_eigenbasis {ι : Type*} [Countable ι]
    (K : SameNoiseSecondChaos.symmetricKernel μ)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (c : ι → ℝ)
    (hEig : ∀ i, T K.val (b i) = c i • b i) :
    HasSum (fun i => c i • SameNoiseSecondChaos.diagonalKernel μ (b i)) K := by
  classical
  let d : ι → SameNoiseSecondChaos.symmetricKernel μ :=
    fun i => SameNoiseSecondChaos.diagonalKernel μ (b i)
  have hd : Orthonormal ℝ d := diagonal_orthonormal μ b b.orthonormal
  have hcoeff (i : ι) : ⟪d i,K⟫ = c i := by
    change ⟪SameNoiseSecondChaos.rankOne μ (b i) (b i),K.val⟫ = c i
    rw [← integral_operator_pairing μ T hT, hEig, real_inner_smul_left,
      real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    simp
  let V : ∀ i : ι, ℝ →ₗᵢ[ℝ] SameNoiseSecondChaos.symmetricKernel μ :=
    fun i => LinearIsometry.toSpanSingleton ℝ _ (hd.1 i)
  have hV := hd.orthogonalFamily
  have hsq : Summable (fun i => ‖c i‖^2) := by
    simpa only [hcoeff] using hd.inner_products_summable (x := K)
  have hsV := (hV.summable_iff_norm_sq_summable c).mpr hsq
  have hs : Summable (fun i => c i • d i) := by
    simpa only [V, LinearIsometry.toSpanSingleton_apply] using hsV
  let L := ∑' i, c i • d i
  have hL : HasSum (fun i => c i • d i) L := hs.hasSum
  let S : SameNoiseSecondChaos.symmetricKernel μ →L[ℝ]
      (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) := T.comp (SameNoiseSecondChaos.symmetricKernel μ).subtypeL
  have hLb (i : ι) : T L.val (b i) = c i • b i := by
    let F : SameNoiseSecondChaos.symmetricKernel μ →L[ℝ] Lp ℝ 2 μ :=
      (ContinuousLinearMap.apply ℝ (Lp ℝ 2 μ) (b i)).comp S
    have hm := hL.map F F.continuous
    have ht (j : ι) : F (c j • d j) = if j = i then c i • b i else 0 := by
      change T (c j • SameNoiseSecondChaos.rankOne μ (b j) (b j)) (b i) = _
      rw [map_smul, smul_apply, integral_operator_diagonal μ T hT,
        (orthonormal_iff_ite.mp b.orthonormal) j i]
      by_cases h : j = i <;> simp [h]
    have hm' : HasSum (fun j => if j = i then c i • b i else 0) (F L) := by
      simpa only [Function.comp_def, ht] using hm
    exact hm'.unique (hasSum_ite_eq i (c i • b i))
  have heq : T L.val = T K.val := by
    apply ContinuousLinearMap.ext
    intro f
    have h1 := (b.hasSum_repr f).map (T L.val) (T L.val).continuous
    have h2 := (b.hasSum_repr f).map (T K.val) (T K.val).continuous
    simp only [Function.comp_def, map_smul, hLb, hEig] at h1 h2
    exact h1.unique h2
  have hLK : L = K := Subtype.ext (integral_operator_injective μ T hT heq)
  simpa only [hLK, d] using hL

end KernelSeries

/-- The actual same-noise expansion of a kernel once its spectral expansion has been constructed in
that same kernel Hilbert space.  The `HasSum` premise is the concrete spectral construction
obligation; no product noise or equality-in-law replacement occurs here. -/
theorem same_noise_series_of_kernel_hasSum {ι : Type*} [Countable ι]
    (K : SameNoiseSecondChaos.symmetricKernel μ)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (e : ι → Lp ℝ 2 μ) (coeff : ι → ℝ)
    (he : Orthonormal ℝ e)
    (hEig : ∀ i, T (e i) = coeff i • e i)
    (hK : HasSum (fun i => coeff i • SameNoiseSecondChaos.diagonalKernel μ (e i)) K) :
    (Summable (fun i => (coeff i) ^ 2)) ∧
      (∑' i, (coeff i) ^ 2 = ‖K‖^2) ∧
      (‖K‖^2 = Var[fun ω => SameNoiseSecondChaos.secondIntegral μ P W hW K ω; P] / 2) ∧
      (∀ i, |coeff i| ≤ ‖T‖) ∧
      ((⨆ i, |coeff i|) ≤ ‖T‖) ∧
      HasSum
        (fun i => (coeff i) • SameNoiseSecondChaos.centeredSquare μ P W hW (e i))
        (SameNoiseSecondChaos.secondIntegral μ P W hW K) := by
  classical
  let d : ι → SameNoiseSecondChaos.symmetricKernel μ :=
    fun i => SameNoiseSecondChaos.diagonalKernel μ (e i)
  have hd : Orthonormal ℝ d := diagonal_orthonormal μ e he
  let V : ∀ i : ι, ℝ →ₗᵢ[ℝ] SameNoiseSecondChaos.symmetricKernel μ :=
    fun i => LinearIsometry.toSpanSingleton ℝ _ (hd.1 i)
  have hV : OrthogonalFamily ℝ (fun _ : ι => ℝ) V := hd.orthogonalFamily
  have hterms : (fun i => V i (coeff i)) = fun i => coeff i • d i := by
    funext i
    simp [V, d]
  have hsumV : Summable (fun i => V i (coeff i)) := by
    rw [hterms]
    exact hK.summable
  have hsq : Summable (fun i => (coeff i) ^ 2) := by
    have hh := (hV.summable_iff_norm_sq_summable (fun i => coeff i)).mp hsumV
    simpa [V] using hh
  have hnorm : (∑' i, (coeff i) ^ 2 = ‖K‖^2) := by
    let f : lp (fun _ : ι => ℝ) 2 :=
      ⟨coeff, memℓp_gen (by simpa [Real.norm_eq_abs, sq_abs] using hsq)⟩
    have hKeq : K = OrthogonalFamily.linearIsometry hV f := by
      exact hK.tsum_eq.symm.trans (by
        rw [OrthogonalFamily.linearIsometry_apply]
        apply tsum_congr
        intro i
        have hVi : V i (coeff i) = coeff i • d i := by
          simp [V, d]
        simpa [f] using hVi.symm)
    have hnormf : ‖f‖ ^ 2 = ∑' i, (coeff i) ^ 2 := by
      simpa [f, Real.norm_eq_abs, sq_abs] using
        (lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) f)
    rw [hKeq, (OrthogonalFamily.linearIsometry hV).norm_map, hnormf]
  have hvariance :
      ‖K‖^2 = Var[fun ω => SameNoiseSecondChaos.secondIntegral μ P W hW K ω; P] / 2 := by
    have hmean : (∫ ω, SameNoiseSecondChaos.secondIntegral μ P W hW K ω ∂P) = 0 :=
      (SameNoiseSecondChaos.secondIntegral_characterization μ P W hW).1 K
    have hvar :
        Var[fun ω => SameNoiseSecondChaos.secondIntegral μ P W hW K ω; P] =
          ‖SameNoiseSecondChaos.secondIntegral μ P W hW K‖ ^ 2 := by
      rw [variance_of_integral_eq_zero (Lp.memLp _).aemeasurable hmean,
        ← real_inner_self_eq_norm_sq, L2.inner_def]
      congr 1
      funext ω
      simp [pow_two]
    have hnormI := (SameNoiseSecondChaos.secondIntegral_characterization μ P W hW).2.2.1 K
    rw [hvar, hnormI]
    have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    rw [mul_pow, hs]
    ring
  have hbound : ∀ i, |coeff i| ≤ ‖T‖ := by
    intro i
    have hi := hEig i
    have heq : |coeff i| = ‖T (e i)‖ := by
      calc
        |coeff i| = ‖coeff i • e i‖ := by
          rw [norm_smul, he.1 i]
          simp [Real.norm_eq_abs]
        _ = ‖T (e i)‖ := by rw [← hi]
    rw [heq]
    simpa [he.1 i] using T.le_opNorm (e i)
  have hsup : (⨆ i, |coeff i|) ≤ ‖T‖ := by
    classical
    cases isEmpty_or_nonempty ι with
    | inl hι =>
        letI := hι
        simpa using (norm_nonneg T)
    | inr hι =>
        letI := hι
        exact ciSup_le hbound
  have hmapped := hK.map
    (SameNoiseSecondChaos.secondIntegral μ P W hW)
    (SameNoiseSecondChaos.secondIntegral μ P W hW).continuous
  have hterm (i : ι) :
      SameNoiseSecondChaos.secondIntegral μ P W hW (coeff i • d i) =
        (coeff i) • SameNoiseSecondChaos.centeredSquare μ P W hW (e i) := by
    simp [d, SameNoiseSecondChaos.secondIntegral_diagonal]
  have hmapped' : HasSum
      (fun i => (coeff i) • SameNoiseSecondChaos.centeredSquare μ P W hW (e i))
      (SameNoiseSecondChaos.secondIntegral μ P W hW K) := by
    have hmappedd : HasSum
        (fun i => SameNoiseSecondChaos.secondIntegral μ P W hW (coeff i • d i))
        (SameNoiseSecondChaos.secondIntegral μ P W hW K) := by
      convert hmapped using 1
      funext i
      rfl
    convert hmappedd using 1
    · funext i
      exact (hterm i).symm
  exact ⟨hsq, hnorm, hvariance, hbound, hsup, hmapped'⟩

include hW in
/-- Every finite family of evaluations of the original W is jointly Gaussian. Arbitrary fixed
old vectors are included by choosing the family on a finite sum of index types. -/
theorem same_noise_finite_joint {ι : Type*} [Finite ι] (f : ι → Lp ℝ 2 μ) :
    HasGaussianLaw (fun ω i => W (f i) ω) P := by
  classical
  letI := Fintype.ofFinite ι
  let X : Ω → (ι → ℝ) := fun ω i => W (f i) ω
  have hXm : Measurable X := measurable_pi_lambda _ (fun i => (Lp.stronglyMeasurable _).measurable)
  constructor
  apply isGaussian_of_isGaussian_map
  intro L
  let a : ι → ℝ := fun i => L (Pi.single i 1)
  let v : Lp ℝ 2 μ := ∑ i, a i • f i
  have hL (z : ι → ℝ) : L z = ∑ i, a i * z i := by
    rw [← LinearMap.sum_single_apply (fun _ : ι => ℝ) z, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hs : Pi.single i (z i) = z i • Pi.single i (1 : ℝ) := by
      ext j
      by_cases h : i = j <;> simp [h, Pi.single_apply]
    rw [hs, map_smul]
    simp [a, mul_comm]
  have hcoe (s : Finset ι) :
      (fun ω => W (∑ i ∈ s, a i • f i) ω) =ᵐ[P]
        (fun ω => ∑ i ∈ s, a i * W (f i) ω) := by
    induction s using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℝ 2 P)
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, map_add, map_smul]
      filter_upwards [Lp.coeFn_add (a i • W (f i)) (W (∑ j ∈ s, a j • f j)),
        Lp.coeFn_smul (a i) (W (f i)), ih] with ω ha hs hh
      simp only [ha, hs, hh, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hlin : (fun ω => W v ω) =ᵐ[P] L ∘ X := by
    filter_upwards [hcoe Finset.univ] with ω hω
    simpa [v, Function.comp_def, X, hL] using hω
  have hg := (hW v).hasGaussianLaw.congr hlin
  rw [Measure.map_map L.continuous.measurable hXm]
  exact hg.isGaussian_map

/-- The finite joint law constructed from the original W gives independence of its orthonormal
coordinates on the same probability space. -/
theorem same_noise_finite_independence {ι : Type*} [Finite ι]
    (e : ι → Lp ℝ 2 μ) (he : Orthonormal ℝ e)
    (hW : ∀ f : Lp ℝ 2 μ,
      HasLaw (fun ω => W f ω) (gaussianReal 0 (‖f‖ ^ 2).toNNReal) P)
    :
    iIndepFun (fun i ω => W (e i) ω) P := by
  classical
  apply (same_noise_finite_joint μ P W hW e).iIndepFun_of_covariance_eq_zero
  intro i j hij
  have hmemi : MemLp (fun ω => W (e i) ω) 2 P :=
    (hW (e i)).hasGaussianLaw.memLp_two
  have hmemj : MemLp (fun ω => W (e j) ω) 2 P :=
    (hW (e j)).hasGaussianLaw.memLp_two
  have hsum : MemLp (fun ω => W (e i + e j) ω) 2 P :=
    (hW (e i + e j)).hasGaussianLaw.memLp_two
  have hvar_i : Var[fun ω => W (e i) ω; P] = ‖e i‖^2 := by
    rw [(hW (e i)).variance_eq, variance_id_gaussianReal]
    simp
  have hvar_j : Var[fun ω => W (e j) ω; P] = ‖e j‖^2 := by
    rw [(hW (e j)).variance_eq, variance_id_gaussianReal]
    simp
  have hvar_s : Var[fun ω => W (e i + e j) ω; P] = ‖e i + e j‖ ^ 2 := by
    rw [(hW (e i + e j)).variance_eq, variance_id_gaussianReal]
    simp
  have hlin : (fun ω => W (e i + e j) ω) =ᵐ[P]
      (fun ω => W (e i) ω + W (e j) ω) := by
    filter_upwards [Lp.coeFn_add (W (e i)) (W (e j))] with ω hω
    change (W (e i + e j)) ω = (W (e i)) ω + (W (e j)) ω
    rw [map_add]
    exact hω
  have hv := variance_add hmemi hmemj
  change Var[fun ω => W (e i) ω + W (e j) ω; P] = _ at hv
  rw [← variance_congr hlin, hvar_s, hvar_i, hvar_j] at hv
  have hnorm : ‖e i + e j‖ ^ 2 = ‖e i‖^2 + ‖e j‖^2 := by
    rw [norm_add_sq_real]
    have ho := (orthonormal_iff_ite.mp he) i j
    simpa [hij] using ho
  linarith [hv]

section ActualConstruction
variable (T : Lp ℝ 2 (μ.prod μ) →L[ℝ] (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))
variable (hT : ∀ K f, (fun x => T K f x) =ᵐ[μ]
  (fun x => ∫ y, K (x, y) * f y ∂μ))
include hT

/-- The actual countable spectral series on the original W and P. Compactness, complete
kernel HasSum, square sum, and finite joint Gaussian laws are constructed in this unit. -/
theorem actual_same_noise_spectral [MeasurableSpace.CountablyGenerated X]
    (K : SameNoiseSecondChaos.symmetricKernel μ) :
    ∃ (ι : Type uX) (_ : Countable ι) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (c : ι → ℝ),
      (∀ i, T K.val (b i) = c i • b i) ∧
      HasSum (fun i => c i • SameNoiseSecondChaos.diagonalKernel μ (b i)) K ∧
      Summable (fun i => (c i)^2) ∧
      (∑' i, (c i)^2 = ‖K‖^2) ∧
      (‖K‖^2 = Var[fun ω => SameNoiseSecondChaos.secondIntegral μ P W hW K ω; P] / 2) ∧
      (∀ i, |c i| ≤ ‖T K.val‖) ∧
      ((⨆ i, |c i|) ≤ ‖T K.val‖) ∧
      HasSum (fun i => c i • SameNoiseSecondChaos.centeredSquare μ P W hW (b i))
        (SameNoiseSecondChaos.secondIntegral μ P W hW K) ∧
      iIndepFun (fun i ω => W (b i) ω) P ∧
      (∀ i, HasLaw (fun ω => W (b i) ω) (gaussianReal 0 1) P) ∧
      (∀ (s : Finset ι) (n : ℕ) (old : Fin n → Lp ℝ 2 μ),
        HasGaussianLaw (fun ω (j : s ⊕ Fin n) =>
          W (Sum.elim (fun i : s => b i.val) old j) ω) P) := by
  classical
  obtain ⟨ι, hι, b, c, hEig⟩ := integral_operator_eigenbasis μ T hT K
  letI := hι
  have hK := kernel_hasSum_of_eigenbasis μ T hT K b c hEig
  obtain ⟨hsq, hnorm, hvar, hbnd, hsup, hseries⟩ :=
    same_noise_series_of_kernel_hasSum μ P W hW K (T K.val) b c b.orthonormal hEig hK
  have hind : iIndepFun (fun i ω => W (b i) ω) P := by
    apply iIndepFun_iff_finset.mpr
    intro s
    exact same_noise_finite_independence μ P W (fun i : s => b i.val)
      (b.orthonormal.comp _ Subtype.val_injective) hW
  refine ⟨ι, hι, b, c, hEig, hK, hsq, hnorm, hvar, hbnd, hsup, hseries, hind, ?_, ?_⟩
  · intro i
    simpa [b.orthonormal.1 i] using hW (b i)
  · intro s n old
    exact same_noise_finite_joint μ P W hW (Sum.elim (fun i : s => b i.val) old)

end ActualConstruction

end D5.S3.Fourier.Asymptotics.ActualSpectralSeries
