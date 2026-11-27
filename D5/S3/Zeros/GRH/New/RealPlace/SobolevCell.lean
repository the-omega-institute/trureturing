/- GID: D5/S3/Zeros/GRH/New/RealPlace/SobolevCell
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/RealPlace/SobolevCell
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.RealPlace.SobolevCell. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/RealPlace/SobolevCell.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.RealPlace.BesselOrthonormal
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Lower bound for Haar integral via open-cell double coset chart, explicit constant.
Unfolding bound over the Bessel unipotent group when frame entries stay bounded. Schur's bound read
at one section point, via Sobolev chain in derivative words. -/

attribute [-instance] MeasurableSingletonClass.toDiscreteMeasurableSpace

open MeasureTheory Measure Shape ENNReal Matrix.Norms.L2Operator Subgroup

set_option synthInstance.maxSize 999

/-- Let f ≥ 0 be measurable on G₁ and g = `gramDiscReal`, Ω = `Shape.openCell`, c_G =
`Shape.openCellConst`. If L ≤ ∫_Ω c_G g(Z)^{|κ|−1}
∫_H∫_{𝖴⁰}∫_{𝖴⁰} f(u k γ_Z (v h)⁻¹) du dv dh dZ for every k in H, then L ≤ ∫_{G₁} f. -/
lemma le_lintegral_of_gramSection {𝔰 : Shape} {f L} (hf : Measurable f) (h : ∀ k,
  L ≤ ∫⁻ Z in openCell, .ofReal (𝔰.openCellConst * gramDiscReal Z ^ (𝔰.k - 1)) * ∫⁻ h, ∫⁻ v, ∫⁻ u,
  f (u.1 * (embedH k * (gramSection Z * (v.1 * embedH h)⁻¹))) ∂besselHaar₀ ∂𝔰.besselHaar₀) :
  L ≤ ∫⁻ γ, f γ := have ⟨e, he, h_jac⟩ := @openCellChart_jacobian 𝔰
  (Haar.lintegral_chart_rotate_le e he
  (isOpen_openCell.measurableSet.prod .univ) (@openCellChart_injOn 𝔰) h_jac).exists.elim fun t e ↦
    by
  grw [← lintegral_mul_left_eq_self f (circleScalar t)⁻¹, ← e, ← one_mul L,
    ← (by simpa [cayleyDenom] using (lintegral_cayleyDensity_skewColumnEquiv 𝔰.k₀ 0 one_pos) :),
    ← lintegral_mul_const, h (cayleyChart 1 (skewColumnEquiv _ (‹_›, 0)))]
  simp (disch := first | finiteness | with_unfolding_all fun_prop) [volume_eq_prod _ (_ × _),
    openCellChart, ← prod_restrict, lintegral_prod, @lintegral_prod_symm 𝔰.UnipotentParams,
    lintegral_eq_cayleyChart, besselHaar₀, volU,
    lintegral_map, ← lintegral_const_mul, ← mul_assoc, ← ofReal_mul, ← ofReal_mul', openCellConst]
  rw [lintegral_lintegral_swap]; gcongr; simp [field]; repeat fun_prop

/-- Let w, φ ≥ 0 be measurable on G₁, w left `besselS`-invariant, ∫_{𝖴⁰} φ(uy)du ≤ K for all y,
and the frame matrix of s ∈ 𝖴 have entries ≤ R (R ≥ 1) whenever φ(y), φ(sy) ≠ 0. Then ∫φw ≤
K(2R)^{2(ϱ+1)²}∫_{𝖴∖G₁}w. -/
lemma lintegral_mul_le_of_frameMatrix_le {𝔰 : Shape} {w φ : 𝔰.G₁ → _} {K R} (hw : Measurable w)
  (hφ : Measurable φ) (hwU : besselS.FixesLeft w) (h : ∀ y, ∫⁻ u, φ (u * y) ∂𝔰.besselHaar₀ ≤
  K) (hR : ∀ y, φ y ≠ 0 → ∀ s ∈ besselU, φ (s * y) ≠ 0 → ∀ a b, ‖frameMatrix s a b‖ ≤ R) (h1 : 1 ≤
  R) : ∫⁻ y, φ y * w y ≤ K * .ofReal ((2 * R) ^ (2 * 𝔰.n ^ 2)) * ∫⁻ y, w y ∂besselQuotMeasure := by
  grw [← lintegral_orbitMeasure_lintegral (ν := 𝔰.besselHaar), ← lintegral_const_mul]; gcongr with y
  simp [Subgroup.smul_def, hwU]
  by_cases! e : ∀ u : besselU, φ (u.1 * y) = 0; simp [e]
  rw [lintegral_mul_const, ← lintegral_mul_right_eq_self _ e.choose, Shape.besselHaar,
    lintegral_map, lintegral_prod, ← setLIntegral_eq_of_support_subset
    (s := .pi ⊤ fun _ ↦ Metric.closedBall 0 R) fun x c p _ ↦ (not_forall.1
    (c ∘ lintegral_eq_zero_of_ae_eq_zero ∘ .of_forall)).elim fun u _ ↦ ?_]
  simp [mul_assoc]; grw [h, setLIntegral_const, mul_assoc]; gcongr; simp (disch := finiteness)
    [volume_pi, pow_mul, ← ENNReal.toReal_le_toReal]
  grw [Real.pi_le_four, Fintype.card_subtype_le]; simp [sq]; grind; bound
  simpa [frameMatrix_mul, liftUnitri_mem_besselU, mem_besselU0_iff.1, unitriMatrix, p.2] using
    hR _ e.choose_spec _ (mul_mem u.2.1 (liftUnitri_mem_besselU x)) (by simp_all [mul_assoc]) p.1.1
    p.1.2; repeat fun_prop

open Complex ComplexOrder Fintype Matrix Metric Real Set Norms.L2Operator

/-- Let F satisfy `HasSchurBound` with constants P ≥ 8r, D; let 𝗀 ≥ c > 0 and `IsBoundedInCell`
(bound P) hold within P⁻⁶ of Z; let φ be measurable, integrable, zero where ‖y‖ > P²⁰. Then
c_G c^{k−1} ∬ ‖∫ φ(y)F(γ_Z(uh)⁻¹y) dy‖² dh du ≤ P^{2000(ϱ+1)²} D ∫|φ|², over h ∈ U(κ), u ∈
𝖴⁰, ‖u‖ ≤ P²⁰. -/
lemma lintegral_gramSection_integral_le {𝔰 : Shape} {I} [Fintype I] {P c : ℝ} {D rep F}
  {Z : 𝔰.FrameMat} (hP : 8 * 𝔰.r ≤ P) (hV : HasSchurBound (I := I) F rep P D) (hc : 0 < c) (B : ∀
    {y}, y ∈ ball Z (P ^ 6)⁻¹ → c
  ≤ gramDiscReal y ∧ IsBoundedInCell y P) {φ : _ → ℂ} (hφ : Measurable φ) (hi : Integrable φ) (hφ' :
  ∀ y, φ y ≠ 0 → ‖y.1.1‖ ≤ P ^ 20) : ∫⁻ ω in {ω | ‖ω.2.1.1.1‖ ≤ P ^ 20}, ‖∫ y, φ y • F (gramSection
  Z * (ω.2.1 * embedH ω.1)⁻¹ * y)‖ₑ ^ 2 ∂ENNReal.ofReal (𝔰.openCellConst * c ^ (𝔰.k - 1)) •
  volume.prod 𝔰.besselHaar₀ ≤ .ofReal (P ^ (2000 * 𝔰.n ^ 2)) * D * ∫⁻ y, ‖φ y‖ₑ ^ 2 := by
  simp [mul_comm] at hP; have ⟨h1, h8, _⟩ : 1 ≤ P ∧ 8 ≤ P ∧ |P| = P := by grind
  let e :=
    (basisOneI.smulTower (A := 𝔰.FrameMat) (stdBasis ..)).equivFun.symm.toContinuousLinearEquiv
  obtain ⟨he, he'⟩ : MeasurePreserving (Z + e ·) ∧ ∀ x, ‖e x‖ ≤ _ * (‖x‖ + ‖x‖) := by
    use (HasGaussianIntegral.measurePreserving e.1 ?_).add_left .., fun _ ↦ l2_opNorm_le_of_apply ?_
      <;> simp [e, ite_and, sum_prod_type, stdBasis_eq_single, Matrix.sum_apply, norm_le_pi_norm,
      ← sq, -norm_eq_abs, RCLike.norm_sq_eq_def, norm_add_le_of_le, single_apply]
  choose bg o bi bn _ using fun {y} h ↦ B (ball_half_subset y h (mem_ball_self (by bound)))
  set Q := ball Z _
  have hx {x} (h : x ∈ Icc 0 fun _ ↦ (P ^ 8)⁻¹) : Z + e x ∈ Q := by
    grw [add_mem_ball_iff_norm, he', ← dist_zero_right, dist_le_of_mem_pi_Icc h (by grind)]
    simp [*, field]; nlinarith
  let ψ := List.foldr (fun ((a, b), c, d) ψ y ↦ ψ y * (y⁻¹.1 a d * y.1 c b / P ^ 40)) φ
  choose _ hψ using (List.rec (by tauto) fun _ _ ⟨h, k⟩ ↦ ⟨h.mul (by fun_prop), fun y ↦
    (norm_mul_le_of_le (k y) le_rfl).trans ((em' (φ y = 0)).elim (by grw [norm_div, norm_mul,
    norm_apply_le_l2_opNorm, norm_apply_le_l2_opNorm, U.norm_inv, hφ' _ ·]; simp [*, field])
    (by simp [·]))⟩ : ∀ i, Measurable (ψ i) ∧ ∀ y, ‖ψ i y‖ ≤ ‖φ y‖)
  have iψ i := hi.mono (by fun_prop) (.of_forall (hψ i)); choose V v hW hd hs using hV
  let T i g y := ψ i y • V (i.map (·.1)) (g * y)
  refine' (lintegral_congr (by simp [T, ψ, v])).trans_le ((sobolev_chain (fun i x (a, b) ↦
    ∫ y, T i (gramSection (Z + e x) * (embedH a⁻¹ * b.1⁻¹)) y) (by fun_prop) _ _
    (ae_restrict_of_forall_mem (by simp; fun_prop) fun ω h i j x _ k ↦ _) fun i hi ↦ _).trans _)
  rotate_left 5
  · let p t := Z + e (Function.update x j t)
    let g t := gramSection (p t) * (embedH ω.1⁻¹ * ω.2.1⁻¹)
    choose! A hA' hA using fun {t} (q : p t ∈ Q) ↦ show ∃ A, HasDerivAt (g · |>.1.1) (g t * A) t ∧
        ‖P ^ 40 • A‖ ≤ P ^ 112 by
      have ⟨a, b⟩ := norm_sectionMatrix_le (o q) (by positivity) h8 fun _ k ↦
        (B (ball_half_subset _ q k)).2
      refine ⟨_, ((((gramSection_eventuallyEq (o q)).hasFDerivAt_iff.2
        (differentiableAt_sectionMatrix (o q)).hasFDerivAt
        ).comp_hasDerivAt _ ((e.hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_update ..)).const_add Z)
        ).mul_const _).congr_deriv (by rw [Units.mul_inv_cancel_left]), ?_⟩
      grw [norm_smul, norm_mul_le, ← Subgroup.coe_inv, U.norm_inv, Subgroup.coe_mul, Units.val_mul,
        norm_mul_le, norm_mul_le, norm_embedH_mul, U.norm_inv, h.out, h.out, coe_gramSection,
        (fderiv ..).le_opNorm, e.coe_coe, he', a, b] <;> simp [Pi.norm_single, *, field]; nlinarith
    have s i j := (hW j).integrable_smul (iψ i)
    refine ⟨_, (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := fun t y ↦ ∑ l, (P ^ 40 •
      A) l.2.2 l.2.1 • T (l :: i) (g t) y) ((isOpen_ball.preimage (f := p) ?_).mem_nhds
      (hx k)) (.of_forall (by fun_prop)) ?_ ?_ (.of_forall fun y t ↦ (by grw [norm_sum_le,
      norm_smul_le, norm_apply_le_l2_opNorm, hA ·, norm_smul_le, (hW _).bounded.choose_spec])) ?_
      (.of_forall fun y t q ↦ .congr_deriv (.fun_const_smul _ (hd _ (g · * y) (y⁻¹ * A * y) _
      (by simpa [mul_assoc] using (hA' q).mul_const _))) ?_)).2, by
      grw [integral_finsetSum, norm_sum_le, congr(‖$(integral_smul ..)‖).le,
      norm_smul_le, norm_apply_le_l2_opNorm, hA (hx k)]; fun_prop⟩ <;> try fun_prop
    simp [-sum_sum_type, T, ψ, Finset.smul_sum, smul_smul, sum_prod_type, mul_apply,
      Finset.sum_mul, Finset.sum_smul]; congr! 5; field
  · have ⟨χ, mχ, v⟩ := (@isUnimodularHaar_besselHaar₀ 𝔰).out
    simp [← sq, Subgroup.smul_def] at hi v ⊢; grw [setLIntegral_le_lintegral {x | _}]
    have m := mχ.indicator (s :=
      realFrameGram ⁻¹' Q) (measurableSet_ball.preimage (by fun_prop [frameGram]))
    exact .trans (le_lintegral_of_gramSection (by fun_prop) fun _ ↦
      .trans_eq (.trans (setLIntegral_mono' (by simp) fun x h ↦ by grw [bg (hx h),
      lintegral_prod_le] <;> simp [𝔰.openCellConst_pos.le, indicator, mem_sup_left, mem_sup_right,
      realFrameGram_gramSection, realFrameGram_mul_invariant, lintegral_mul_const', hx h, T,
      ← mul_assoc (gramSection _), *, (hW _).enorm_integral_besselS_mul, fun u : besselU0 ↦
      mem_inf.1 u.2]) (lintegral_mono_set (by tauto)))
      (he.setLIntegral_comp_preimage isOpen_openCell.measurableSet (by fun_prop)))
      ((lintegral_mul_le_of_frameMatrix_le (w := (‖∫ y, T i · y‖ₑ ^ 2)) (by fun_prop) m
      (by simp +contextual [T, (hW _).enorm_integral_besselS_mul]) (by grw [indicator_le_self ..,
      v ·]) (by simp_intro y i s j k ..; simpa [realFrameGram_eq_frameMatrix_mul y j,
      (o k.1).1] using (norm_apply_le_l2_opNorm ..).trans (norm_mul_le_of_le (bn i.1) (bi k.1))) (by
      bound)).trans (by grw [hs .., i.length_map, hi, enorm_le_iff_norm_le.2 (hψ ..)] <;> simp [*]))
  simp (disch := bound) [← sq, ← mul_assoc, pow_mul, ← ENNReal.ofReal_mul, ← mul_pow,
    -ENNReal.ofReal_pow]; grw [le_of_mul_le_of_one_le hP, one_le_pow₀ h1 (n := 232)]
  gcongr; field; grw [← h8]; grind; repeat bound
