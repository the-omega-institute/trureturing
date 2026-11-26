import GRH.Lib.DiscreteSeries.Bessel.BesselNormInvariance
import GRH.New.RealPlace.GramSection
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Jacobian and injectivity of the open-cell double coset chart of U(p,q). Explicit
perturbation bounds for determinant, inverse and discriminant near an open-cell matrix. -/

open Fin Module Complex Finset HasGaussianIntegral Haar MatMul Matrix MeasureTheory Sum
  Norms.L2Operator

/-- The chart (Z, η, q, y, q') ↦ u(q)·c(η)·γ_Z·(u(q')·c(y))⁻¹ of G₁, with u = `unipotentOf` and
c the Cayley chart of H = U(X₀), at η after the coordinate change `skewColumnEquiv`. -/
noncomputable def openCellChart {𝔰 : Shape} := fun (Z, θ, q, η, r) ↦ unipotentOf q * embedH
    (cayleyChart 1 (skewColumnEquiv 𝔰.k₀ (θ, 0))) * gramSection Z *
  (unipotentOf r * embedH (cayleyChart 1 η))⁻¹

set_option synthInstance.maxSize 999

attribute [-simp] Prod.forall map_mul _root_.mul_inv_rev

attribute [local simp] forall_fin_succ' coe_embedH inclMatrix_gram_eq_zero
  inclMatrix_gram_mul_eq_zero inclMatrix_gram_eq_one inclMatrix_gram_mul_eq_self actOnCols
  sectionFrame sectionMatrix val_unipotentOf_coe

/-- The real-linear map from square matrices S to the parameter space of the chart
`openCellChart` that reads each parameter from a block of S; its Z-component is F'ᴴSF,
with F = `Shape.frameCols` and F' = `Shape.dualFrameCols`. -/
noncomputable def chartCoords {𝔰 : Shape} := let r i := inr (inl (ite (i = 𝔰.k₀) (inr ()) (inl i)))
  let R S w d := ((skewCoords S).submatrix w w, S.submatrix d w, (skewCoords S).submatrix d d)
  (⟨⟨fun S ↦ (𝔰.dualFrameColsᴴ * S * 𝔰.frameCols, ((skewColumnEquiv 𝔰.k₀).symm (R S r inl).1).1,
    (R S r inl).2, -R S 𝔰.indexX₀ eStar), by simp [R, submatrix_add, ↓neg_add,
         -skewColumnEquiv_spec]⟩, by simp [R, submatrix_smul, -skewColumnEquiv_spec]⟩ : _ →ₗ[ℝ] _)

/-- The real-linear map (η, b, c) ↦ (Wη + Db)Wᴴ + (D·sk(c) − Wbᴴ)Dᴴ, where W, D have columns
x_i, e*_a and sk is `skewOfReal`. -/
noncomputable def besselTangent {𝔰 : Shape} :=
    (.mk ⟨⟨fun (η, b, c) ↦ (𝔰.definiteCols * η + 𝔰.dualCols * b) * 𝔰.definiteColsᴴ +
  (𝔰.dualCols * skewOfReal c - 𝔰.definiteCols * bᴴ) * 𝔰.dualColsᴴ, by
    simp; grind⟩, by simp [star_trivial, smul_sub]⟩ : Matrix 𝔰.κ _ ℂ × 𝔰.UnipotentParams →L[ℝ] _)

lemma logDerivU_unipotentOf_mul_embedH {𝔰 : Shape} {V} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {z' : V →L[ℝ] _ × 𝔰.UnipotentParams} {z p} (hz : HasFDerivAt z z'
  p) : let F p := unipotentOf (z p).2 * embedH (cayleyChart 1 (z p).1); DifferentiableAtU F p ∧ ∀ v,
    let (η, b, c) := z' v; logDerivU F p v = besselTangent (logDerivU (cayleyChart 1) (z p).1 η,
      b * (cayleyChart 1 (z p).1).1.1, c + skewCoords (skewAdjointPart ℝ ((z p).2.1 * bᴴ))) := by
  have h := (besselTangent ∘L .inr ..).hasFDerivAt.comp p hz.snd |>.const_mul 𝔰.J₁
  refine (fun h ↦ ⟨⟨_, h⟩, (congr(_ * $h.fderiv ·).trans ?_)⟩) ((((h.add ((h.mul'
    h).const_smul (2⁻¹ : ℂ))).const_add 1).mul' (((besselTangent ∘L .inl ..).hasFDerivAt.comp p
    (((abs_det_logDerivU_cayleyChart (det_cayleyDenom_one_ne_zero _)).1.hasFDerivAt.comp p
    hz.fst).sub_const 1)).const_add 1)).congr_of_eventuallyEq
    (.of_forall fun _ ↦ ?_)) <;> simp [besselTangent, -map_sub, star, J₁_eq, logDerivU] <;> module

lemma exists_symm_eq_chartCoords_skewOfReal {𝔰} : ∃ e : _ ≃ₗ[ℝ] _, MeasurePreserving e ∧ ⇑e.symm =
  @chartCoords 𝔰 ∘ₗ skewOfReal := by
  apply exists_measurePreserving_equiv; simp_intro _ [chartCoords, mul_inclMatrix,
    conjTranspose_inclMatrix_mul]; simp [skewOfReal, sum_univ_castSucc, div_pow,
    Fintype.sum_eq_add_sum_subtype_ne _ 𝔰.k₀, RCLike.norm_sq_eq_def]; ring_nf
  simp [sum_add_distrib, @sum_comm (Fin _) _ (@Subtype 𝔰.κ _)]; nth_rw 2 [sum_comm]; ring
  simp [finrank_matrix]; grind [@Fintype.card_pos _ _ ⟨𝔰.k₀⟩]

/-- For some measure-preserving real-linear identification e of the parameter space, at every p
with Z in Ω the chart `openCellChart` is differentiable and its logarithmic derivative has
|det| equal to g(Z)^{|κ|−1} times two Cayley weights `cayleyDensity`; g(Z) = |det Z|² − |D_ϱ|²
(`gramDiscReal`), D_ϱ the leading principal minor of order ϱ of Z. -/
lemma openCellChart_jacobian {𝔰 : Shape} : ∃ e : _ ≃ₗ[ℝ] _, MeasurePreserving e ∧
  ∀ p ∈ 𝔰.openCell ×ˢ Set.univ, DifferentiableAtU (@openCellChart 𝔰) p ∧
  |(e.symm.1 ∘ₗ skewCoords ∘ₗ logDerivU openCellChart p).det| = gramDiscReal p.1 ^ (𝔰.k - 1) *
  (cayleyDensity 1 (skewColumnEquiv 𝔰.k₀ (p.2.1, 0)) * cayleyDensity 1 p.2.2.2.1) := by
  cases Nat.exists_eq_add_of_lt (@Fintype.card_pos _ _ ⟨𝔰.k₀⟩)
  refine exists_symm_eq_chartCoords_skewOfReal.imp fun e ↦ .imp_right fun _ p ⟨hp@⟨_, _⟩, _⟩ ↦ ?_
  obtain ⟨⟨_, hγ⟩, s⟩ := differentiableAt_sectionMatrix hp, hasStrictFDerivAt_snd (𝕜 := ℝ) (p := p)
  obtain ⟨⟨a⟩, b, γ, d⟩ :=
    logDerivU_unipotentOf_mul_embedH (((skewColumnEquiv _).hasStrictFDerivAt.comp p (s.fst.prodMk
    (hasStrictFDerivAt_const ..))).prodMk s.snd.fst).hasFDerivAt,
    logDerivU_unipotentOf_mul_embedH s.snd.snd.hasFDerivAt, (hγ.congr_of_eventuallyEq
    (gramSection_eventuallyEq hp)).comp p hasFDerivAt_fst, cornerDefect_pos hp; extract_lets F at b
  have h : DifferentiableAtU openCellChart p := (a.mul ⟨_, γ⟩).mul
    (by simpa only [Ring.inverse_unit] using! b.1.inverse ⟨_, rfl⟩)
  let Δ := @diagLast 𝔰 (√(cornerDefect p.1))⁻¹; let R := 1 + 𝔰.dualFrameCols * (𝔰.frameCols -
    𝔰.dualFrameCols)ᴴ
  let M A B := 𝔰.frameCols * ((A * Δ - 1) * 𝔰.frameColsᴴ + B * Δ * 𝔰.dualFrameColsᴴ)
  let K := 1 + M p.1⁻¹ (sectionCoeff p.1ᴴ)
  have : (gramSection p.1).1.1 * K = R + M (sectionCoeff p.1) p.1ᴴ⁻¹ := by
    simp +zetaDelta [coe_gramSection, *, mul_mul_eq_of_mul_eq (diagLast_sqrt_mul_inv _)]; abel
  have q v A B : besselTangent v * M A B = 0 ∧
    (M A B)ᴴ * besselTangent v = 0 := by simp [M, besselTangent]
  have t := abs_det_skew_congruence e.symm (F p * K) (skewCoords ∘ₗ logDerivU openCellChart p)
  generalize hT : (e.symm.1 ∘ₗ _ : End ..) = T at t
  have hT w : T w = _ := .trans (by simp [← hT, conjTranspose_logDerivU, *])
    congr(chartCoords (Kᴴ * $(sub_eq_of_eq_add (logDerivU_mul h b.1 w)) * K)).symm
  simp [openCellChart, logDerivU_mul a ⟨_, γ⟩, *, F,
    (logDerivU.eq_1 ..).trans congr(_ ∘ₗ $γ.fderiv.1),
    mul_mul_eq_of_mul_eq (conjTranspose_mul _ K).symm, mul_mul_eq_of_mul_eq (q ..).2] at hT
  rw [det_mul, det_one_add_mul_comm, det_eq_mul_of_block_triangular, det_eq_mul_of_block_triangular,
    abs_mul, abs_mul, det_mulLeft_mulRight_real (p.1ᴴ⁻¹ *
    Δ)ᴴ (p.1⁻¹ * Δ), abs_det_logDerivU_col_eq_cayleyDensity, ← LinearMap.det_conj _ (.prodAssoc ..),
    det_eq_mul_of_block_triangular, det_mulLeft_mulRight_real 1 (cayleyChart 1 (skewColumnEquiv _
    (p.2.1, 0))).1.1, det_eq_mul_of_block_triangular 1, det_eq_mul_of_block_triangular
    (skewCoords ∘ₗ logDerivU (cayleyChart 1) p.2.2.2.1), det_eq_mul_of_block_triangular _ _
    (LinearMap.id.ext _), det_mulLeft_mulRight_real 1 (cayleyChart 1 p.2.2.2.1).1.1] at t
  simpa [abs_det_logDerivU_cayleyChart, mul_pow, pow_mul, Δ, diagLast, d.le, abs_of_pos, *,
    gramDiscReal_eq, prod_univ_castSucc, pow_add, field] using t.symm
  all_goals simp [*, K, chartCoords, Prod.mk_zero_zero, LinearEquiv.prodAssoc]
  rotate_right; exact fun _ ↦ .trans (by simp [R, M, besselTangent]) congr(_ * (_ *
    ($(((mulLeftLinearMap .. ∘ₗ mulRightLinearMap ..).toContinuousLinearMap.hasFDerivAt.comp _ hγ
    ).unique ((hasFDerivAt_id _).congr_of_eventuallyEq
    (.of_forall (@frameCols_gram_sectionMatrix _)))) _ * _)))
  all_goals simp [entrywise, @skewCoords.eq_1 𝔰.BesselIndex, inclMatrix, -re_sum, -im_sum, R,
    skewOfReal,
    sum_univ_castSucc, -Matrix.mul_sub, -Matrix.add_mul]; clear * -; simp [besselTangent,
    inclMatrix, mul_apply, -map_add] <;> first | (intros; simp [skewOfReal]; grind) |
    aesop (add simp skewCoords)

/-- The chart `openCellChart` is injective where Z lies in the open cell. -/
lemma openCellChart_injOn {𝔰 : Shape} : (𝔰.openCell ×ˢ Set.univ).InjOn openCellChart := by
  have u : (fun q ↦ (@unipotentOf 𝔰 q).1.1 * 𝔰.dualCols).Injective := fun _ _ e ↦ by
    simpa [by simpa using congr(𝔰.definiteColsᴴ * $e),
      Prod.ext_iff] using congr(skewCoords (𝔰.isotropicColsᴴ * $e))
  rintro ⟨Z, _, q, _, r⟩ ⟨hZ⟩ ⟨_, _, p, _, s⟩ ⟨⟩ e
  cases by simpa [openCellChart, realFrameGram_mul_invariant, realFrameGram_gramSection,
    Subgroup.mul_mem_sup, unipotentOf_mem_besselU0, *] using congr(realFrameGram $e)
  have c {x g} (e : openCellChart (Z, x) = g) := by
    simpa [coe_gramSection, hZ.1, hZ, diagLast_sqrt_mul_inv] using congr($(eq_mul_of_mul_inv_eq
      e).1.1 * (𝔰.frameCols * Z⁻¹ * @diagLast 𝔰 (√(cornerDefect Z))⁻¹))
  obtain ⟨this, e1⟩ := @u q p, (c e).trans (c rfl).symm
  simp [entrywise, inclMatrix, forall_and] at e1 this
  simp [openCellChart, cayleyChart_col_injective _ (funext e1.2.2), e1.1.elim this] at e ⊢
  simp_all [@u r s, by simpa [Units.val_inj, cayleyChart_injOn.eq_iff] using
    congr(𝔰.definiteColsᴴ * $e.1.1 * 𝔰.definiteCols)]

open Real Fintype Metric

/-- Let M ≥ 8(ϱ+1), 𝗀(Z) ≥ M⁻¹, all |Z_ab| ≤ M², P ≥ M^{9(ϱ+1)} and ‖Z' − Z‖ < P⁻⁶. Then 𝗀(Z') ≥
𝗀(Z)/2, Z' lies in Ω (`Shape.openCell`), and ‖Z'⁻¹‖, ‖Z'‖, δ(Z')^{−1/2} ≤ P, with δ =
`cornerDefect`. -/
lemma mem_openCell_and_bounds_of_near {𝔰 M P Z Z'} (hg : M⁻¹ ≤
  @gramDiscReal 𝔰 Z) (hM : 8 * (𝔰.ϱ + 1) ≤ M) (hZ : ∀ a b, ‖Z a b‖ ≤ M ^ 2) (hP : M ^ (9 * 𝔰.n) ≤
  P) (h : Z' ∈ ball Z (P ^ 6)⁻¹) : gramDiscReal Z / 2 ≤ gramDiscReal Z' ∧ IsBoundedInCell Z' P := by
  have ⟨r, m, _, _⟩ : 𝔰.n ≤ M ∧ 2 ≤ M ∧ M ≤ P ∧ 1 ≤ P := by grind [le_self_pow₀]
  have p n := hP.trans' ∘ pow_le_pow_right₀ (m := n) (by grind)
  have k := h.out.trans_le (c := 1) (by bound)
  have z {Y} (h : dist Y Z < 1) a b : ‖Y a b‖ ≤ M ^ 3 := by
    grw [norm_le_insert', hZ, ← Y.sub_apply, norm_apply_le_l2_opNorm, ← dist_eq_norm]; nlinarith
  have s l := (abs_norm_sub_norm_le ..).trans ((norm_sub_le_of_holomorphic_bdd (f :=
    (leadingMinor · l ^ 2)) (fun _ _ ↦ ⟨by simp [leadingMinor, det_apply]; fun_prop, by grw
    [norm_pow, leadingMinor, norm_det_le_norm_pow, l2_opNorm_le_of_apply
    (by tauto), ← sq, Fintype.card_fin, mul_pow, ← pow_mul, ← pow_mul, p, l.is_le, r, p] <;> lia⟩)
    _ k).trans (c := M⁻¹ / 4) (by grw [mem_ball_iff_norm.1 h]; field; nlinarith))
  have ⟨g, a⟩ : gramDiscReal Z ≤ 2 * gramDiscReal Z' ∧ 0 < gramDiscReal Z' := by
    simp_all [Fin.forall_fin_succ', gramDiscReal, leadingMinor, frameDisc, mul_conj',
      ← ofReal_pow]; grind [inv_pos]
  have ⟨n, _⟩ := mem_openCell_iff.2 a
  grw [g, m, ← inv_mul_le_iff₀, ← sq, ← le_sqrt', gramDiscReal_eq n, sqrt_mul, sqrt_sq,
    inv_le_comm₀] at hg
  have d := hg; grw [mul_le_of_le_one_right] at d; rw [mul_inv, inv_mul_le_iff₀] at hg
  simp [IsBoundedInCell, Z'.inv_def, norm_smul, mem_openCell_iff]; grw [d, l2_opNorm_le_of_apply (by
    simp_intro .. [adjugate_fin_succ_eq_det_submatrix']
    grw [norm_det_le_norm_pow, l2_opNorm_le_of_apply (by tauto), ← sq, Fintype.card_fin,
      𝔰.ϱ.le_succ, r]),
    hg, norm_det_le_norm_pow, l2_opNorm_le_of_apply (z k), ← sq, Fintype.card_fin, r]
  ring; repeat first | bound | simp [*, cornerDefect, ← pow_add]

lemma euclidean_enorm_sq_eq_sum {I} [Fintype I] (u : EuclideanSpace ℂ I) : ‖u‖ₑ ^ 2 =
  ∑ i, ‖u i‖ₑ ^ 2 := by simp [enorm, u.nnnorm_eq, ← ENNReal.coe_pow]
