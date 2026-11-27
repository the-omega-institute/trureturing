/- GID: D5/S3/Zeros/GRH/New/Rows/LineArithmetic
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/LineArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.LineArithmetic. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/LineArithmetic.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Columns.SizeEstimates
import D5.S3.Zeros.GRH.New.Selmer.FitTwists
import D5.S3.Zeros.GRH.New.Rows.LineCoordinates
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Twisted theta forms lie on one line. Explicit theta forms on U(W_j), whose coefficient vectors
are integral off the conductor and small when untwisted, are for every twist multiples of one
twist-free form, with squared ratio a product of Hecke L-value ratios and a power of the conductor's
norm, and this gives the number carrying the twist. The rank one case (the lift is a scalar of
square modulus an L-value), twisting on a square block and integral theta data are known. Related
work: T. Yang, Theta liftings and Hecke L-functions, 1997; Böcherer–Schmidt, p-adic measures
attached to Siegel modular forms, 2000; Harris–Li–Skinner, The Rallis inner product formula and
p-adic L-functions, 2005.

This file: Coefficient vectors are integral off the conductor and small when untwisted. -/

open RingHom ComplexConjugate Finset Fintype Ideal Matrix MvPolynomial NeZero Real Sum

variable {P} {D : Data P} (j : D.LiftIndex)

lemma Data.norm_mul_gProd_pow_mem_modulus {ϑ c} : ↑(ϑ.levelNorm * D.gProd ^ c) ∈ (D.𝔪 ϑ
  c).ideal := by with_unfolding_all simpa [← ϑ.Q.prod_coe_sort] using! mul_mem_mul_rev (pow_mem_pow
  (span_piGBar D ▸ mem_span_singleton.2 ⟨_, D.piGBar_mul_star.symm⟩) c) (prod_mem_prod fun _ _ ↦
  absNorm_mem _)

/-- One c ≠ 0, depending on j, makes every y = conj(c·`Data.lineMultiplier` ϑ j i h) integral at h
(`weylGauge` ≤ 1) for all ι: ℂ → ℂ_p, p prime to N(Q); if Q = ∅, all Aut(ℂ)-conjugates have squared
norm ≤ exp(rB₀).

Twisted theta forms lie on one line. -/
lemma Data.lineMultiplier_integral_and_small : ∃ c ≠ (0 : ℂ), ∀ i ϑ h, let y := star (c •
    lineMultiplier ϑ j i h); (∀ p [Fact p.Prime] [PadicPlace p], p.Coprime ϑ.levelNorm →
    weylGauge _ 0 h y ≤ 1) ∧ (ϑ.Q = ∅ → ∀ φ : ℂ ≃+* ℂ, weylNormSq (φ ∘ y) ≤ .exp (D.r * D.B₀)) := by
  have ⟨n, d, H, H₀, H₁, hQ⟩ := exists_denom_linePolyCoords j
  grw [(card_detIndex j _).2, sum_const, smul_eq_mul] at d; have g :=
    d.trans (D.nat_le_of_hasLogBound (B := D.gProd))
  obtain ⟨⟨c₀, _, K₀⟩, ⟨c₁, _, K₁⟩, ⟨c₂, _, K₂⟩, c, _, E⟩ := exists_modKernel_integral_bound
    (Fin D.m) D.CarrierIndex D 0, exists_modKernel_integral_bound (Fin j) (BigIndex j) D 0,
    exists_modKernel_integral_bound (LPlusIndex j) (BigIndex j) D n,
    exists_modKernel_neg_left (stdSpace D.E (Fin j)) (stdSpace _ (BigIndex j))
  use D.chosenGroupOrder * D.chosenGroupOrder * c₂ * H * c₀ * conj c₁ *
    c, by simp [ne]; grind [norm_zero]
  intro ⟨u, i⟩ ϑ h Y
  obtain ⟨⟨hL, hY⟩, e⟩ := (Space.exists_short_basis_stdSpace P.cycloConductor_mem_different
    i.1.out).choose_spec, let b := (@hasWeight_liftChar _ D ϑ j).mul_upsilonU1_pow (bigCharExp
      j); PProd.mk b (b.inv.mul_upsilonU1_pow (.card (BigIndex j)))
  specialize K₀ (unitModulus _) ϑ.levelNorm 1 (twistedChi_hasWeight ϑ j) .one ⟨⟩ (by simp) 1
  specialize K₁ _ ϑ.levelNorm (conj ∘ Pi.single (inclMatrix _ (inl ∘ inr ∘ inl)) 1 <|
    (D.𝔪 ϑ 2).normNegOne • ·) .one e.2 norm_mul_gProd_pow_mem_modulus (by simp [apply_ite]) 1 1
  specialize K₂ _ _ (lPlusDatum ϑ j u) e.1 e.1 norm_mul_gProd_pow_mem_modulus fun _ ↦
    ite_mem.2 ⟨fun _ ↦ sum_mem fun _ _ _ _ _ ι ↦ ((ι.compAddChar _).norm_apply _).le, by simp⟩
  rw [(?_ : Y = (D.chosenGroupOrder * (D.chosenGroupOrder * 1) : ℂ) • stdClassSum
    (Kf D.E D.CarrierIndex) fun w ↦ stdClassSum (Kf D.E (Fin D.m)) fun v ↦ star
    ((_ * conj _ : ℂ) • c₂ • modKernelBilin _ _ _ _ _ (1, _) (1, h) _ ∘ (H • linePolyCoords j i)))]
  use fun p _ _ hp ↦ ?_, fun _ φ ↦ let σ := starRingAut.trans φ; by
    grw (transparency := default) [weylNormSq_comp_smul, (sqrt_le_iff.1 (sqrt_weylNormSq_classSum_le
      φ fun u ↦ sqrt_weylNormSq_classSum_le _ fun v ↦ sqrt_weylNormSq_le_of_dual σ fun w k ↦ by
    simp_rw [dotProduct_smul, dotProduct, Function.comp, ← smul_eq_mul (w _), ← map_smul, ← map_sum]
    rw [smul_eq_mul, map_mul, map_mul]
    refine norm_mul_le_of_le (norm_mul_le_of_le ((K₀ v u ?_).2 ?_ ?_ ?_ ?_ _ 1 1 ?_ ?_) ((K₁ h
      ?_).2 ?_ ?_ ?_ ?_ (starRingAut.trans σ) 1 1 ?_ ?_)) ((K₂ _ _ _ ?_).2 ?_ ?_ g ?_ σ _ _ (fun σ
      _ ↦ by rw [lPlusDatum]; split; simpa using! norm_sum_le_of_le univ fun _ _ ↦
      ((σ.toRingHom.compAddChar _).norm_apply _).le; simp) fun z hz ↦ by
      specialize k ((H : ℂ) • eval z ∘ linePolyCoords j i); grw (transparency :=
        default) [weylNormSq_comp_smul, (weylNormSq_linePolyCoords_le j _ _ σ z).2 ⟨fun τ a b ↦
        (hY (.comp σ (Φ τ)) ..).trans (by simpa using D.le_of_hasLogBound), hz⟩, (card_detIndex j
        _).2] at k; simpa [dotProduct] using k; use D.le_of_hasLogBound) <;> simp +contextual
      [smul_sum, smul_comm (_ ^ n), -aeval_eq_bind₁, apply_ite, *,
      -zsmul_eq_mul, ↓card_rowIndex] <;> clear * - <;> grind)).2]
    clear * - g d H₀ H₁; repeat grw [D.card_stdClasses_le_exp principalLevel_le_Kf]
    grw [H₁, g, card_eq_nat_card, card_GL_le, Modulus.card_resRing_le
      (levelModulus_ideal_le norm_mul_gProd_pow_mem_modulus), ← le_exp_of_log_le]
    all_goals simp [log_mul, ne, log_sqrt, pos, sqrt_eq_zero', ← pow_mul, twist_one_spec]
    grw [d]; use D.le_of_hasLogBound
  swap; ext l; simp [Y, -Pi.single_apply, inv_mul_cancel_comm, ← Pi.evalAlgHom_apply ℂ _ l (_ • _),
    lineMultiplier, bigChar, E, carrierXi, mul_classSum,
    map_classSum, ↓← Int.cast_smul_eq_zsmul ℂ H, modKernelI]; ac_rfl
  iterate 2 apply weylGauge_classSum_le_one _ (card_classAut_dvd_chosenGroupOrder (by simpa using
    D.nat_le_of_hasLogBound) le_rfl); intro
  rename_i w _; let ι := ιₚ.comp conj
  choose γ hγ _ using fun {n} [Fintype n] ↦ (exists_mul_mem_integralAbove p · 1 (stdSpace D.E n))
  erw [one_smul, star_smul, weylGauge_smul]; use mul_le_one₀ (by
    simpa [modKernel_embFin_mul (twistedChi_hasWeight ..) .one, by simpa using
      (modKernel_embFin_mul (L := Fin j) .one e.2 · · 1 1 (γ h)
      1)] using! norm_mul_le_of_le (@(K₀ _ _ (by simp)).1 p _ ⟨ι⟩ hp (hγ _) (hγ _)
    (by simp)) ((K₁ _ (by simp)).1 _ hp (by simp) (hγ h) (by simp))) (norm_nonneg _) ?_
  erw [← (?_ : (stdSpace ..).weightRep _ 0 _⁻¹ _ = star _), ← weylGauge_embFin,
    Representation.self_inv_apply, weylGauge_le_one_iff _ (hγ _)]
  use fun l ↦ @(K₂ _ _ _ (hQ i (D.shortRows i * (γ _).1.1ᵀ) l).1).1 p _ ⟨ι⟩ hp
    (sum_mem_integralAbove 1 1 (by simp) (sum_mem_integralAbove _ _ (hγ i.1.out) (hγ w))) (hγ h)
    ((hQ ..).2 _ fun τ x y ↦ let σ := ι.comp (Φ τ); by simpa [← Matrix.map_mul,
      shortRows, ← transpose_mul, mul_assoc, Function.comp_def] using! ((adeleExtension_mem_intGL σ
      (hγ i.1.out)).isIntMatrix.mul (N :=
      .map _ (adeleExtension σ)) (norm_adeleExtension_le_one _ <| hL · ·) y x))
  apply star_injective ((map_weightRep conj ..).trans _); ext
  simp [weylRep, mulVec_eq_sum, RingHom.comp, @starRingEnd_apply D.E, ← modKernelBilin_apply,
    -zsmul_eq_mul, mul_left_comm _ c₂, ← mul_sum, ← smul_sum, -coe_units_inv]
  simp_rw [← smul_eq_mul (schur ..), ← map_smul, ← map_sum]
  congr 2; apply (modKernel_embFin_mul e.1 e.1 ..).trans
  erw [twoSidedSubst_firstColsCoord _ _
    (.trans (congrArg _ (congrArg _ ?_)) (twoSidedSubst_stackedDetProd _ (detRows j i) ..))]
  simp [← modKernelBilin_apply, ← map_det, mul_pow, ← card_detIndex_add_bigCharExp,
    add_assoc, -card_sum, ← mapMatrix_apply]
  field_simp [prod_ne_zero_iff]
  ext τ (k | k) x (y | y | y | y) <;> simp [U.sum, detRows, mul_apply,
    inclMatrix] <;> split <;> simp [eq_comm]
