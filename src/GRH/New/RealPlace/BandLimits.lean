import GRH.New.RealPlace.ComplexShells
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Band limits and energy bound for cut Bessel function at a real place. -/


open Matrix MeasureTheory Measure Fintype Real ENNReal InnerProductSpace Finset IsCutBessel Function
  Norms.L2Operator Level Gauge
variable {𝔰 : Shape} {s I} [Fintype I] {rep ρ b n} {F W : C(𝔰.G₁, EuclideanSpace ℂ I)}
  (hF : IsCutBessel F rep ρ s b W n) {p}

variable (F) in
/-- The vector Ξ(p) = ω(p)J_F(γ_p) (`normCorrelation`), with γ_p = w_{(p₁,…,p_ϱ)}·w_ϱ(p_n/min(1,
|p_n|)), n = ϱ+1, and w_ϱ the boost `cellChart`. -/
noncomputable def sieveVector p := normCorrelation (cellChart 𝔰 𝔰.ϱ (p 𝔰.ϱ)) F p

include hF
attribute [local simp] weylRatio ContinuousLinearMap.inner_map_map_of_mem_unitary upperPairing
  Unitary.map_mem cellDensity sqrt_eq_zero' abs_of_pos normCorrelation embedH_mem_floorGroup
  cellChart_mem weylElem_mul_left_comm

/-- If F satisfies `IsCutBessel`, the normalised Bessel integral Ξ(p) = `sieveVector` F p is a
continuous function of p. -/
lemma IsCutBessel.continuous_sieveVector : Continuous (sieveVector F) := .of_at fun p ↦ by
  choose L _ a _ using hF.exists_gauge_isHead _ p p 0
  refine have : Continuous fun c : (_ → ℂˣ) × 𝔰.G₁ ↦ cellChart 𝔰 𝔰.ϱ (c.1 𝔰.ϱ) :=
      continuous_U_iff_matrix.2 (.congr ?_ fun _ ↦ by simp [cellChart, field]; rfl); .smul
      (M := ℝ) ?_ (((PiLp.continuous_toLp ..).comp_continuousOn (continuousOn_pi.2 fun i ↦
      continuousOn_integral_of_compact_support (hF.gauge (by grind : _ ≤ L + 1)
    ).isCompact_hasMatSize ?_ fun c y m ↦ not_imp_comm.1 fun n ↦
      hasMatSize_of_ne_zero _ hF.isCut_complexLevel m cellChart_mem (n <| · ▸ by simp) (n <|
    · ▸ by simp))).continuousAt ((Set.finite_Iic _).eventually_all.2 fun i l ↦ (ContinuousAt.norm
    ?_).eventually_le_const ((a i l).trans_lt (by simp)))) <;> fun_prop (disch := simp [ne_of_gt])

/-- Let W, F be a cut pair of Bessel functions with the numerical conditions of `IsCutBessel`. If W
has Schur's bound with constant deg⁻¹|I|, where 0 < deg and deg·Θ ≤ b^{4r²} (Θ =
`Shape.bandConst`), then F has the band
limits `HasBandLimits` for some forms J.

Real-place Bessel integrals: band limits, energy and open-cell bound. -/
lemma hasBandLimits_of_isCutBessel [Nonempty I]
    {deg} (hd : 0 < deg) (hS : SchurLe W (.ofReal deg⁻¹ * card I))
  (hD : deg * 𝔰.bandConst ≤ b ^ (4 * 𝔰.r ^ 2)) : ∃ J, HasBandLimits b F deg J := by
  let δ := hF.complexLevel.upperPairing 0 (translatePairing F W 1) 1
  obtain ⟨c, Γ, ⟨_, _, a⟩, ⟨_, _, d⟩, hW, b2, _, B, _, v, H, l⟩ := hF.isCut_complexLevel, hF.gauge,
    hF.isCut_complexLevel.1.1, (hF.isBesselFunction .full).1, hF.isBesselFunction .full,
    hF.two_le_b, hF.k_eq, hF.isBesselFunction .cut, hF.haarRatio_spec
  choose _ _ x y _ using (hF.exists_gauge_isHead 𝔰.ϱ · · 0)
  refine ⟨fun i p q ↦ ite (i ≤ 𝔰.ϱ) (hF.formConst * hF.complexLevel.floorForm i p q
    F 1) ⟪sieveVector F p, sieveVector F q⟫_ℂ, ⟨by simp [wave], fun i p q ξ hi ↦
    .imp_right (fun e ↦ ⟨(e.trans <| by simp [·, hi, Pi.one_def]), ((congrArg _ e).trans_le <|
    hF.norm_floorForm_le hi ·.unit (by simp) (·.formModulus_sq_le_of_char c hi · ⟨⟩
    fun _ _ ↦ rfl))⟩) ?_, fun _ _ _ ↦ by simpa using! posSemidef_gram .., by
    simpa using! hF.continuous_sieveVector.fst'.inner hF.continuous_sieveVector.snd', fun p q ↦ ?_,
    fun i p q h y ↦ ite_eq_left h ▸ hF.norm_floorForm_le h y.unit (by simp)
    (·.formModulus_sq_le_of_heads c h · ⟨⟩ rfl (by simp))⟩, fun σ h p q e f ↦ by
    -- the isometry clause
    by_cases! t : ‖(p 𝔰.ϱ).1‖ ≤ 1
    simp [sieveVector, *]
    obtain ⟨k, k', rfl⟩ := cartan_decomposition h e t
    simp [sieveVector, *, inner_besselCorrelation _ c F.2 (x p q)]
    nth_rw 2 [← integral_mul_left_eq_self _ (embedH k, embedH k)]; simp [mul_assoc, ← map_inv _ k',
      -map_inv, B.3, weylElem_mul_left_comm]⟩
  obtain h | rfl := hi.lt_or_eq
  simpa [h] using Γ.integral_floorForm_succ c ⟨i, h⟩ _ ξ (hF.lintegral_formMajorant_ne_top hi)
  -- the top floor is the integral of the products of two vectors with one last entry
  refine integral_succ_floor_eq Γ c 𝔰.top ξ (hF.lintegral_formMajorant_ne_top hi)
    (hF.complexLevel.measureH_spec.1.mono unitriGroup_inf_floorGroup_last.ge) (by simp)
    ((ite_eq_right (by simp)).trans (ite_eq_left rfl)) (Place.ae_isUnit.mono fun
      | _, ⟨z, rfl⟩ => ?_)
  by_cases! hl : ‖z.1‖ ≤ 1; simp [sieveVector, *]
  erw [← stackMeasure_top, (by simp [descConv_add] : _ ∗ₘ _ = hF.complexLevel.groupMeasure), v]
  simp [sieveVector, inner_besselCorrelation _ c F.2 (x p q) (y p q), prod_smul_left,
    prod_smul_right, realFrameGram_cellChart hl,
    mul_left_comm _ (wave _), ← mul_assoc _ _ (integral ..)]
  rw [← (measurePreserving_prod_mul_swap ..).hasLaw.integral_comp (by fun_prop)]
  norm_cast; congr 3
  simp [headDensity, prod_range, ne_of_lt, ← toReal_rpow, ← one_div,
    ← sqrt_eq_rpow, mul_pow, posPart_def]; rw [toReal_ofReal (by positivity)]
  grind [formConst, toReal_ne_zero, Shape.openCellConst, 𝔰.openCellConst_pos, pow_right_comm]
  simp (disch := fun_prop) [formIntegrandOne, descConv, integral_map]
  simp [mul_assoc, weylElem_mul_left_comm, B.3]
  -- the energy
  have K {B} h := by simpa using Γ.isPairingKernel_translatePairing (W' := B) c h 0 1 1
  obtain ⟨k, k', V⟩ := K c.1, @K W ⟨hW.1, by simpa using hW.2⟩, (⟨⟨by fun_prop, _,
    (norm_sub_le_of_le (a _) <| d ·)⟩, by simp_all [hW.2, B.2, smul_sub]⟩ :
    Place.IsBessel (⇑F - ⇑W) 1)
  grw [ite_eq_left, add_div, one_div, ← ofReal_le_ofReal_iff, ofReal_add, ← (?_ : 2 * _ ≤ _ / deg),
    ofReal_mul, ← hF.formConst_mul_lintegral_le zero_le V hF.lintegral_sq_sub_le _ _ _ (fun {y} _ ↦
    ⟨y⁻¹, by simp [hF.ten_le.trans']⟩) le_rfl le_rfl, ofReal_norm, enorm_mul, enorm_floorForm_le,
    lintegral_mono fun x ↦ (?_ : _ ≤ ‖δ x‖ₑ ^ 2 + 2 * hF.complexLevel.formMajorant 0 p q F (F - W)
    x), lintegral_add_left, lintegral_const_mul', headDensity, prod_range_zero, one_mul, mul_add,
    mul_left_comm _ 2, v, lintegral_smul_measure, lintegral_le_of_forall_fin_meas_le
    (hF.haarRatio ^ 2 * card I * (.ofReal deg⁻¹ * card I)) fun s hs h ↦ ?_, show _ * _ ≤
    .ofReal deg⁻¹ by simpa [← toReal_le_toReal, field, formConst, mul_eq_top, le_of_lt, *] using l]
  any_goals first | finiteness | fun_prop | simp [Size.IsHead, Size.zero_one_mem_ofSize]
  obtain ⟨⟨D, d, f⟩, _⟩ := k'.exists_lintegral_le 0, Fact.mk h.lt_top; let β := s.indicator (star δ)
  have m q : MemLp β q := (memLp_indicator_iff_restrict hs.nullMeasurableSet).2
    (.star (.of_enorm_bound
    (by fun_prop) d.ne (.of_forall ((enorm_integral_le_lintegral_enorm _).trans <|
    f 1 ·)))); have i := memLp_one_iff_integrable.1 (m 1); have e := lintegral_enorm_sq i (m ⊤)
  grw [setLIntegral_mono' hs (g := (‖β ·‖ₑ ^ 2)) (by simp +contextual [β]), restrict_le_self,
    ← ENNReal.mul_div_cancel_right' id (e.trans_ne coe_ne_top).elim, div_le_of_le_mul]
  grw [← sq, mul_assoc, mul_assoc, ← hS _ i, ← hF.lintegral_sq_cut_le, ← sq_lintegral_le
    (by fun_prop) (Measurable.aemeasurable (by fun_prop)) fun z ↦ (mul_pow ..).le, ← mul_pow, ← H _
    (by fun_prop) (by simp +contextual [B.enorm_besselS_mul (mem_unitriGroup_of_mem_besselU _),
    hW.enorm_integral_besselS_mul (mem_unitriGroup_of_mem_besselU _)]), e,
    ofReal_le_enorm, ← Complex.ofRealLI.enorm_map, ← LinearIsometry.integral_comp_comm,
    integral_congr_ae (.of_forall fun x ↦ .trans (b := β x * δ x) (by by_cases x ∈ s <;> simp [β, *,
    RCLike.conj_mul]) (integral_const_mul ..).symm), integral_integral_swap ⟨by fun_prop,
    (lintegral_prod_le _).trans_lt ?_⟩, enorm_integral_le_lintegral_enorm]
  gcongr; simp [← inner_smul_right, integral_inner, hW.integrable_smul i, enorm, ← ENNReal.coe_mul,
    nnnorm_inner_le_nnnorm]
  simp_rw [uncurry, enorm_mul, lintegral_const_mul' _ _ enorm_ne_top]
  grw [f, lintegral_mul_const'] <;> finiteness [i.2]
  simp [formModulus, formMajorant, descConv, ← formIntegrandOne_eq Γ c]
  grw [← k.enorm_upperPairing_le, ← (K V).enorm_upperPairing_le, Eq.trans (a := δ x) (by simp [δ])
    (integral_sub (k.integrable_upperMeasure 0 1 x) ((K V).integrable_upperMeasure 0 1 x)),
    ← toReal_le_toReal, toReal_add] <;> simp [formIntegrandOne, mul_ne_top]
  grw [← abs_norm_sub_norm_le, sq_abs, sub_sq]; nlinarith
  grw [(le_div_iff₀' hd).2 hD, b2]; simp [hF.rho_eq, field, ← pow_mul, ← pow_add, *]
  gcongr; any_goals bound [hF.ten_le]
  clear * - hF; obtain ⟨_, rfl⟩ := hF.mul_cube_lt_s.dest; lia
