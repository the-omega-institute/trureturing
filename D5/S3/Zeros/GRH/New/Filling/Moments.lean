/- GID: D5/S3/Zeros/GRH/New/Filling/Moments
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/Moments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.Moments. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/Moments.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Heights.OneDeterminant
import D5.S3.Zeros.GRH.New.Trace.BadShare
import D5.S3.Zeros.GRH.New.Filling.CrudeEnergy
import D5.S3.Zeros.GRH.New.Filling.FiniteSystem
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Second moment of the Poincaré series with constant one. For the normalised Poincaré series P on
columns, the mean over level translates s of the squared Hilbert–Schmidt norm of P*sP is at most
nearly (columns)²/(expected rows), bad types carry little of P, and a variance inequality turns this
into large rank of some translate modulo any subspace of the rows. In rank one, Poisson summation on
a product of two Kloosterman sides with a sharp diagonal term is known. Related work: Herman, Beyond
endoscopy for the Rankin–Selberg L-function, 2011; Iwaniec–Li, The orthogonality of Hecke
eigenvalues, 2007; Michel–Ramakrishnan–Yang, Bessel periods on U(2,1)×U(1,1), 2023.

Phase sums are sharply dominated by local Bessel kernels. In the unfolded second moment of the
Poincaré series, the summed main terms are dominated by the quadratic form of a positive kernel of
local Bessel (orbital) integrals at a finite set of primes, with a constant near 1. With the sieve
this bounds the main term sharply. Literature: Kloosterman sums as local orbital integrals, normal
forms for Bessel double cosets and Siegel's formula are known. Related work: Jacquet–Ye, Germs of
Kloosterman integrals for GL(3), 1999; Y. Liu, Relative trace formulae toward Bessel and
Fourier–Jacobi periods, 2014; Siegel, Über die analytische Theorie der quadratischen Formen, 1935.

Part of: Translates of the columns fill the rows (see New.Filling.FillingTheorem).

Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Trace of a small central projection on the Bessel-subgroup terms is small. Sharp bound
for the second moment over elements fixing vectors with unit minors. Moment bounds for the Poincaré
series and spread of translates modulo any subspace. -/

open Module Classical Complex EuclideanSpace Finset Fint Fintype InnerProductSpace Matrix
  MeasureTheory IntegralPlace Real Matrix.Module

namespace Filling

variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰} [ok :
  S.IsAdmissible] {V} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Let x be a central idempotent of ℂ[𝖦_i] with Re x(1) ≤ b⁻⁸/2. Then Re ∑_s x(s)·ν⁻¹∑_c tr
A_S(c,s⁻¹,c) ≤ b⁻⁴D_c, where A_S sums the amplitudes of terms in the Bessel subgroup. -/
lemma re_trace_besselS_le [WeilData E] {𝔰} (S : Filling E 𝔰) [ok : S.IsAdmissible] {i x} (hx :
  IsCentralProj x) (b : (x.coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) :
  (∑ s, x.coeff s * ∑ y : _ × _, S.amplitudeSum (S.ratMiddle E).besselS y.1
  (Pi.mulSingle i s)⁻¹ y.1 (y.2, y.2) / S.unipCovolume).re ≤ (S.b ^ 4)⁻¹ * S.columnDim := by
  let T := univ.biUnion fun p : Σ i, S.chosenPlaces i ↦ {p.2.1, star p.2.1}
  have : T.StarStable := ⟨by aesop⟩
  have := Fact.mk ((mem_integralOff T).2
    (idem_mul_mem_Ô.1 ((mul_comm ..).subst ((S.inv_gIdele_smul_mem_iff ⟨idem Tᶜ, idem_mem_Ô _⟩).2
    (by simp [reduceAboveG, -reduceAt_eq_zero]; grind [reduceAt_idem, star_idem, coe_star_Ô])))))
  have ⟨P, F, hF⟩ := S.exists_isFillingLevel T
  obtain ⟨G, B, σ, _⟩ := hF.reduction_eq_iff,
    hF.floorZeroForm_le_main_term ⟨_, unitaryLevel_le_unitaryLevel_one, le_rfl⟩ 0
    (by grind [S.pow_chain]), axiomOfChoice (ok.reduction_surjective <| Pi.mulSingle i ·)
  have z g := ENNReal.toReal_pos (unitaryLevel_open_compact.1 (g := g).measure_ne_zero _ (by simp))
    (hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one)
  grw [Level.floorZeroForm, ← setLIntegral_le_lintegral, lintegral_iUnion (fun s ↦
    measurable_const_mul (S.toPlaces T (σ s))⁻¹ (measurableSet_unitaryLevel (g := F.g))) fun s t n ↦
    Set.disjoint_left.2 fun z u ↦ mt (div_mem u.out) (by simp [← G, *]),
    ← setLIntegral_mono' (measurable_const_mul _ measurableSet_unitaryLevel) fun z e ↦ by
    rw [setIntegral_congr_fun measurableSet_unitaryLevel fun y a ↦ (phase_mul_of_mem_unitaryLevel
      (unitaryLevel_one_le_normalizer a (inv_mem e))).symm.trans (by rfl)], sdiff_le,
    SemilocalField.volume_O, hF.inv_two_pow_le_groupMeasure (volume_nonunits_le le_rfl)] at B
  grw [re_le_norm, ← mul_le_mul_iff_right₀ (z 1), ← norm_smul_of_nonneg, ← measureReal_def,
    ← sq_le_sq₀, ← setIntegral_const, ← setIntegral_congr_fun measurableSet_unitaryLevel (f := fun y
    ↦ S.columnDim * ∑ s, x.coeff s * phase F.g (y * S.toPlaces T (σ s) * y⁻¹)) fun y a ↦ ?_,
    integral_const_mul, integral_finsetSum _ fun s _ ↦
    ContinuousOn.integrableOn_compact unitaryLevel_open_compact.2 (by fun_prop)]
  simp [mul_pow]
  grw [norm_sum_le, norm_mul_le, sum_mul_sq_le_sq_mul_sq, (by simpa [by simpa [-Fintype.card_pi]
    using hx.isChar.apply_inv, x.coeff_mul_apply_left, Finsupp.sum_fintype, mul_conj',
    ← ofReal_pow] using (hx.1.eq ▸ b :) :), (by simpa [← sum_mul, ENNReal.toReal_sum, ← le_div_iff₀,
    z, ← two_mul] using (ENNReal.toReal_mono (by simp [ENNReal.mul_ne_top,
    hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one]) B) :)]
  have := (z F.g).ne'; simp [field, Measure.real]
  any_goals positivity
  obtain ⟨k, rfl, o, -⟩ := exists_toPlaces_eq y
  lift k to S.latStabilizer using mem_latStabilizer_iff.2 ⟨o, a⟩
  rw [← (MulAut.conj (S.reduction k i)).sum_comp]; simp [mul_sum]; congr with s
  let l := k * σ s * k⁻¹
  erw [hx.2, show _ * _ = S.toPlaces T l by simp [l], Pi.mulSingle, Function.update_eq_iff
    (g := S.reduction l).2 (by simp_all [l]), phase]
  split_ifs with hs
  · obtain ⟨⟨k, r, o⟩, b, e⟩ := exists_toPlaces_eq hs.choose, hs.choose_spec; rw [← r] at *
    lift k to S.latStabilizer using mem_latStabilizer_iff.2 ⟨o.1, by
      simpa using div_mem (mem_latStabilizer_iff.1 l.2).2 (unitaryLevel_le_unitaryLevel_one e)⟩
    simp [↓hF.psi_simpleRootSum_eq_unipotentChar, o, by simpa [(G ..).2 e] using
      (amplitudeSum_besselU_mul isStable_besselS (u := 1) (one_mem _)
      (o.2.1 b) · 1), amplitudeSum_besselS_one, S.unipCovolume_pos.ne', columnDim]
  have {c} : IsEmpty ↥(_ ∩ S.termsOver c (S.reduction l)⁻¹ c) :=
    ⟨fun ⟨_, a, k, e, f⟩ ↦ have ⟨_, hu, δ, _⟩ := exists_besselU_mul_toBesselH a; hs ?_⟩
  simp [amplitudeSum, tsum_empty]
  let y := c.out⁻¹ * stdEmbFin δ * c.out
  have f : k * (S.inclHFin y)⁻¹ ∈ besselU := by simpa [*, y, termPosition, ratToFin_toBesselH,
    mul_assoc] using hu.termPosition_mem_besselU _
  cases eq_one_of_reduceAt_eq_one le_rfl _ _ ((forall_congr'
    (S.reduction_inclHFin_eq_one_iff (mem_unitaryLevel_of_besselU_mul f (inclHFin_mem_besselH y)
    (unitaryLevel_one.ge (by simpa [latStabilizer] using k.2))).1 (i + 1))).1
    fun _ ↦ by ext a b; cases (besselH_apply_eq_or f (inclHFin_mem_besselH y) a b) <;> simp [*, l,
    reduction_apply_congr k, reduction_apply_congr 1, -Matrix.one_apply])
  exact ⟨_, (by simpa [y] using f : k⁻¹.1 ∈ besselU).map_mem_unitriangularOn _,
    (G k⁻¹ _).1 (by simp [*])⟩

/-- Main-term estimate: under the standing hypotheses, for every set Σ of chosen places
above q₀, the `Filling.energy` of all terms over `Filling.fixingSet` Σ is
at most (1 − b⁻⁴)(1 + 9b⁻⁴)·𝖽·b^{−6k|Σ|}, where k = |κ|. -/
lemma energy_fixingSet_le [WeilData E] {𝔰} {S : Filling E 𝔰} [S.IsAdmissible] Sg D :
  energy (S.amplitudeSum .univ) (fixingSet Sg D) ≤ (1 - (S.b ^ 4)⁻¹) *
  ((1 + 9 / S.b ^ 4) * S.mainEnergy * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #Sg) := S.of_size_bounds (by
  intros; set y : ℝ := _ ^ #Sg
  obtain ⟨⟨x, u, e⟩, a, c⟩ := exists_nonneg_add_of_le S.thousand_le_b, S.ϱ_le_k,
    S.card_chosenPlaces 0 ▸ Sg.card_le_univ
  have hy : S.tailScale ^ 20 * S.besselEnergy ≤ y * S.mainEnergy := by
    grw [← IsAdmissible.besselEnergy_le]; simp [y, field]; grw [c, pow_mul _ 4 6,
      tailScale_pow_four]; ring_nf; rfl; bound
  grw [energy_le_of_linkEnergy_le _ (by tauto) (by tauto) (by simp) (fun s k ↦ ⟨Sg.image
    fun w ↦ (⟨0, w⟩, (D w).1), (prod_image (by simp)).ge, forall_mem_image.2 (⟨_, k.1 · ·⟩)⟩)
    (w := (1 + (S.b ^ 4)⁻¹) * y * S.mainEnergy) _ (by grw [← hy, ← ‹2 ≤ S.tailScale›]; bound)
    {_Λ | Sg ≠ univ} (by
    simp; intro; grw [← le_levelPrime, pow_mul _ 4 3, tailScale_pow_four]; simp [y, field,
      S.card_chosenPlaces, *]
    ring_nf; gcongr; lia), ← e, ← sub_nonneg]; field_simp; ring_nf; any_goals positivity
  simp_rw [linkEnergy, Set.univ_inter, ← ENNReal.tsum_prod]
  refine (tsum_subtype_support _).ge.trans (ENNReal.summable.tsum_le_of_sum_le fun F ↦ ?_)
  choose t σ n ht L H H' using fun j : F ↦ S.exists_hasSum_cosetAmplitude (j.1.2 ∘ sq_eq_zero_iff.2
    ∘ enorm_eq_zero.2) fun _ ⟨k, r, f⟩ l e ↦ j.1.1.2.2.1.2.2.elim j.1.1.2.2.2.2 fun ⟨w, z⟩ ↦ z l (by
    erw [← r, leadingMinor, submatrix_submatrix, ← map_splitGram_latMiddle (reduceAt _),
      ← Matrix.map_mul, submatrix_map,
      ← RingHom.map_det, Subtype.ext (((Ô E).subtype.map_det _).trans _), map_zero]
    erw [RingHom.mapMatrix_apply, ← submatrix_map, Matrix.map_mul, map_splitGram_latMiddle,
      ← submatrix_submatrix, ← frameGram, congr(frameGram _ ($f).1.1), frameGram_termPosition,
      submatrix_map, ← RingHom.map_det]; simpa)
  simp (disch := bound) only [← ofReal_norm, ← ENNReal.ofReal_pow, ← F.sum_coe_sort,
    ← ENNReal.ofReal_sum_of_nonneg]; gcongr; cases' hk : 𝔰.k with k; omega
  let r := (∏ v, √𝔰.openCellConst * ∏ a : Fin 𝔰.n,
    S.frameScaleSq v a ^ (k + 2 * a.rev)) / Fintype.card S.BesselCoord
  have c0 := 𝔰.openCellConst_pos; choose τ hτ using (Real.range_exp.ge <| S.frameScaleSq_pos · ·)
  refine le_of_tendsto_of_frequently (tendsto_finsetSum _ fun j _ ↦ (H j).norm.pow 2)
    (Filter.frequently_atTop.2 fun A ↦ let T₀ := A.biUnion univ.image ∪ univ.image t
    ⟨univ.map (.arrowCongrRight (.subtype (· ∈ T₀))), fun p h ↦ mem_map.2 ⟨(⟨p ·, by grind⟩),
    by simp, rfl⟩, le_of_mul_le_mul_left (a := r ^ 2) ?_ (by simp [r, ← hτ]; positivity)⟩)
  apply le_of_tendsto_of_frequently ((tendsto_finsetSum _ fun j _ ↦ (tendsto_finsetSum _ fun p _ ↦
    H' j p).norm.pow 2).const_mul _) ((S.exists_places_integralOff T₀).mp (.mono _ _)); rotate_right
  rintro T (o : ∀ i j, _ ∧ _) ⟨_, h₀, g, hT⟩; obtain ⟨P, G, hG⟩ := S.exists_isFillingLevel T
  obtain ⟨Y, hm, K⟩ := hG.exists_finite_sieveSystem Sg D
  apply ((Filter.Eventually.all fun i ↦ hG.sum_blocks_le_topKernel hT (j := {j // t j = t i}) _ (ht
    · |>.1) (fun j ↦ (ht j).2.1.trans congr($(j.2))) (ht i).2.2.1 (fun j ↦ hm (n j) (by simp [ht]))
    (o i · |>.1) ⟨i, rfl⟩ («π» := .cut) _ _ (o i · |>.2)
    ).exists_mem_basis_of_smallSets Metric.nhds_basis_closedBall).elim
  rintro ε ⟨p, M⟩; let V := IsUltrametricDist.closedBall_openAddSubgroup (LocProd T) p
  apply ((mul_le_mul_of_nonneg_left (S.sieve T h₀ g.1 (K V (isCompact_closedBall ..))
    le_sup_right) _).trans _).trans'
  · rw [mul_sum, ← sum_fiberwise_of_maps_to fun i ↦ mem_image_of_mem t, re_sum, mul_sum]
    use sum_le_sum (forall_mem_image.2 fun i _ ↦ by
      simpa only [← sum_subtype_eq_sum_filter, ht, subtype_univ, Subtype.prop (p := (t · = _)),
        sum_map, Nat.not_succ_le_self] using! M i ⟨V.2, isCompact_closedBall .., zero_mem V⟩)
  · unfold packetConst siegelConst; positivity
  · obtain D := ‹0 ≤ S.mainEnergy›, S.besselDegree_pos, volÔ_ne_zero (E := E)
    simp [prod_range]
    grw [← besselDegree, prod_comm, IsAdmissible.packetConst_mul_mass_le, ← sq_sqrt c0.le,
      (?_ : (1 + _) ^ _ ≤ 1 + S.b⁻¹ ^ 9), ← c]
    simp only [y, frameScaleProd, hk, pow_add, prod_mul_distrib, prod_pow, fieldLe, ← e, inv_pow,
      ← hτ, card_univ, prod_const, Fin.val_rev, Nat.succ_sub_succ, pow_mul]
    clear * - u D; rw [← sub_nonneg]; ring_nf; positivity
    grw [add_comm, add_one_le_exp, ← Real.exp_nat_mul, S.f_le_b, Real.exp_bound' _ _ one_pos] <;>
      simp [field] <;> bound
  intro i j l e; ext <;> simp only [ht, by simpa [ht] using e]; swap
  · -- the correlation integrals of the product vector are the products of the local ones
    intro i j; ext
    rw [Finset.prod_congr rfl fun v _ ↦
      (S.besselSys v).band_limits.2 _ ((ht j).1.ratToInf_mem_unitriangularOn v) _ _ ?_ ?_]
    simp_rw [normCorrelation, gram_apply, inner_smul_left_eq_smul, inner_smul_right_eq_smul,
      real_smul]
    simp only [inner, besselFn, besselCorrelation, Pi.mul_apply, Pi.inv_apply, star_def,
      prod_univ_sum, ratToInf_weylElem_mul, prod_mul_distrib, ← map_prod, sum_prod_type,
      ← integral_fintype_prod_volume_eq_prod, ← ofReal_prod]; rfl'
    repeat simp [ht, frameScaleSq, padTuple, unitOrOne, j.2]
  · intro i p
    simp [frameScaleSq.eq_1 S _ 𝔰.ϱ, div_pow, div_mul_eq_mul_div, div_sub_one, -one_div, hk,
      mul_add, unitOrOne, ↓Fin.prod_univ_castSucc, mul_pow, abs_of_pos, pow_add, Fin.rev_castSucc,
      padTuple, prod_pow, prod_range, (S.frameScaleSq_pos ..).ne', Level.headDensity,
      P.md_evalPlaces_rpow_half (h₀ _ (p _).2), @prod_comm (Fin 𝔰.ϱ), prod_eq_zero_iff, field]
    simp [sqrt_eq_rpow, rpow_pow_comm, finsetProd_rpow, ((ht i).2.2.1 _).le, prod_nonneg]
  simp [↓Filter.eventually_all, eventually_isIntegralOff, -Filter.eventually_atTop])

attribute [-simp] mul_re univ_unique Fintype.card_pi

/-- Second moment bound: under `Filling.IsAdmissible`, for i = 0, 1, the energy `Filling.energy` of
the terms outside the Bessel subgroup S(E⁺), over the s whose i-th component is that of an element
of the image S̄ of S, is at most b⁻¹²d₁, d₁ = |S̄|·D_c, D_c = `Filling.columnDim`. -/
lemma energy_compl_besselS_le [StablyUnram E] i :
    energy (S.amplitudeSum (S.ratMiddle E).besselSᶜ) {s | ∃ t ∈ S.reducedImage besselS, s i = t i} ≤
  (S.b ^ 12)⁻¹ * S.besselEnergy := S.of_size_bounds (by
  intros; obtain _ := S.ϱ_le_k, @besselFrame_castSucc 𝔰 ⟨0, pos_of_gt S.ϱ_le⟩
  grw [energy_le_of_linkEnergy_le (by bound) (by grind [IsStable, S.isStable_besselS]) ?_ (by simp)
    (fun s h ↦ ⟨image (.map (.mk i) id) ⊤, (prod_image (by intro; grind)).ge,
    forall_mem_image.2 fun p _ ↦ ⟨⟨Pi.single (0 : Fin (𝔰.ϱ + 1)) 1, by simp⟩,
    .symm ?_⟩⟩) le_rfl le_rfl ∅ (by
    simp [S.card_chosenPlaces]; grw [← ok.mainEnergy_le, codimFactor, g_le_b_pow, ← le_levelPrime]
    simp [div_pow, field, pow_mul _ 4 2, tailScale_pow_four]; ring_nf; bound)
    (by simp [linkEnergy])]; simp
  · rintro ⟨γ, n, c, c', _, ⟨_, ⟨t, ht, rfl⟩, hs⟩, ⟨k, rfl, hk⟩, ζ, hζ, h⟩
    choose X Y e h using (h · bot_le)
    have h3 : (1⁻¹ * stdEmbFin (U.of isUnit_one (scalar Unit ζ) (by simp [mul_comm, hζ])) *
        1).1 () () = k.1.1 (𝔰.besselFrame 0) (𝔰.besselFrame 0) := by
      obtain _ := congrFun (e 0) (𝔰.besselFrame 0),
        congrFun₂ (hk ▸ frameImage_termPosition) (𝔰.besselFrame 0) 0
      simp_all [classCoord_eq_fromBlocks, mul_apply, U.of, mulVec_eq_sum, Fin.sum_univ_succ]
    have := S.eq_one_of_reduceAt_eq_one (by simp; omega) _ (mem_Kf.2 fun _ _ ↦
      h3 ▸ k.2.isIntMatrix _ _) fun w ↦ by
      ext; convert hs ▸ reduction_apply_congr 1 i w
        (mem_besselS_iff_frameImage.1 ht (𝔰.besselFrame 0) 0 bot_le)
      use congr(reduceAt _ ⟨$h3, _⟩); simp
    cases (by simpa [U.of] using congr($this.1 () ()) : ζ = 1)
    cases n (mem_besselS_iff_frameImage.2 fun j ↦
      wellFounded_lt.fix fun b ↦ by clear * - e h; grind [congrFun
      (e b) j, mulVec_apply_eq_sum, Fintype.sum_eq_single b, Matrix.one_apply, submatrix_apply])
  obtain ⟨_, ⟨k, hk, rfl⟩, h⟩ := h; have := (mem_besselS_iff_frameImage.1 hk · 0)
  simp [h, ← intGL_map_reduceAboveG, Units.smul_def]; simp_all [funext_iff, mulVec_eq_sum,
    inclMatrix, -Sum.forall, ite_eq_iff', ← Submonoid.one_def, ← ZeroMemClass.zero_def])

/-- Let Θ ≥ 0 on 𝖦 have positive type, sum over each Ω at most the `Filling.energy` of all
terms over Ω, and vanish unless s
fixes given nonzero frame vectors modulo w or w̄ for all w ∈ A (chosen places above q₀). Then
∑Θ ≤ (1 + 9b⁻⁴)·𝖽·b^(−6|κ||A|).

Second moment of the Poincaré series with constant one. -/
lemma sum_le_of_positive_type [WeilData E] {Θ : _ → ℝ} (h0 : ∀ s, 0 ≤ Θ s) (u : _ → V) (hu :
  ∀ a b, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) A (D : ∀ _, _) (hB : ∀ Ω, ∑ s with s ∈ Ω, Θ s ≤ energy
  (S.amplitudeSum .univ) Ω) (hA : ∀ s, Θ s ≠ 0 → ∀ w ∈ A, s ∈ S.vectorFixer (i := 0) w (D w)) :
  ∑ s, Θ s ≤ (1 + 9 / S.b ^ 4) * S.mainEnergy * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #A := by
  induction' A using WellFoundedGT.induction with A ih generalizing V Θ D
  obtain ⟨hq, q, _⟩ := S.levelPrime_le 0, S.le_levelPrime 0, S.thousand_le_b, univ.sum_nonneg' h0,
    S.ϱ_le_k; by_contra! hK
  apply hK.not_ge
    (le_of_mul_le_mul_left (.trans _ (energy_fixingSet_le A D)) (by bound [@one_lt_pow₀ ℝ]))
  grw [← hB, one_sub_mul, sub_le_comm, ← sum_sdiff_eq_sub (by simp), ← sum_filter_ne_zero]
  obtain hw | ⟨w, hw⟩ := em' (Exists (· ∉ A))
  · rw [Finset.sum_eq_zero (by simp; grind [fixingSet])]; bound
  choose! L hL using fun s (e : s ∉ S.fixingSet A D) h ↦ by simpa using (e ⟨hA s h, .inr ⟨w, ·⟩⟩)
  grw [← Finset.sum_fiberwise _ L, sum_le_card_nsmul _ _ (3 * univ.sum Θ / S.b ^ 10)
    fun l _ ↦ let F b := frameImage (cond b (S.latMiddle (ResField w.1)).splitGram 1) *
      inclMatrix (ResField w.1) (Fin.castLE l.is_le)
    (le_div_iff₀' (by bound)).2 (.trans ?_ ((card_mul_sum_det_le (.mk' (· 0 w) (by simp)) F h0 hu
    (univ.sum Θ / S.b ^ (6 * 𝔰.k)) (by bound) fun b v hv ↦ by
    grw [sum_filter, ih _ (ssubset_insert hw) _ (fun a ↦
      basisFun _ ℂ (cond b invTransposeGL 1 (a 0 w) • F b *ᵥ v) ⊗ₜ[ℂ] u a) _
      (Function.update D w ⟨b, _, (map_ne_zero_iff _ (inclMatrix_mulVecLin_injective (Fin.castLEEmb
      l.is_le) _)).2 hv⟩) (.trans (by gcongr; bound) <| hB ·), ← hK] <;> simp
      [*, apply_ite ofReal, ite_nonneg, pow_succ, field, inner, smul_smul, ← eq_inv_smul_iff]
    · exact fun s h _ ↦ ⟨by cases b <;> simp [vectorFixer] <;> (repeat erw [mul_smul]) <;>
        simpa [F, ← mul_inclMatrix, ← mulVec_mulVec, inv_smul_eq_iff] using! h.symm, by grind⟩
    tauto).trans ?_))]
  · simp [field]; grw [← le_self_pow₀, ← k_le_b, ← S.ϱ_le_k] <;> push_cast <;> nlinarith
  · gcongr <;> simp [*, sum_nonneg', subset_iff, F, transpose_splitGram, mul_inclMatrix,
      ← inclMatrix.eq_1, card_eq_nat_card, ↓card_resField_eq_levelPrime]; bound
  grw [mul_div_left_comm, div_le_one_of_le₀]; linarith
  grw [← sq_le_sq₀, mul_pow, sq_sqrt, card_eq_nat_card, card_resField_eq_levelPrime, hq, hq]
  simp [← pow_mul, ← pow_add]; repeat bound [l.2]

/-- Under `Filling.IsAdmissible`, let x be a central idempotent of ℂ[𝖦_i]. The ℓ² norms of the rows
of the block matrix (∑_t x(t)ν⁻¹A_T(c, t⁻¹, c')), T the complement of 𝖲(E⁺), sum to at most
b⁻⁴D_c, D_c = `Filling.columnDim`. -/
lemma sum_norm_amplitudeSum_le [StablyUnram E] i {x} (hx : IsCentralProj x) : ∑ a :
  _ × _, ‖WithLp.toLp 2 fun b : _ × _ ↦ ∑ t, x.coeff t * (S.amplitudeSum (S.ratMiddle E).besselSᶜ
  a.1 (Pi.mulSingle i t)⁻¹ b.1 (a.2, b.2) / S.unipCovolume)‖ ≤ (S.b ^ 4)⁻¹ * S.columnDim := by
  let φ : _ →* S.GRes := .mulSingle _ i; have := S.thousand_le_b
  let Y s := ∑ c, ∑ c', ‖∑ t,
    x.coeff t • S.amplitudeSum (S.ratMiddle E).besselSᶜ c ((φ t)⁻¹ * s) c'‖ ^ 2 / S.unipCovolume ^ 2
  have h := ((card_nsmul_le_sum {s | s ∈ S.reducedImage besselS} Y (Y 1) fun σ
    h ↦ ?_).trans ?_).trans (S.energy_compl_besselS_le (i + 1))
  · simp [besselEnergy, ← card_subtype, field] at h
    grw [← sq_le_sq₀, sq_sum_le_card_mul_sum_sq, show ∑ _, _ = Y 1 by simp [Y, φ, norm_sq_eq,
      sum_prod_type, ← sum_div, div_pow, mul_div, @sum_comm S.Classes _ S.BesselCoord],
      (le_div_iff₀ _).2 h] <;> simp [columnDim, field, sum_nonneg'] <;> bound
  choose p σ₀ h₀ h₁ using (exists_besselS_mem_termsOver · (mem_filter.1 h).2)
  apply congr(∑ c, $(sum_bijective p (Finite.injective_iff_bijective.1 fun c d h ↦
    (eq_and_mem_classUnip_of_besselS (by aesop)
    (mul_inv_cancel σ ▸ termsOver.mul (h₁ c) (.inv (h ▸ h₁ d)))).1) _ _ fun d ↦ .symm ?_)).le
  obtain ⟨u, hu, η, hη, e⟩ := mem_besselS.1 (h₀ d)
  choose k hk using fun v ↦ exists_toBesselH_eq (hη.ratToInf_mem_unitriangularOn v)
  let A v := (S.besselSys v).rep (k v); let := @instDecidableEqProd
  rw [← Unitary.norm_map ⟨_, Unitary.map_mem (toEuclideanCLM (𝕜 := ℂ)) (kronecker_mem_unitary
    (one_mem _) (UnitaryGroup.map_star ⟨(S.unipotentChar (S.ratToFin u))⁻¹ • kroneckerPi (A ·), by
    erw [mem_unitaryGroup_iff, star_smul, smul_mul_smul, ← kroneckerPi_one, ← funext (A · |>.2.2),
      kroneckerPi_mul, mul_conj', norm_inv, norm_selfDualChar]
    ext; simp [mul_apply, kroneckerPi]⟩).2)⟩, map_sum]
  congr! 4; rw [map_smul, ← amplitudeSum_move (by grind [IsStable, S.isStable_besselS]) _
    (S.classUnip _).one_mem.2 _ (h₁ _)] <;> simp [h₀, mul_mem_cancel_right]
  intros; ext; simp [e, besselKernel, mul_assoc, besselFn_ratToInf_mul hu, mulVec_apply_eq_sum,
    sum_prod_type]
  simp [besselFn, hk, ((besselSys ..).tail.isBesselFunction _).3, kroneckerPi, ↓mulVec_eq_sum,
    Fintype.prod_sum, mul_sum]; ac_rfl
  simp_rw [Y, energy, ← @sum_comm S.GRes, ← sum_div]; gcongr
  refine .trans ?_ (by simpa [apply_ite, sum_ite] using
    hx.sum_norm_conv_le φ fun s ↦ ite (∃ t, _) (S.amplitudeSum ..) 0)
  grw [← subset_univ]
  congr!; aesop

/-- Filling: let ρ be unitary, ⟨ρ(s)Qe_y, Qe_x⟩ = c·(amplitude sums), c > 0, R = ρ(∏g_i) for
central idempotents with Re(1−g_i)(1) ≤ b⁻⁸/2, rank R ≤ |𝖦|·deg·mass. Each subspace F of im
R, of share φ, has an s with dim (Rρ(s)Q)⁻¹F ≤ ½(1 + φ + 19b⁻⁴)D_c. -/
lemma Fits.exists_translate_finrank_comap_le [WeilData E] {g c} [Module.Finite ℂ V] {ρ :
  Representation ℂ _ V} (hρ : ∀ s x y, ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) {Q :
  EuclideanSpace ℂ (_ × _) →ₗ[ℂ] V} (hQ : ∀ s x y, ⟪ρ s (Q (.single y 1)), Q (.single x 1)⟫_ℂ =
  ofReal c * S.amplitudeSum .univ x.1 s y.1 (x.2, y.2)) (hg : ∀ i, IsCentralProj (g i)) (hb : ∀ i,
  ((1 - g i).coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) (hc : 0 < c) (hD : finrank ℂ (ρ.asAlgebraHom
  (piTensorElem g)).range ≤ Nat.card S.GRes * S.besselDegree * mass E 𝔰.r) : IsSpread
  ((ρ.asAlgebraHom (piTensorElem g)).rangeRestrict ∘ₗ ρ · ∘ₗ Q) (19 / 2 * (S.b ^ 4)⁻¹) := by
  set R := ρ.asAlgebraHom (piTensorElem g); intro F φ; apply S.of_size_bounds; intros
  obtain ⟨⟨t, ht⟩, G, B, o⟩ := (isSquare_iff.2 (mul_pos hc S.unipCovolume_pos).le).inv,
    IsCentralProj.piTensorElem hg, S.amplitudeSum_split .univ (S.ratMiddle E).besselSᶜ,
    (hg · |>.one_sub); let P := t • Q
  have hu a b x y : ⟪ρ b (P (.single y 1)), ρ a (P (.single x 1))⟫_ℂ =
      S.amplitudeSum .univ x.1 (a⁻¹ * b) y.1 (x.2, y.2) / S.unipCovolume := hρ a⁻¹ .. ▸ by
    simp [← End.mul_apply, ← map_mul, P, ← mul_assoc, ← ofReal_mul, ← ht, hQ, field, hc.ne']
  have pr {z} (hz : IsCentralProj z) y : ⟪_, _⟫_ℂ = _ :=
    (hz.self_adjoint ρ 1 (innerₛₗ ℂ) hρ y _).trans congr(⟪y, $(hz.1.map ρ.asAlgebraHom) y⟫_ℂ)
  have hb' i := add_le_add (S.re_trace_besselS_le (o i) (hb i)) ((sum_norm_amplitudeSum_le i
    (o i)).trans' (sum_le_sum fun a _ ↦ (PiLp.norm_apply_le _ a).trans' (re_le_norm _)))
  refine (exists_le_of_sum_le univ_nonempty (g := fun _ ↦ S.columnDim / 2 * (1 + 9 * (S.b ^ 4)⁻¹ +
    φ)) ((sum_le_sum fun s _ ↦ finrank_sub_le_re_inner_dyadSum (stdOrthonormalBasis ..) (ρ s ∘ₗ P)
    (ρ.asAlgebraHom (1 - piTensorElem g)) (F.comap (R.rangeRestrict ∘ₗ ρ s ∘ₗ Q)) (F.map
    R.range.subtype) (Eq.trans_le ?_ (S.sum_norm_amplitudeSum_le 0 (.one_sub ⟨.zero, by simp⟩)))
    fun _ ↦ (⟨_, F.smul_mem t ·, by simp [P, R]⟩)).trans ?_)).imp fun s h ↦ ?_
  · congr! 2; ext; rw [← basisFun_inner]
    simp [inner_sub_right, LinearMap.adjoint_inner_right, inner_single_left, hu,
      amplitudeSum_besselS_one, ite_div, add_div, B, apply_ite, S.unipCovolume_pos.ne',
      Finsupp.single_apply, MonoidAlgebra.one_def]; grind
  · grw [← re_sum, ← sum_inner, re_le_norm, norm_inner_le_norm, ← sq_le_sq₀, mul_pow,
      @norm_sq_eq_re_inner ℂ, inner_sum_sum_eq_card_mul (energy (S.amplitudeSum .univ) {·}) ?H]
    simp [@norm_sq_eq_re_inner ℂ, ↓inner_dyadSum, apply_ite, ← Submodule.coe_inner, mul_pow,
      ← show φ *
      _ = _ from div_mul_cancel_of_imp (mod_cast by bound [F.finrank_le]), orthonormal_iff_ite.1]
    grw [sum_le_of_positive_type (fun _ ↦ by unfold energy; positivity) _ ?H ∅ (fun _ ↦
      ⟨⊤, 1, by simp⟩) _ nofun, hD, ← four_mul_le_sq_add]
    simp [mainEnergy]; field_simp [mass_pos, besselDegree_pos, ne_of_gt]; any_goals positivity
    repeat norm_num [energy, sum_filter, norm_sq_eq, sum_prod_type, sum_div, hu, div_pow,
      @sum_comm S.Classes _ S.BesselCoord, @sum_comm S.GRes]
  have k := univ.sum_nonneg' fun y ↦ pr (.piTensorElem o) (P (.single y 1)) ▸ inner_self_nonneg
  simp [add_div, show piTensorElem (1 - g ·) = ∑ i,
    piTensorElem (Pi.mulSingle i (1 - g i)) - (1 - piTensorElem g) by
    ext; simp [← map_one piTensorElem, -map_one]; ring, ↓@norm_sq_eq_re_inner ℂ, ↓hρ, columnDim,
    ↓pr G.one_sub, mul_add, mul_sum, @sum_comm (_ × _), asAlgebraHom_piTensorElem_mulSingle, B, (by
    simpa using congr(ρ.asAlgebraHom $(G.2.commute (.single s 1)) ·).symm),
    asAlgebraHom_eq_sum (ρ.comp _), by simpa using (hu · 1)] at *
  linarith
