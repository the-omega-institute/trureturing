/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/OneVector/OneVector
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/OneVector/OneVector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.OneVector.OneVector. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/OneVector/OneVector.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Analytic.Landau.PolarLandau
import D5.S3.Zeros.GRH.Lib.SiegelWeil.Formula.SiegelWeilFormula
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Siegel's formula for representing a number by a hermitian form, and local density
bounds. The form here is a sum of at least three norms over a CM field with enough roots of unity, a
splitting character and a self-dual lattice, and any level and test function are allowed. The
singular series is left as one adelic Fourier integral, read off the Siegel-Weil formula, and local
densities are only bounded above, by a zeta value. Source: A. Weil, Acta Math. 113 (1965), Thm 5 for
one vector; for the classical case, C. L. Siegel, Ann. of Math. 36 (1935); H. Braun, Zur Theorie der
hermitischen Formen, Abh. Math. Sem. Hamburg 14 (1941).

This file: Siegel's mean value formula for representing one number by a sum of norms. -/
seal Finset.univ Finset.sum Finset.prod

open NumberField Real Matrix MeasureTheory Complex Finset Function WeilData Space Int AddChar
  GaussianFourier FractionalIdeal CompleteSplitting Splitting Prod Fintype Lagrangian Nat
  FourierTransform MatMul
attribute [-simp] map_vadd vadd_fst vadd_snd setIntegral_measure_zero measure_univ
attribute [local simp] Set.indicator Splitting.symm map_add_eq_mul prod_pow conj_mul'
  snd_sum fst_sum
  pi_pos im_pos differentIdeal_ne_bot map_sub_eq_div Space.vecAtPoint Circle.smul_def Units.smul_def
  funext_iff le_of_lt mul_add mul_sum hyperbolicSplitting trace Complex.exp_neg mixedValue add_mul

/-- Laplace's integral for 1/Γ: for an integer k ≥ 1 and real x ≥ 0, the integral over real z of
e^{2πixz} (1 + 2πiz)^{−(k+1)} equals x^k e^{−x} / k!. -/
lemma integral_fourierChar_mul_inv_pow {k} (hk : 1 ≤ k) {x} (hx : 0 ≤ x) : ∫ z,
    𝐞 (x * z) * ((1 + 2 * π * .I * z : ℂ) ^ (k + 1))⁻¹ = x ^ k * cexp (-x) / k ! := by
  have hg : ?g = 𝓕 fun t ↦ toNNReal t ^ k * cexp (-t) / k ! := ?_
  show ∫ z, _ * ?g z = _
  simpa [fourierInv_eq, hx] using congr(𝓕⁻ $hg x).trans
    (Integrable.fourierInv_fourier_eq (.of_integral_ne_zero (by simpa [fourier_eq] using congr($hg 0
    = 0))) (hg ▸ (integrable_inv_one_add_sq.comp_mul_left' two_pi_pos.ne').mono' (by fun_prop)
    (by simp [norm_eq_sqrt_sq_add_sq]; grw [← hk] <;> simp [sq_nonneg, add_nonneg])) (by fun_prop))
  ext; rw [← div_div_cancel_left', ← laplace_pow] <;> simp [fourier_eq', Complex.exp_add,
    ← integral_indicator, ← integral_div]; grind [ofReal_zero, zero_pow]

/-- Siegel's formula. Let n = |κ| ≥ 3, K ⊂ K₀ open, Φ₀ ≥ 0 K-invariant Schwartz–Bruhat, α = ᾱ
totally positive. Then ∑_{x∈E^n, x*x=α} Φ₀(h⁻¹x) converges, and its K-class sum is (class sum of
1)·|D_E|^{1/4}·∏_v π^n α_v^{n−1}/(n−1)!·∫∫Φ₀(x)ψ_f(z(x*x−α)/2) dx dz, z = z̄ a finite adele,
measures `volÔ`, `volume_codifferent`. -/
lemma classSum_norm_eq {E κ : Type} [Field E] [CMType E] [WeilData E] [Fintype κ]
  (hk : 3 ≤ card κ) (K : Subgroup (Gf E κ)) [ho : IsLevel K] (Φ₀ : LocallyConstant _ NNReal)
  (hi : ∀ k ∈ K, ∀ x, Φ₀ (↑k *ᵥ x) = Φ₀ x) (b : HasCompactSupport Φ₀) {α : E} (hα : star α = α)
  (hα' : ∀ v, 0 < (Φ v α).re) : let F (z : selfAdjoint _) := ∫ x,
    (ψf E ((2⁻¹ : E) * (z.1 * (star x ⬝ᵥ x - α))) : ℂ) ∂volume.withDensity (Φ₀ ·)
  let σ (h : Gf E κ) x := if star x ⬝ᵥ x = α then Φ₀ (h⁻¹.1.1 *ᵥ (x ·)) else 0
  (∀ h, Summable (σ h)) ∧ ((classSum stdRatPoints K fun h ↦ ↑(tsum (σ h)) : ℝ) : ℂ) =
  (classSum stdRatPoints K 1 * √√|NumberField.discr E| *
  ∏ v, π ^ card κ / (card κ - 1)! * (Φ v α).re ^ (card κ - 1) : ℝ) * ∫ z, F z := by
  intro F σ; let γ (x : κ → 𝔸 E) := cexp (-∑ v, ((star x ⬝ᵥ x).1 v).re); let D :=
    hyperbolicSplitting E Unit
  have ⟨f, hf⟩ := (⟨by simp, Φ₀.2.comp (↑), _, b, by simpa using! subset_closure⟩ : IsSchwartzBruhat
    .univ _).mem_of_cosets (.comap (.pi fun x ↦ γ (xᵀ ()) • .proj (x · () |>.2)) (LinearMap.pi
    (mixedValue (stdSpace ..) D · |>.1)).range) fun _ _ ↦ ⟨⊤, by simp, fun u z _ _ ↦ ?_⟩
  let R := maximalRealSubfield E
  let p (x : (_ → ℝ) × selfAdjoint _) : 𝔸 E := ((x.1 ·), x.2.1)
  let r (x : selfAdjoint (𝔸 E)) : _ × selfAdjoint _ := ((x.1.1 · |>.re), ⟨_, congr($(x.2).2)⟩)
  have Z x z : p (r x + z) = x + p z := by ext <;> simp [p, r, conj_eq_iff_re.1 congr($(x.2).1 _)]
  let ι : R →+ _ := .mk' (r ⟨toAdele ·, (star_toAdele _).trans (by simp [star])⟩) (by simp [r])
  choose Ω hΩ b v u using exists_fundDomain_prod ι (codifferent E 1) (.mk0 (differentIdeal ℤ
    (𝓞 R))⁻¹ (by simp)) (fun a ↦ by
    simp [mem_inv_iff, ← algebraMap_mem_Ô, forall_ψf_mul_eq_one, mul_comm a,
     ← @IsIntegralClosure.isIntegral_iff _ ℤ, ← isIntegral_algebraMap_iff (A := R) (B := E), R,
     mul_comm (ι a).2.1, codifferent,
      differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 R) (𝓞 E)]
    exact Ideal.map_le_iff_le_comap (K := (Subalgebra.toSubmodule ⟨_, @coe_mem_Ô E _ _⟩).comap
      (.toSpanSingleton ..))) (fun z ↦ (exists_sub_mem_Ô (stdLattice.traceOneAdele * z.1)).imp' _
    fun _ h _ ↦ ψf_of_mem ∘ mul_mem (by simpa [← add_mul, ← map_add, sub_add_sub_comm,
    ← trace_maximalReal_eq_add_star] using! add_mem h (star_mem_Ô h))) exists_mixedEquiv_maximalReal
  let s := ι.ofInjective (by simp [Injective, ι, r])
  let D' (a : R) : type_of% D := by use D.l + (j⁻¹ * a.1) • D.k, D.k, 0 <;> simp [D,
    ← ext_iff, mem_maximalRealSubfield_iff_star_eq.1]
  have i : Injective (lagrangian ∘ D') := fun _ _ h ↦ (h.ge ⟨1, rfl⟩).elim (by simp +contextual [D',
    D])
  choose hs _ H using siegel_weil _ D (by simpa); have := s.surjective.countable
  let o z :=
    (stdAddChar E ((2⁻¹ : E) * (p z * α)))⁻¹ • splitWeil _ _ (D.radicalElt 0 (p z • 1), 1) f
  have N z x : mixedValue _ D (replicateCol _ x) (o z) = γ x * Φ₀ (x · |>.2) * stdAddChar E ((2⁻¹ :
    E) * (p z * (star x ⬝ᵥ x - α))) := .trans (by
    simp [o, sourceTerm_radicalElt, mul_sub]; ring) congr($hf (replicateCol _ x) * _)
  let G v t := 𝐞 ((Φ v α).re * t) * (∫ w : ℂ, cexp (-(1 + 2 * π * .I * t) * ‖w‖ ^ 2)) ^ card κ
  let P z := (∏ v, dcomp @G (fst z) v) * F z.2
  have e := IsAddFundamentalDomain.mk' (μ := volume.prod volume) (hΩ.prod
    (isOpen_codifferent ..).measurableSet).nullMeasurableSet (s.existsUnique_congr_right.1 <| u ·)
  have W β z : P (s β +ᵥ z) = (lagrangian (D' β)).zeroTerm _ (o z) := by
    simp [P, G, F, ← integral_fintype_prod_volume_eq_prod,
      integral_withDensity_eq_integral_smul Φ₀.continuous.measurable]
    erw [zeroTerm_lagrangian_eq_theta, (D' β).symm.symm_homSource_zeroTerm_eq_integral,
      ← (θ _).integral_comp_comm (by fun_prop),
      ← (volume_measurePreserving_piCongrLeft _ (.symm (.prodPUnit _))).integral_comp',
      ← integral_fintype_prod_volume_eq_pow, ← integral_const_mul (∏ _, _), ← integral_prod_mul,
      ← (volume_measurePreserving_arrowProdEquivProdArrow ..).integral_comp']
    congr with x; convert N _ x
    simp [↓N, γ, dotProduct, stdAddChar, p, map_ofNat, fourierChar, ← Complex.exp_add,
      ← Complex.exp_sum, mul_mul_mul_comm _ (Φ₀ _ : ℂ), @sum_comm _ _ κ, ← ofReal_pow, sum_mul,
      ← sum_neg_distrib, ← sum_add_distrib, NNReal.smul_def]; congr! 3; simp [← mul_sum]; ring!
    erw [← sourceTerm_eq_mixedTerm _ _ (replicateCol _ x), Matrix.one_mul, sourceTerm,
      ← zeroTerm_homSource_congr _ _ D.gram_kk rfl, ← sourceTerm_zero, sourceTerm_varrho,
      Z, show kCoord (D' β).symm = D.kCoord + star (toAdele (j⁻¹ * β.1)) • D.lCoord by
      simp [kCoord, lCoord, lAdelic, kAdelic, D', D.l.map_add, D.k.map_smulₛₗ _ toAdele]]
    simp; erw [N]; simp [mul_sub, ← map_mul, ← mul_assoc, div_eq_inv_mul]; ring
  have io := ((by fun_prop : Continuous o).continuousOn.integrableOn_compact (μ := volume.prod
    volume) (b.isCompact_closure.prod (isCompact_codifferent E isUnit_one))).mono_set
    (by grw [← subset_closure])
  have hP := e.integral_eq_tsum'' P ⟨(funext (by simpa using W 0 ·) : P = _) ▸
    Continuous.aestronglyMeasurable (by fun_prop), by
    simp [HasFiniteIntegral, e.lintegral_eq_tsum'', ← s.tsum_eq,
      W]; grw [(Lagrangian.zeroTerm ..).le_opENorm]
    simpa [lintegral_const_mul'] using
      ENNReal.mul_lt_top (hs.comp_injective i).tsum_ofReal_lt_top io.2⟩
  simp [← s.tsum_eq, W, (Lagrangian.zeroTerm ..).integral_comp_comm io] at hP
  let g := (cexp (∑ v, (Φ v α).re) * √√|discr E|) • ∫ z in Ω ×ˢ codifferent E 1,
    o z ∂volume.prod volume
  have A ξ h : mixedValue _ D (replicateCol _ (1 *ᵥ toAdele ∘ ξ)) (splitWeil _ _ (1, h) g) =
    σ h.2 ξ := by
    simp_rw [one_mulVec, mixedValue_splitWeil, ← replicateCol_mulVec, g, map_smul,
      ← (mixedValue ..).integral_comp_comm io, N, γ, σ, by simpa [↓move_vecAtPoint] using
      ((stdSpace ..).move h).stdForm_vecAtPoint, ← map_sub]
    split_ifs with q
    simp [↓q, v, Int.norm_eq_abs, ← ofReal_mul, ← cast_abs, abs_discr_eq_discr_sq, field, entrywise,
      coeIdeal_absNorm, absNorm_differentIdeal R, ↓measureReal_def, discr_ne_zero]
    rfl
    contrapose q; refine sub_eq_zero.1 (isDualFamily_ratAdeles.6 _ fun t ↦ (right_eq_mul₀ q).1 ?_)
    erw [mul_smul_comm, ← integral_const_mul, e.setIntegral_eq (e.vadd_of_comm (r ⟨_, .add_star_self
      t⟩)), (measurePreserving_vadd ..).setIntegral_image_emb (measurableEmbedding_addLeft _),
      ← stdAddChar_half] <;> simp [hα, ι, Z, -map_sub, -map_mul, ← star_dotProduct, mul_comm _ t,
      mul_left_comm _ (_ * Φ₀ _ : ℂ), -Prod.forall, ← toAdele.map_mul, @forall_comm (_ × _)]
  have X h :=
    ((Equiv.mk _ (·ᵀ ())).hasSum_iff.2 (hasSum_theta_sourceTerm ..)).congr_fun (A · h |>.symm)
  have Y h := by exact_mod_cast (X h).tsum_eq
  use (mod_cast X ⟨1, ·⟩ |>.summable)
  have Q (f : _ → ℝ) hΓ hf := (eq_inv_mul_iff_mul_eq₀ (by simp)).1
    ((stdSpace ..).integral_quotMeasure_eq_classSum (f := f) hΓ (by simp) K (hf ·)
    (isLocallyConstant_of_eventually_mul ((ho.2.eventually_mem K.one_mem).mono hf)).continuous.snd')
  rw [← Q _ (fun _ ↦ by simpa only [← ofReal_inj, Y] using! (pairThetaKer ..).swap.theta_rat_mul _)
    (by simp +contextual [← mulVec_mulVec, σ, by simpa using (hi ·⁻¹)]), ← Q]
    <;> simp [Y, ← integral_complex_ofReal, -θ_apply]
  cases le_iff_exists_add'.1 hk; rw [H, ← i.tsum_eq]
  simp [g, ← hP, tsum_mul_left, ↓integral_prod_mul (∏ v, dcomp @G · v), G, mul_pow, P, *,
    ↓integral_fintype_prod_volume_eq_prod, ↓integral_cexp_neg_mul_sq_norm, division_def,
    integral_fourierChar_mul_inv_pow, mul_left_comm (𝐞 _).1, ← Complex.exp_sum]
  field_simp (disch := simp)
  refine support_subset_iff'.2 fun L k ↦ (eq_of_le fun y hy ↦ ⟨y ∘ .inr, .symm ?_⟩ : L =
    lagrangian D) ▸ by simpa [zeroTerm_lagrangian_eq_theta, sourceTerm,
    σ, show 0 ≠ α from (by simp [← ·] at hα')] using A 0 1
  ext ⟨⟩ <;> simp [D]; contrapose k
  use ⟨j * y (.inr ()) / y (.inl ()), mem_maximalRealSubfield_iff_star_eq.2 (by simpa [mulVec, k,
                               dotProduct, field, add_eq_zero_iff_neg_eq] using (L.2 y).1 hy y hy)⟩,
    eq_of_le fun _ ↦ forall_exists_index.2 fun t e ↦ ?_
  convert L.1.smul_mem (t () / y (.inl ())) hy; simp [← e, D', D, field]
  have ⟨t, _⟩ : IsUnit ((fun w ↦ √(2 * π * (Φ w j).im)⁻¹, (WeilData.α * u⁻¹).1) : 𝔸 E) := by
    simp [Prod.isUnit_iff, Pi.isUnit_iff, ne_of_gt]
  let D := D.homSource (stdSpace E κ)
  choose g c h using (D.exists_isAdapted_and_frame_eq (star t • 1)).imp fun _ ↦
    (·.1.mixedTerm_omega_vacElem)
  use c⁻¹ • ϱ _ (D.lAdelic *ᵥ (0, -z ·.1)) (ω _ g (vacElem _)); ext x
  simp [x.one_mul ▸ sourceTerm_eq_mixedTerm _ (stdSpace ..) x, D, *,
    vacElem_apply_eq_prod_lineTheta, γ, vacuumFn, _root_.mem_integralBox, matToVec,
    apply_ite norm, mul_assoc, sub_eq_add_neg, mul_pow, ne_of_gt, ← ofReal_pow, ← Real.exp_nat_mul,
    dotProduct, @sum_comm _ _ κ, sum_prod_type, Unique.forall_iff]
  split <;> simp [univ_eq_empty]
