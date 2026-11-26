import OmegaMath.NumberTheory.GRH.Lib.ClassField.Places.UnramifiedCharacters
import OmegaMath.NumberTheory.GRH.Lib.CM.LocalHeight.IsogenyIntegrality
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Kronecker's first limit formula. It is stated here with the discriminant, as a
real limit from the right for any lattice. Rows are compared with integrals by the mean value
theorem where the known proof shifts contours. Source: C. L. Siegel, Advanced Analytic Number Theory
(1961), I Thm 1; for a proof of this shape, F. Chamizo, A simple evaluation of a theta value, the
Kronecker limit formula and a formula of Ramanujan, Ramanujan J. (2022), Prop. 3.1.

Part of: Local heights and Tate's trick; integrality of CM theta functions and torsion translates
(known result; see Lib.CM.LocalHeight.IntegralParameter).

This file: Kronecker's first limit formula for any lattice, as a one-sided real limit. Teichmüller
roots of unity with their norms are p-adic limits from quadratic integers. Logarithm of theta:
second derivative, integrality of constant and of limit dilation quotients. -/

open Complex Set ComplexConjugate Equiv Function IsLocalRing QuadField ModularForm NumberField
  PadicInt PowerSeries Real intervalIntegral Periodic WithPiTopology

/-- Kronecker's first limit formula: for a lattice of area A and discriminant Δ = g₂³ − 27g₃²,
and k > 0, the function F(s) = (s−1)∑_{l≠0}(|l|²/kA)^{−s} on 1 < s < 2, with F(1) = πk, has
right derivative πk(2γ − log(A/kπ²) − ⅙log|Δ|) at 1.

Known result: Kronecker's first limit formula. -/
lemma kronecker_limit L k (hk : 0 < k) :
    ∃ F, F 1 = π * k ∧ HasDerivWithinAt F (F 1 * (2 * eulerMascheroniConstant -
    (PeriodPair.area L / k / π ^ 2).log - ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖.log / 6)) (Ioi 1) 1 ∧ ∀ s ∈ Ioo
    1 2, HasSum (fun l : L.lattice ↦ (s - 1) * (‖l.1‖ ^ 2 / k / L.area) ^ (-s)) (F s) := by
  obtain ⟨⟨a, ⟨z, y⟩, e, H, ⟨⟩⟩, hT, hZ⟩ := exists_lattice_eq_mul_tau L,
    ZLattice.summable_norm_rpow L.lattice, fun
    s ↦ hasSum_re ∘ hasSum_pnat_iff.2 ∘ (sub_add_cancel ..).substr ∘ @LSeriesHasSum_one (ofReal s)
  simp +contextual [riemannZeta_eq_inv_sub_add, ne_of_gt, ← rpow_neg, comp_def, *, cpow_ofReal,
    normSq, ← e.summable_iff, summable_mul_left_iff, mul_rpow, rpow_eq_zero_iff_of_nonneg] at hZ hT
  let w (p : ℕ+ × ℤ) u := ‖p.1 * z + (ofReal u + p.2)‖
  have hle p u : 0 < w p u := (im_le_norm _).trans_lt' (by simpa)
  have S : Summable fun p ↦ (w p 0 / 2) ^ (-3 : ℝ) := by simpa [w, ↓div_rpow] using ((hT (-3) (by
    grind)).comp_injective ((Nat.cast_injective.comp @PNat.eq).prodMap injective_id)).mul_right _
  let F p s u := (w p u).rpow (-2 * s); let D p s := ∫ u in 0..1, F p s 0 - F p s u
  have hC {p} : Continuous (F p).uncurry := .rpow (by fun_prop) (by fun_prop) (by grind)
  have hU := tendstoUniformlyOn_tsum_of_cofinite_eventually (f := D) (s := Icc 1 2) ((S.mul_left
    4).mul_right _) ((S.tendsto_cofinite_zero.eventually_lt_const one_pos).mono fun p _ s _ ↦
    norm_integral_le_of_norm_le_const fun u _ ↦ (fun b ↦ le_trans (by
      apply (convex_Ici (w p 0 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le fun _ _ ↦
        (hasDerivAt_rpow_const ?_).hasDerivWithinAt
      intros; grw [norm_eq_abs, abs_mul, abs_rpow_of_nonneg, rpow_le_rpow_of_nonpos,
        rpow_le_rpow_of_exponent_le]; gcongr; repeat grind [rpow_lt_one_iff])
    (mul_le_of_le_one_right (by bound) b)) ((abs_norm_sub_norm_le ..).trans (by simp; grind)))
  have hD s (h := by grind) : Summable (D · s) := ⟨_, hU.tendsto_at h⟩
  let G s := √π * .Gamma (s - 1 / 2) / .Gamma s * z.im ^ (1 - 2 * s); let T s := 2 * (tsum (D · s)
    + (2 * s - 1)⁻¹ + (riemannZeta₀ (2 * s)).re + G s * (riemannZeta₀ (2 * s - 1)).re)
  have hG : HasDerivAt G .. := .mul (.div (.const_mul _ (.comp_sub_const _ _ ((sub_half _).substr
    hasDerivAt_Gamma_one_half))) hasDerivAt_Gamma_one (by simp)) (((hasDerivAt_const_mul
    _).const_sub _).const_rpow y)
  have R s m (h := by grind) (a := (hD s h).prod_factor m) (b := one_half_lt_one.trans_le h.1) := by
    have h := by simpa (disch := positivity) [mul_rpow, -one_div] using (lintegral_norm_add_rpow
      (m * z) (by simpa) b ▸ MeasureTheory.integral_toReal (by fun_prop) (by simp) :)
    exact (a.hasSum.add (h ▸ (MeasureTheory.Integrable.of_integral_ne_zero (h.trans_ne (by
      positivity))).hasSum_intervalIntegral_comp_add_int)).congr_fun (by
      simp_intro +zetaDelta _ [↓integral_sub _ ((hC.uncurry_left _).intervalIntegrable ..)]; rfl)
  obtain E := @tsum_int_eq_zero_add_two_mul_tsum_pnat, pi_pos, Real.Gamma_one_half_eq,
    rpow_neg_one, hG.continuousAt, by simpa using hU.continuousOn (.of_forall (by fun_prop)) 1
  have hp {k} : ‖eta_q k z‖ < 1 := by simp [pow_lt_one₀, norm_qParam_lt_one, *]
  have hs : Summable (uncurry fun m k ↦ eta_q m _ ^ Nat.succ k / ofReal m.succ) :=
    .of_norm_bounded ((pnatEquivNat.prodCongr pnatEquivNat).symm.summable_iff.2
    (summable_prod_mul_pow 0 (@hp 0)).norm) (by simp [pow_mul, -Nat.cast_add, field, qParam])
  rcases differentiable_riemannZeta₀.continuous, (hasProd_of_hasSum_log (one_sub_eta_q_ne_zero · y)
    (hs.tsum_comm ▸ hs.prod_symm.prod.hasSum.neg.congr_fun (by simp [(hasSum_taylorSeries_neg_log'
    hp).tsum_eq, pow_right_comm]))).tprod_eq, (hD 1).tsum_prod ▸ (pnatEquivNat.symm.hasSum_iff.1
    (((hasSum_re hs.prod.hasSum).mul_left (2 * π / z.im)).congr_fun fun m ↦ by
    have hz := UpperHalfPlane.coe_mem_integerComplement ⟨m.succ * z, by simpa [-Nat.cast_add]⟩
    have := cot_series_rep' hz ▸ im_tsum (summable_cotTerm hz) ▸
      ((((hasSum_nat_add_iff' 1).2 (R 1 m.succPNat).nat_add_neg).mul_left (-m.succ * z.im)
      ).congr_fun (by simp [Complex.sq_norm, normSq]; grind)).tsum_eq
    simp [↓pi_mul_cot_pi_q_exp, ← mul_assoc, ← eta_q_eq_cexp, normSq_eq_norm_sq,
      tsum_div_const, geom_series_succ, ↓hp, -ofReal_add] at *; grind)).tsum_eq
  refine ⟨_, ?_, ((((hasDerivWithinAt_iff_tendsto_slope' ?_).2 (tendsto_nhdsWithin_congr
    (fun _ h ↦ (slope_sub_smul T h.ne).symm) (continuousWithinAt_Ioi_iff_Ici.2 (by
    fun_prop (disch := grind))))).add hG.hasDerivWithinAt).fun_mul ((hasDerivWithinAt_id
    ..).const_rpow (mul_pos hk y))).congr_deriv ?_, fun s _ ↦ e.hasSum_iff.1 ?_⟩
  repeat norm_num [T, G, *, riemannZeta₀, riemannZeta_two, Real.log_mul,
    discriminant, ModularForm.eta, ↓g₂_g₃_eq_eisenstein H, qParam, sq, log_div, ne_of_gt] <;> grind
  specialize hT (-2 * s) (by grind)
  convert! (hT.hasSum.mul_left (s - 1)).mul_right _ using 2
  simp [*, mul_pow, div_rpow, mul_rpow, rpow_neg, rpow_mul, le_of_lt, field]
  rw [hT.tsum_prod, E (fun _ ↦ (tsum_comp_neg _).symm.trans (by simp [norm_neg_add])) hT.prod,
    (((hD s).prod.hasSum.add ((hZ (_ - 1) _).mul_left (G s))).congr_fun (by
    simp [(R s _).tsum_eq, field])).tsum_eq, E (by simp_intro _) (hT.prod_factor _)]
  simp [(hZ (2 * s) (by grind)).tsum_eq]; repeat grind [(hD s).tsum_prod, zero_rpow]

variable {p : ℕ} [hp :
  Fact p.Prime] [PadicPlace p] (d) [PrimeSevenModEight d] {p' : ℕ} [Fact p'.Prime]

instance : CharP (ResidueField (valRingCp p)) p :=
  .of_eq_zero hp.1 (residue_eq_iff_valuation_sub_lt_one.2 (by simpa using! norm_p_lt_one))

omit [PrimeSevenModEight d] in
lemma map_sqrt_neg_sq : ιₚ (I * √d) ^ 2 = -d := by simpa using congr(ιₚ $(sqrtNegD_sq d))

/-- The closure in ℂ_p × ℂ_p of the set of pairs (ι(a), ι(a ā)), for a in ℤ[(1 + √−d)/2]. -/
def normPairClosure := closure {(ιₚ a, ιₚ (a * conj a)) | a ∈ quadInt d}

lemma sqrt_neg_mem_quadInt : I * √d ∈ quadInt d := ⟨sqrtNegDInt d, by simp [two_mul]⟩

omit [PadicPlace p] in
lemma QuadField.exists_map_eq_and_map_star_eq_pow {k} [Field k] [CharP k p]
  (φ : 𝓞 (QuadField d) →+* k) z (h : z ^ primeNorm d p = z) :
  ∃ a, φ a = z ∧ φ (star a) = z ^ p := have E x := mem_bot_iff_intCast p k (x := x).1
  by rcases (eq_map_c₀_pow_iff · φ 1 (φ (star (c₀ d)))),
       (legendreSym_eq_pow_of_sq_eq_neg · (map_sqrtNegDInt_sq φ))
     refine (E ((z - z ^ p) / φ (sqrtNegDInt d)) ?_).elim fun n _ ↦ (E (z - n * φ (c₀ d)) ?_).imp'
       (↑· + n * c₀ d) ?_ <;> simp_all [Subfield.mem_bot_iff_pow_eq_self _ p, map_ofNat, sq,
       pow_mul, ← frobenius_def] <;> split at h <;> simp_all <;>
       grind [hp.1.one_lt, zero_pow, chiK_two]

lemma mem_normPairClosure_of_pow_eq {ζ} (N : ‖ζ‖ = 1) (h : ζ ^ primeNorm d p = ζ) :
  (ζ, ζ ^ (p + 1)) ∈ normPairClosure d := by
  have ⟨a, e, f⟩ := exists_map_eq_and_map_star_eq_pow d ((residue _).comp (.codRestrict (.comp _ _)
    (valRingCp p) (norm_ringOfIntegers_le (ιₚ.domRestrict _)))) ⟦⟨ζ, N.le⟩⟧ congr(⟦⟨$h, _⟩⟧)
  set q := primeNorm d p
  have T {x y} (e : residue (valRingCp p) x = ⟦y⟧) (N : ‖y.1‖ = 1) :=
    (((@continuousAddCharEquiv_of_norm_mul p _ ℂ_[p] _ (.compHom _ Coe.ringHom)
    ⟨(dist_smul_pair ·.1), (dist_pair_smul ·.1 ·.1)⟩).2 ⟨(x - y) / y, by
    simpa [N] using! residue_eq_iff_valuation_sub_lt_one.1 e⟩).2.seqContinuous
    (@tendsto_pow_atTop_nhds_zero_of_norm_lt_one _ _
    ↑q (by simp [q, apply_ite, ↓norm_natCast_lt_one_iff]))).mul_const y.1
  use mem_closure_iff_seq_limit.2 ⟨_, (⟨_, ⟨a ^ q ^ ·, rfl⟩,
    rfl⟩), by simpa [pow_right_comm _ p, *,
    (by simpa using @iterate_fixed _ (· ^ q) _ h), AddChar.map_nsmul_eq_pow, smul_pow, add_div',
    ← nsmul_one, -nsmul_eq_mul, norm_pos_iff.1, RingHom.codRestrict, div_pow,
    pow_succ'] using ((T e N).prodMk_nhds ((T e N).mul (T f (by simp [N]))))⟩

attribute [-simp] RingHom.mem_range map_smul

@[simp] lemma mv_constantCoeff_eq (g : ℂ_[p']⟦X⟧) : MvPowerSeries.constantCoeff g =
  constantCoeff g := rfl

attribute [local simp ←] CMLattice.derivative_taylorVia subst_pow expSubst_add mul_assoc

attribute [local simp] derivative_exp derivative_subst rescale_subst

/-- In ℂ_p, θ = exp(−L) with L = O(z²), L″ = L₂ + ξ and √−d·L₂ integral. For each limit (a, N)
of pairs (ιδ, ι(δδ̄)), δ ∈ 𝓞_K, the series φ(az), exp(NL − L(az)) and (NL − L(az))′ lie in
𝔬[[φ]]. -/
lemma CMLattice.exists_log_theta {p : ℕ} {d} [Fact p.Prime] [PrimeSevenModEight d] (C :
  CMLattice d) [PadicPlace p] : ∃ L L₂, L.constantCoeff = 0 ∧ coeff 1 L = 0 ∧ taylorVia ιₚ C.θ =
  expSubst (-L) ∧ d⁄dX (d⁄dX L) = .C L₂
  + taylorVia ιₚ C.translatedWp ∧ ‖ιₚ (.I * √d) * L₂‖ ≤ 1 ∧ ∀ x ∈ normPairClosure d, rescale x.1
  (taylorVia ιₚ C.translatedWpDeriv) ∈ C.phiSeriesRing ∧ expSubst (x.2 • L) * rescale x.1
  (taylorVia ιₚ C.θ) ∈ C.phiSeriesRing ∧ d⁄dX (x.2 • L - rescale x.1 L) ∈ C.phiSeriesRing := by
  let θ := taylorVia ιₚ C.θ
  obtain ⟨h, t, ⟨Z⟩, i, L, hL0, e⟩ := fun z h ↦ congr(deriv (deriv $(funext
    (@C.theta_add_mul_theta_sub _ z h)) ·) 0), by simpa [self_eq_neg] using deriv_comp_neg C.θ 0,
    C.isSeriesGenerator_translatedWpDeriv.exists_subst_inverse, θ.inv_mul_cancel
    (by aesop), ((⟨.mk fun n ↦ coeff n.pred · / n, by simp, PowerSeries.ext (by simp [field,
    coeff_derivative])⟩) : ∀ f : ℂ_[p]⟦X⟧, ∃ L, L.constantCoeff = 0 ∧ d⁄dX L = f)
    (-d⁄dX θ * θ⁻¹)
  simp (disch := fun_prop) [deriv_comp_const_add, deriv_comp_const_sub] at h
  ring_nf at h
  refine have hθ := by apply inv_unique i (derivative.ext ..) <;>
      simp [*, θ, -MvPowerSeries.inv_pow]; ring
    have hDD := by simp_all [sub_eq_sub_iff_add_eq_add, ← add_mul,
      -MvPowerSeries.inv_pow]; grind [by
      simpa (disch := fun_prop) using congr(map ιₚ $(C.taylorAtZero_congr h))]
    have H := forall₂_imp (fun _ _ ↦ .imp_right fun h ↦ ⟨h,
      (C.isSeriesGenerator_translatedWpDeriv.exists_mul_eq_one h (by simp [*])).elim fun _ k ↦ by
      convert mul_mem (C.deriv_mem_phiSeriesRing h) k.1; simp_all; grind⟩) (closure_minimal ?_ ?_)
    ⟨L, -ιₚ (deriv (deriv C.θ) 0), hL0, by simpa [t, hL0] using congr(coeff 1 $hθ), hθ, hDD, ?_, H⟩
  rintro _ ⟨a, k, ⟨⟩⟩
  cases exists_isIsogeny_of_mul_mem_lattice (C.5 k)
  apply (C.rescale_translatedWpDeriv_mem ‹_›).imp_right (·.elim _)
  simp_all [ne_of_gt, exp_pow_eq_rescale_exp, subst_zero_eq_C_constantCoeff]
  simp [← subst_rescale_eq_subst_smul, *, mem_range_seriesToCp, ← Pi.le_def, rescale,
    ← Prod.mk_le_mk]
  apply isClosed_le <;> fun_prop (disch := simp [*]) [PowerSeries.mk, coeff]
  have {a} k := C.deriv_mem_phiSeriesRing (H _ (subset_closure ⟨a, k, rfl⟩)).2.2
  convert (C.isSeriesGenerator_translatedWpDeriv.norm_coeff_le_one (sub_mem (this (conj_mem_quadInt
    quadGen_mem_quadInt)) (this quadGen_mem_quadInt))).1
  simp [quadGen, map_ofNat, hDD, translatedWp, rescale_eq_subst]; ring
