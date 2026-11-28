/- GID: D5/S3/Zeros/GRH/New/Rows/NaturalFormNear
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/NaturalFormNear
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.NaturalFormNear. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/NaturalFormNear.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.Carrier
import D5.S3.Zeros.GRH.New.Exchange.GridModuli
import D5.S3.Zeros.GRH.Lib.Weil.Fock.ReproducingFormula
import D5.S3.Zeros.GRH.New.Rows.SparseThetaSum
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Products of theta forms detect all good forms (see New.Rows.Separation).

Part of: The carrier: one fixed form under all twists (see New.Rows.Carrier).

This file: The carrier is non-zero, of level one, rapidly decreasing and holomorphic. Combinations
of twist-free theta forms approximate a fixed test function at points away from the cusps (first
minimum bounded below). -/

open Finset Fintype Matrix NumberField Sum WeilData

variable {E} [Field.{0} E] [CMType E] [WeilData E] {m : ℕ} [NeZero m]

/-- Let m > 0 be even, and let E have a tame character of weight 0. Then `carrierForm` is rapidly
decreasing, automorphic of every level N, and holomorphic of weight 0 and 3m on the two blocks, for
some order with the positive block first.

The carrier: one fixed form under all twists. -/
lemma carrierForm_spec (he : Even m) {𝔪 c χ} (hc : IsTameFor (E := E) 𝔪 c 0 χ) :
  (∀ N, carrierForm E m ∈ rapidOfLevel (signedSpace ..) N)
  ∧ ∃ o, IsPosFirstOrder (1 ⊕ᵥ -1) o ∧ IsAdelicHol o (fun _ ↦ 0 ⊕ᵥ 3 * m) (carrierForm E m) := by
  obtain ⟨⟨n, _, _, _⟩, _, _, H⟩ := id hc, by simpa [classSum, Rat.smul_def, mul_sum,
    ← mul_assoc, ← funext_iff] using (stdClassSum_carrierXi_eq_carrierForm E he).choose_spec hc
  use fun _ ↦ H ▸ (one_mul _).subst (mul_sum_mem_rapidOfLevel fun _ ↦ (one_mul _).substr
    ⟨⟨⟨by fun_prop [modKernel], (pairThetaKer ..).theta_rat_mul, ⟨_, isOpen_Kf⟩, ?l⟩,
    isRapid_modKernel _ _ _ _ n (⟨_, ·.nonsing_inv_mul <| χ.apply_ne_zero_iff.1 ·⟩) _ _⟩,
    (funext <| ?l _ ·.2.1)⟩), (-1 - ·) ⊕ᵥ (·), ?q, H ▸ (.sum _ fun _ ↦ isAdelicHol_pairTheta
    (by simpa +arith using (prod_letterMinor_mem_holomorphicData ?q (@.inl _ (Fin m)) 0 _).2) ·)
  simp [↓Subtype.forall', modKernel_mul_Kf_left, hc.apply_det, Pi.smul_def, mul_comm,
    χ.apply_eq_zero_iff]
  simp [IsPosFirstOrder, Function.Injective]; lia

/-- For m > 0 the carrier `carrierForm`, the theta lift of the constant 1 from U(0, m) to U(2m,
m), is not identically zero. -/
lemma carrierForm_ne_zero : carrierForm E m ≠ 0 := by
  have c a := (realInner_realPairWeil_eq_holMinorsPi (E := E) (-1) (1 ⊕ᵥ -1) (∏ τ,
    letterMinor τ (@inr (Fin a) (Fin m)) id ^ a) (by aesop (add safe [prod_mem,
    sum_mem], simp [letterMinor, det_apply', pairSign])) (ν := 0) · 0 fun _ ↦ by
    simpa [linSubst_letterMinor (κ := -1) (elim_inr _ _) Function.injective_id, smul_pow] using
      prod_smul ..)
  have : CompactSpace (@USign (Fin m) _ (-1)) := (by simp [U] : USign _ = U 1).substr inferInstance
  apply mt (integral_eq_zero_of_lift_eq_zero (isSharp_modDatum _ 1 ?_ 0 (by subsingleton) ..)
    _ ?_ ?o ?_ · 0 ?o) <;> simp [Space.IsAutomorphic.mem_rapidFunctions, prod_eq_zero_iff, c,
    Space.petersson, holMinorsPi, holMinors, Heisenberg.IsVacuum.eq_zero_of_modelInner_self.mt,
    inr_injective, MeasureTheory.measureReal_univ_ne_zero, Function.injective_id,
    Space.isAutomorphic_const, NeZero.pos]

attribute [local simp] prod_smul HasHolGap IsKDominant pairSign smul_pow smul_smul

lemma Data.negIndex_posRowIndex_spec {P} {D : Data P} (j : D.LiftIndex) :
  ((negIndex j).Injective ∧ ∀ h, (posRowIndex j h).Injective) ∧
  (∀ a, padSigns j (negIndex j a) = -1) ∧ ∀ h a, padSigns j (posRowIndex j h a) = 1 := by
  refine ⟨⟨?_, fun _ ↦ ?_⟩, ?_, ?_⟩ <;> intro <;> intros <;>
    simp_all [negIndex, posRowIndex, basisVec] <;> split_ifs at * <;> simp_all [signsW] <;> grind

open Norms.L2Operator

/-- For 1 ≤ j ≤ m and ν = `Data.nStar` there are a bounded K₀ and ε with 4ε(5b)^{7ν} + ε <
|K₀(1)| such that, whenever λ(g) ≥ (5b²⁴)^{−1/2} (`Space.firstMinimum`), some combination ∑_a
c_a(g)F♮_a(gy) of the `Data.fNatural` is within ‖y‖^{6ν}ε of K₀(y) for all archimedean y. -/
lemma Data.exists_fNatural_approx {P} {D : Data P} (j : D.LiftIndex) :
  ∃ (K₀ : _ → ℂ) (C ε : ℝ), 4 * ε * (5 * D.b) ^ (7 * nStar D) + ε < ‖K₀ 1‖ ∧ (∀ y, ‖K₀ y‖ ≤ C) ∧
  ∀ g, (√(5 * D.b * D.b ^ 23))⁻¹ ≤ ((D.spaceW j).move g).firstMinimum → ∃ c : _ → ℂ, ∀ y, ‖∑ a,
  c a * fNatural j a (g * (y, 1)) - K₀ y‖ ≤ maxOpNorm y ^ (6 * nStar D) * ε := by
  obtain ⟨hm, ⟨h4, n⟩, hr, b2, cl, _, ho, cH⟩ := (by simp [card_neg_signsW, j.2.2, *] :
    negCount (padSigns j) = D.m), (by simp [↓card_rowIndex]; grind : card D.CarrierIndex ≤ D.t ∧
    card (D.RowIndex ⊕ PadIndex j) ≤ D.t), negIndex_posRowIndex_spec j, D.nStar_bounds,
    carrierForm_spec D.m_even (isTameFor_twistedChi (c := 2) j 1)
  obtain ⟨⟨e⟩, ⟨eb, he, pb⟩, x, x0, xm, xl⟩ :=
    @Function.Embedding.nonempty_of_card_le D.CarrierIndex D.FlatIndex _ _
    (by simp; omega), (@exists_eq_left _ (AutChar.HasWeight _ · 1) _).2 (carrierChar_hasWeight j),
    exists_near_max (5 * D.b) D.x₁ ho (by simp; grind) (by simpa [Real.exp_nonneg] using
    D.le_of_hasLogBound) D.le_of_hasLogBound D.le_of_hasLogBound P.star_sqrtNegDInE
    (by simpa [P.d_prime.pos] using D.le_of_hasLogBound) (cl _) cH carrierForm_ne_zero
  let ς (_ : D.Φ) : D.CarrierIndex → ℤ := -D.reducedHalfGap ⊕ᵥ card D.FlatIndex
  have pe := realInner_realPairWeil_eq_holMinorsPi (1 ⊕ᵥ -1) (padSigns j) (linePoly j) (by
    simp (maxDischargeDepth := 9) [linePoly, letterMinor, det_apply', prod_mem, mul_mem, pow_mem,
      sum_mem, hr]) (fun _ ↦ D.m) eb fun _ ↦ by simp [linePoly, prod_pow_eq_pow_sum, -card_sum,
    linSubst_letterMinor (hr.2.2 _) inl_injective, linSubst_letterMinor hr.2.1 inr_injective]; rfl
  extract_lets v k C at pe
  let ι y : GInf D.E (padSigns j) := (G.sum ((y, 1), 1)).1
  have ⟨J, H⟩ := integral_mul_holMinorsPi_le (m := nStar D) (B := 5 * D.b) (by grw [h4])
    D.le_of_hasLogBound D.le_of_hasLogBound ho (w := ς) (k := k) (by simp [ς]) (by simp [k])
    (by simp [ς, reducedHalfGap]; lia) (by simp [k, -Nat.cast_sum]; grind [reducedHalfGap])
    fun w i ↦ by grw [← two_mul_card_detIndex_add_le j w]; clear * - hm; norm_cast; grind
  obtain ⟨v0, _, _, _, c, hc⟩ := RingOfIntegers.coe_ne_zero_iff.2 (pow_ne_zero 2 D.piGBar_ne_zero),
    NeZero.ne D.cycloConductor, D.t_odd.pos, ((signedSpace ..).move x).firstMinimum_pos,
    reproducing_formula_modKernel ho D.ideal_untwistedModulus_eq_span nonempty_modulus_places _
    (hasWeight_upsilonU1_pow D.m) .one (u :=
    ς) (by simp [ς]) (by simpa using H 1 (by fun_prop) 1 0 : _ ∧
    _).1 (by simp; omega) e (prod_letterMinor_mem_holomorphicData ho (.trans .inl e) ..) _ (fun p ↦
    realPairWeil_mem_span_pairedDetProd (Y := D.shortRows (p, 0)) _ (by simp [shortRows]) _ _) x
  have key {A b} N l (h : ∀ u, ‖A u‖ ≤ b * maxOpNorm u ^ N) (a :
    Continuous A := by fun_prop [modKernel]) := H
    _ ((cH x).continuous.fun_mul a) _ N l fun u ↦ by grw [norm_mul, xm, h, mul_comm, mul_right_comm]
  choose _ _ _ l a r using (isUnitaryRep_detTwist (ε :=
    realSigns D.E (homSigns (n := D.CarrierIndex) (1 ⊕ᵥ -1) (padSigns j)))
    (f := .id _) (γ := 0) (one_mul _).ge).exists_innerProductSpace; simp at r
  have k0 y :=
    key (A := (C · y)) 0 bot_le fun _ ↦ by simp [C, realPairWeil, ← a]; grw [norm_inner_le_norm, r]
  have e1 := IsHolOfWeight.integral_mul_conj_holMinorsPi (u := k) ho (by simp [k]) (by
    convert ((cH x).mul ho.1 (isHolOfWeight_holMinorsPi (u := ς) ho (by simp [ς]))).mul ho.1
      (.sum (T := {0}) ![C 1 1] fun _ ↦ isHolOfWeight_holMinorsPi ho (u := v) (by simp [v]))
    ext w (_ | _) <;> simp [ς, v, k, he, hm, ← card_detIndex_add_bigCharExp j] <;> omega)
  simp [mul_assoc _ (C .. * _), ← pe, mul_right_comm _ _ (C ..)] at e1
  refine ⟨_, _, _, ?_, (ι · |> k0 |>.2), fun g hl ↦ (norm_modKernel_sub_realInner_le ((D.spaceW
    j).sum ((stdSpace ..).neg.sum (stdSpace ..))) (hasWeight_upsilonU1_pow _) pb (div_ne_zero
    (NeZero.ne (D.N₁ : D.E)) v0) ?_ (.sum (g, 1)) (D.b ^ 7 * D.x) (2 * nStar D) (HasLogBound.pos D)
    (fun w ↦ ?_) (by grw [card_prod, card_prod, h4, n]; use D.nat_lt_of_hasLogBound) (linePoly j)
    rfl _ fun _ _ ↦ by simp [-sum_add_distrib, -prod_mul_distrib, linePoly, letterMinor, det_apply',
    ← Complex.coe_smul, -smul_eq_mul, ← smul_sum, ← pow_mul, ← pow_add,
    prod_pow_eq_pow_sum]; rfl).elim fun Ψ hΨ ↦ (exists_sum_smul_addChar_trace_eq (D.untwistedModulus
    2).isPrimitive_primAddChar fun x ↦ Ψ x.toRows₁ * (Pi.single (inclMatrix _ e) 1 : _ → ℂ)
    x.toRows₂).imp' (fun f a ↦ c a.2 * f a.1) fun f hf y ↦ (key _ (by omega) (hΨ · (ι y))).elim fun
    i q ↦ (congrArg _ (sub_eq_of_eq_add (.trans (.trans ?_ ((hc _ (mul_modKernel_mem_rapidOfLevel
    D.ideal_untwistedModulus_eq_span (hb := pb) (cl _) ..)).symm.trans
    (by congr with; simp [field]))) (MeasureTheory.integral_add i (k0 _).1)))).trans_le (q.trans
    (by simp_rw [mul_assoc]; grw [← mul_assoc 3, show maxOpNorm _ ≤ maxOpNorm y by simp [ι, G.sum,
    U.sum, pi_norm_le_iff_of_nonempty, one_le_maxOpNorm, norm_le_pi_norm (y · |>.1.1)]]; rfl))⟩
  grw [show ι 1 = 1 by simp [ι], e1 (k0 _).1, (?_ : _ / _ ≤ (D.b ^ 12)⁻¹)]
  simp [C, abs_of_pos J, field, ← a, linePoly]
  field_simp [prod_eq_zero_iff, hr, inl_injective, inr_injective]
  use D.lt_of_hasLogBound
    (by clear * -; grind [(D.le_of_hasLogBound : 1 + 7 * |↑(nStar D)| ≤ nStar D * D.logB)])
  grw [Nat.cast_sum, sum_le_card_nsmul _ _ (2 * D.m * (5 * D.b)) fun w _ ↦ by
    grw [← two_mul_card_detIndex_add_le j
      w]; clear * -; norm_cast; simp [← mul_sum]; lia]; simpa using D.le_of_hasLogBound
  simpa [Modulus.reduction_eq_zero_iff, ideal_untwistedModulus_eq_span,
    Ideal.mem_span_singleton, ↓dvd_def, -Subtype.forall, ← mul_assoc,
    mul_right_comm _ α.1, ← map_pow, ← map_mul, -Nat.cast_mul, ↓div_mul_cancel₀ _ v0,
    -Subtype.exists] using! fun z : Ô _ ↦ mul_right_comm _ _ z.1 ▸ mul_mem P.N₁_mul_α_mem z.2
  · grw [← firstMinimum_mul_le_hom _ P.cycloConductor_mem_different, Space.shortBasisConst,
      ← inf_le_firstMinimum_sum, ← G.sum.map_one, ← inf_le_firstMinimum_sum, ← ((stdSpace ..).move
      _).one_le_firstMinimum, ← ((stdSpace ..).neg.move _).one_le_firstMinimum, inf_idem,
      inf_of_le_left (by simp), ← hl, ← xl _ le_rfl, h4, n, show ‖_‖ = (D.N₁ : ℝ) / D.gProd by
      simpa [sq, -Nat.cast_mul] using congr(D.N₁ / ‖Φ w $D.piGBar_mul_star‖)]
    simpa [WeilData.j] using D.le_of_hasLogBound
  · simp_rw [sum_prod_type_right (α₂ := _ × _), mul_assoc (c _), ← mul_sum, fNatural, Pi.mul_apply]
    congr! 2; rw [← integral_mul_sum_const_mul fun t ↦
      mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (cl _) ..]; congr with
    simp_rw [mul_assoc, ← modKernel_sum_right, ← hf, ← modKernelBilin_apply]; simp [ι, G.sum,
      ← map_mul]; left; rfl
