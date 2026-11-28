/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/Tower/LargeSideConstantTerm
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/Tower/LargeSideConstantTerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.Tower.LargeSideConstantTerm. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/Tower/LargeSideConstantTerm.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.SiegelWeil.Tower.LineGaussSum
import D5.S3.Zeros.GRH.Lib.SiegelWeil.Tower.ConstantTerm
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Tower property for the constant term of a theta lift along an isotropic line. In the literature
the lifted form is cuspidal, while here it is a character and the data are ramified. The isotropic
orbit survives as a Tate integral, so the constant term is the smaller lift times a factor whose
size is a ratio of Hecke L-values. Source: S. Rallis, On the Howe duality conjecture, Compositio
Math. 51 (1984), Thm I.1.1; unitary case C. Wu, Irreducibility of theta lifting for unitary groups,
J. Number Theory 133 (2013), Prop. 3.1.

This file: Constant term of lifted character equals smaller lift times explicit Hecke L-value
factor. -/

open Complex Fintype MatMul MeasureTheory ProbabilityTheory Real SemilocalField Set Space WeilData
  MeasureTheory.Measure

attribute [-instance] DiscreteUniformity.instDiscreteTopology

attribute [-simp] card_punit card_unique Nat.cast_add θ_apply map_smul

variable {E} [Field E] [CMType E] {μ} (𝔠 : SplitTameChar E μ) (e : ℤ)

/-- The number (∏_{w ∈ S} Nw)^(e²) · ∏_{z=1}^{e} |L^S(z, ν)|², for a natural number e. -/
noncomputable def lValueProd S (ν : AutChar E) (e : ℕ) :=
  (∏ᶠ w ∈ S, FinPlace.q w : ℕ) ^ e ^ 2 * ∏ z ∈ .Icc 1 e, ‖ν.L S z‖ ^ 2

/-- For an integer e, the number Π(e): `lValueProd` at e for the character and places of 𝔠 if
e ≥ 0, its inverse at −e if e < 0. -/
noncomputable def lValueProdInt := lValueProd 𝔠.S 𝔠.ν e.toNat / lValueProd 𝔠.S 𝔠.ν (-e).toNat

lemma lValueProdInt_pos : 0 < lValueProdInt 𝔠
  e := by apply_rules [div_pos, mul_pos] <;> simp +contextual [sq_pos_iff,
  ↓finprod_mem_coe_finset, (𝔠.weight_pos _).ne', 𝔠.hasWeight.L_ne_zero, funext_iff, Finset.prod_pos]

variable [WeilData E] {n n' r r'} [Fintype n] [Fintype n'] [Fintype r] [Fintype r'] {s s' t t'}
  {W : Space E n s} {W' : Space E n' s'} {V : Space E r t} {V' : Space E r' t'} {b} [Fintype b] {ν :
  AutChar E} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit) [IsBaseAdapted A] [IsBaseAdapted X]

lemma rankTwist_eq_mul_of_splitting (A : W'.Splitting W b) : rankTwist ν n' = rankTwist ν n *
  upsilonU1 ^ card b := by simp [rankTwist, mul_assoc, pow_add, A.card_eq, Nat.add_mul_div_left]

/-- A datum f with real part v, the standard function `stdRowDatum` at the places of 𝔠 and the
vacuum elsewhere is fixed by the integral finite points k of U(V), when the character on
U(V) is ν⁻¹υ^⌊rk W/2⌋. -/
lemma pairWeil_stdRowDatum_eq_self {𝔠 : SplitTameChar E μ} {c v z k f} (σ : r' ⊕ r ≃ n) (hz :
  IsIntMatrix O z) (hk : k ∈ Kf E r) (e : localDatum W V v (stdRowDatum σ 𝔠.χ z) 𝔠.readsAt = f) :
  pairWeil W V (rankTwist 𝔠.ν⁻¹ n) c (1, k) f = f := by
  erw [← e, 𝔠.readsAt.pairWeil_localDatum_of_mem_Kf (stdRowDatum_mem ..) (by simp) hk, ← map_smul,
    smul_name]
  congr!; convert (isPartner_stdRowDatum_stdColDatum σ hz).left_mul (g :=
    atPlaces _ k⁻¹) _ <;> cases mem_intGL.1 hk <;> simp_all [atPlaces,
    rankTwist, ↓← 𝔠.nu_det_of_mem_Kf (s := t), ← map_inv, mem_intGL, evalPlaces_mem_O]

set_option synthInstance.maxSize 999

local instance : LocallyCompactSpace (maxCompact E t) := inferInstance

/-- Removing a plane, large side: for standard data, the constant term along A of the theta
integral for (W′, V′) is γ times that for (W, V) with a cone integral as real datum, where
|γ|²Π(e) = CΠ(e+1), e = rk V − rk W/2, C free of 𝔠.

Known result: Tower property: constant term of a theta lift along an isotropic line. -/
lemma exists_constant_term_thetaLarge {b} [Fintype b] σ' (σ : b ⊕ r ≃ n) (hn : 2 ∣ card n) μ : ∃ β,
  ∃ z ≥ 1, ∃ C, ∀ 𝔠 : SplitTameChar E μ, ∃ γ ≠ 0, ‖γ‖ ^ 2 * lValueProdInt 𝔠 (card r - card n / 2) =
  C * lValueProdInt 𝔠 (card r - card n / 2 + 1) ∧ ∀ v', IsRapidDatum v' → ∀ s, IsIntMatrix O s →
  ∀ u g, u = 1 ∨ card r = card n → ∫ q, thetaLarge W' V' 𝔠 v' (stdRowDatum σ' 𝔠.χ (s *
  (adaptedFrame 𝔠.readsAt A).I')) (lineRadical A q * A.levi (.scalar _ u, g)) ∂radicalMeasure = γ
  * thetaLarge W V 𝔠 (haar.prod haar)[coneIntegrand A X μ β z v'] (stdRowDatum σ 𝔠.χ s) g := by
  obtain ⟨a, ⟨d, hc⟩, β, z, hz⟩ := @measurePreserving_prodAssoc, id hn, (Int.rec (⟨true, ·, rfl⟩)
    (⟨false, ·, by lia⟩) : ∀ e, ∃ β, ∃ z : ℕ, e = _root_.cond β ↑z (-↑z - 1)) (card r - card n / 2)
  let τ (β : Bool) x : ℝ := d - card r + ite β (x - 1) (-x)
  obtain ⟨⟨c₁, _, H₁⟩, ⟨l, H₃⟩, e, k, k'⟩ := exists_unfold_constant_term A X,
    exists_lineTerm_localDatum A σ' σ X,
    show τ β z.succ = 0 ∧ (1 : ℝ) ≤ z.succ ∧ (1 : ℝ) < z.succ + 1 by norm_cast +zetaDelta +beta; lia
  let j β : (𝔸 E)ˣ ≃ₜ* _ := _root_.cond β (.refl _)
    ⟨.inv _ * starMulAut, continuous_star.inv, continuous_inv.star⟩
  let ε β := (j β).trans {MulEquiv.prodUnits, Homeomorph.prodUnits with}
  choose ρ _ hε using fun β ↦ (⟨_, .nnreal_smul haar (haarScalarFactor_pos_of_isHaarMeasure
    ..).ne', by fun_prop, (isMulLeftInvariant_eq_smul ..).trans (prod_smul_right _).symm⟩ :
    ∃ ρ, IsHaarMeasure ρ ∧ MeasurePreserving (ε β) haar (haar.prod ρ))
  let η β := (ρ β).real (@idelesUnitOff E _ _ ∅ ∩ univ)
  refine ⟨β, _, k, ‖c₁ * η β * (l β).1 * ideleAbs (scaleIdele E) ^ z.succ‖ ^ 2, fun 𝔠 ↦ ?_⟩
  obtain ⟨i, q, ⟨γ, hγ, H₃⟩, w, c, d₁, d₂, d₃ : ideleAbs (finIdeleIncl c)⁻¹ = _⟩ :=
    𝔠.hasWeight.isHeckeOfType, 𝔠.readsAt, H₃ 𝔠.readsAt
    𝔠.tameLocalChar, (lValueProdInt_pos 𝔠 z.succ).ne', exists_idele_star_eq_unif 𝔠
  set N := adaptedFrame q A
  let K := finIdeleIncl c⁻¹ * scaleIdele E
  let R β (s : ℝ) := l β * γ * 𝔠.ν.baseChange.1 K * (ideleAbs K ^ s :)
  let f p a := ite (idem (conjClosure 𝔠.S)ᶜ * a ∈ Ô E)
    (invOnUnits 𝔠.χ (evalPlaces _ a) / invOnUnits 𝔠.χ (evalPlaces _ (star a) * p)) 0
  -- Tate's integral at the finite places
  choose U M Y using fun β ↦ i.tate_integral (conjClosure 𝔠.S) (f 1 ·) _ (ρ β) isOpen_univ ⟨⟩ (by
    unfold f; simp +contextual [invOnUnits, ↓isIntegralUnit_iff_v_eq_one, or_imp, idem_mul_mem_Ô,
      star_involutive.surjective.forall (p := (star · ∈ _ → _))])
    (by unfold f; simp +contextual [div_mul_eq_mul_div, 𝔠.invOnUnits_mul_div_star, idem_mul_mem_Ô])
    (by unfold f; simp +contextual [mem_Ô, evalPlaces, RingHom.pi, ↓idem_mul_mem_Ô])
  constructor
  refine (fun h ↦ ⟨fun e ↦ U β (by simpa [(lValueProdInt_pos ..).ne', η, *] using h.1), h⟩)
    (.symm ⟨fun v hv s hs u g hu ↦ .trans (integral_thetaIntegral_lineRadical A _ _
    (q.isTargetBounded hv (stdRowDatum_mem ..)) _) (H₁ _ _ _ _ |> fun H ↦ And.elim
    (H (by simp [rankTwist_eq_mul_of_splitting A, constTermAt_zero, A.sourceTerm_levi,
    (by simpa [localDatum, ← Pi.zero_def] using (q.sourceTerm_localDatum A V' (G := 0)
    (stdRowDatum_mem σ' 𝔠.χ (s := s * N.I')) 0 v fun w k ↦ by_contra fun h ↦ by
    simpa [k, IntegralFrame.blocks_spec, N] using congr(N.K' *
      $((isPrimitiveMatrix_of_stdColDatum_ne_zero .one _ (.trans_eq h (ite_self
    0))).2.choose_spec.2) * N.K)) :)]) · |>.trans) ?_), ?_⟩)
  extract_lets F T Θ₀ m at H
  let L h := θ _ ∘L pairWeil W V (rankTwist 𝔠.ν⁻¹ n) (rankTwist 𝔠.ν⁻¹ n) (g,
    h) ∘L (integrated _).flip (namedVector W V (stdRowDatum σ 𝔠.χ s) q)
  have key β ξ p : T β ξ p = θ _ _ := rfl
  simp_rw [F, (by simp : ∀ (x : G E s') (y k : G E t'), (x, y * k) = (x, y) * ((1, k.1, 1) * (1,
    ↑k.2))), ← rep_apply_apply, pairWeil_stdRowDatum_eq_self _ (hs.mul N.blocks_spec.2.1) (_ :
    maxCompact ..).2.2 rfl, pairWeil_integrated_right, rankTwist_eq_mul_of_splitting A, card_unit,
    pow_one, lineTerm_pairWeil_levi A X hu, spaceChar_rankTwist hn, H₃] at key
  let J β : _ ≃ principalAdeleUnits E := (_root_.cond β 1 (.inv _ * starMulAut.1)).trans
    (.ofInjective _ (Units.map_injective (@toAdele E ..).injective))
  have P β p : _ = ∑' ξ, T β (toAdele ξ) p := Units.val_injective.tsum_eq fun _ ↦ Ne.isUnit ∘
    mt (by simp [invOnUnits, key, ·])
  let Θ σ p := Θ₀ p * (ideleAbs (p.1.1 * u)).rpow σ
  let Z β x := (L · <| coneIntegrand A X μ β x v ·).uncurry
  have o β : Z β = _ := funext₂ fun x p ↦ (map_smul ..).trans (mul_rotate ..).symm
  have hI β x h : Integrable (Z β x) (V.quotMeasure.prod _)
  · obtain ⟨m, i, -, H⟩ := stdRowDatum_mem σ 𝔠.χ, integrable_coneIntegrand A X μ β h hv
    exact (pairTheta_decay_of_onto W V _ _ _ q.1 (q.isSchwartzBruhat m) (fun _ ↦
      @m.2.2 _) 0).elim fun N ⟨Q, D, b⟩ ↦ (H
      Q).elim fun _ ⟨j, H⟩ ↦ ((j.comp_snd _).norm.const_mul _).mono' ((by simp [L]; fun_prop :
      Continuous (L · ·).uncurry).comp_aestronglyMeasurable₂ (by fun_prop) i.1.comp_snd)
      (.of_forall fun p ↦ (mul_one _).ge.trans ((b _ _ _ ((H _).trans_lt enorm_lt_top).ne).trans
      (by grw +useKAbstract [mul_right_comm, le_abs_self (D * _), H, toReal_enorm]; simp)))
  have B β s h : Integrable (Θ (τ β s)) m ∧ m[Θ (τ β s)] =
      R β s * (𝔠.ν.L 𝔠.S s * η β) * (V.quotMeasure.prod (haar.prod haar))[Z β s]
  · refine (?_ : _ = Θ _) ▸ ((((a ..).prod (.id _)).comp ((a ..).symm.comp (.comp (.prod (.id _)
         ((hε β).comp (measurePreserving_orbitMeasure.mul_right _ (u / (j β).symm K)))) ((a ..).comp
      ((measurePreserving_swap.comp (a ..)).prod (.id _)))))).fubini ((hI β s h.le).mul_prod ((M β s
      h).const_mul _))).imp (·.integral_prod_left)
      (by erw [·, ← Y β s h, mul_comm, ← integral_const_mul, ← integral_prod_mul])
    simp_rw [Θ, Θ₀, fun p ↦ (P _ p).trans (.trans ((tsum_lineTerm A X β).1 _) (P β p).symm), ←
      tsum_mul_left, ← tsum_mul_right, integral_count_eq_tsum, ← (J β).tsum_eq]
    congr! with ⟨⟨a⟩⟩ ξ; simp [MeasurableEquiv.prodAssoc, -map_mul]
    have e : toAdele ξ.1 = j β (J β ξ) := β.rec (eq_star_of_eq_star (star_toAdele _).symm) rfl
    generalize h : ε _ _ = y; rw [(by rw [← h, (Units.ext (Prod.fst_mul_snd _) : (ε β _).1.map
      (.inl ..) * finIdeleIncl (ε β _).2 = j β _)]; simp [Subgroup.smul_def, mul_assoc, K] : a =
      (j β).symm ((j β (J β ξ))⁻¹ * (y.1.map (.inl ..) * finIdeleIncl y.2 * finIdeleIncl c⁻¹ *
      scaleIdele E)) * u⁻¹), (β.rec rfl rfl : ⇑(j β).symm = _root_.cond β id star⁻¹)]
    have a a : ite .. = _ := show f ϖ.1 a = f 1 (a * c) by unfold f; simp +contextual [d₁, d₂,
      idem_mul_mem_Ô, (funext (d₁ _ <| 𝔠.star_notMem _ ·.2) : evalPlaces _ _ = 1)]
    cases β <;> simp [↓a, (congrArg _ (Units.ext e)).symm.trans (ideleAbs_toAdele ξ), e, key, o, hc,
      L, τ, R, K, pow_mul, fun x ↦ (congr(𝔠.ν.1 ⟨$(by simp [mul_comm]), _⟩) :
      𝔠.ν.baseChange.1 (star x) = 𝔠.ν.baseChange.1 x⁻¹), pow_add, 𝔠.hasWeight.baseChange_apply_inf,
      HeckeChar.finPart, finIdeleAbs, mul_pow, rpow_add, rpow_sub, inv_rpow, rpow_neg,
      mul_rpow, ← ofReal_pow, 𝔠.ν.baseChange.2 _ ⟨_, e⟩] <;> field (disch := simp [rpow_def_of_pos])
  have I := mellin_analytic_on_strip (by simp) (by fun_prop) (B false _ k').1.2 (B true _ k').1
  obtain ⟨a, a'⟩ := I.1 0 (by clear * - e; grind), EqOn.of_subset_closure (B β · ·.1 |>.2)
    (I.2.1.comp (by unfold τ; split <;> fun_prop) fun _ ↦ by clear * -; grind) (.mul (.mul (by
    fun_prop (disch := simp)) (((i.exists_hasPrimeDensity (by simp [Finite.star]) (i.ne_one (by simp
               [↓funext_iff, (𝔠.weight_pos _).ne']))).1.mono fun _ ↦ (·.1)).mul_const _)) (o β ▸
    (mellin_analytic_on_strip (by simp)
    (continuous_ideleAbs.comp (.units_map _ (.prodMk_left _))).snd'.snd'.measurable (o β ▸ hI β 1
    le_rfl).2 (o β ▸ hI β _ k'.le)).2.1)) Ioc_subset_Icc_self (by simp) ⟨k, by simp⟩
  simp [e, Θ] at a a'
  use a; erw [a', ← mul_assoc, integral_prod _ (hI β _ k)]
  rcongr; exact (L _).integral_comp_comm (integrable_coneIntegrand _ _ _ β k hv).1
  cases β <;> simp [hz, mul_pow, lValueProdInt, lValueProd, add_comm (1 : ℤ), R, K, d₃,
    Finset.prod_Icc_succ_top, ↓neg_add', ↓finprod_mem_coe_finset, card_ResField, ← 𝔠.S.prod_attach,
    hγ, TameLocalChar.ResidueRing, Nat.card_pi] at w ⊢ <;> field (disch := simp [w])
