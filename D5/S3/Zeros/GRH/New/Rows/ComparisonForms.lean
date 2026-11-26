/- GID: D5/S3/Zeros/GRH/New/Rows/ComparisonForms
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/ComparisonForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.ComparisonForms. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/ComparisonForms.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.RowVolume
import D5.S3.Zeros.GRH.New.Filling.FillingTheorem
import D5.S3.Zeros.GRH.New.Rows.CartanIntegrality
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Integral comparison forms seeing the twist through one number. There are forms on a definite unitary group, integral off the twist's conductor, short when untwisted and orthogonal as the congruence bound requires, whose descents to U(W_j) detect all good forms and see the twist only through one number made of Hecke L-values, and they cancel a lift's unknown volume. Integral forms pairing with a lift to an explicit L-value (pullback, seesaw) are known in low rank. Related work: Böcherer–Dummigan–Schulze-Pillot, Yoshida lifts and Selmer groups, 2012; Y.-S. Lee, Hida family of theta lift from U(1) to definite U(2), 2024; Prasanna, Integrality of a ratio of Petersson norms, 2006. -/

noncomputable section


open Finset Real ComplexConjugate Data WeilData Submodule Function.Embedding MeasureTheory LinearMap
  Fintype LevelPlaces AuxPair
variable {P} {D : Data P} (j : D.LiftIndex)
seal Subgroup.one levelSpace weylGauge

/-- The hook number (`hookNumber`) of the weight k⁻ of the auxiliary pair `Data.untwistedAuxPair`,
taken in the rank of V° at every infinite place. -/
abbrev smallHookNumber := hookNumber (untwistedAuxPair j).colsMinus (rankAt D.SmallIndex)

/-- The value space of forms on V°: complex functions on the chosen standard fillings of shape
k⁻ of the j-th auxiliary pair, later normed by their Gram matrix. -/
@[implicit_reducible] def SmallFormValues :=
  WeylIndex D.SmallIndex (untwistedAuxPair j).colsMinus → ℂ

instance : NormedAddCommGroup (SmallFormValues j) := Matrix.toNormedAddCommGroup _ weylGram_posDef

instance : InnerProductSpace ℂ (SmallFormValues j) := .ofCore (F := _ → ℂ) _

instance : Module.Finite ℂ (SmallFormValues j) := .pi

/-- The space of tables: families of coordinate vectors of weight k⁻ on V°, indexed by a choice
in `Data.MemberIndex` and a class of the principal level ϖ². -/
abbrev Data.Tables := PiLp 2 fun _ : MemberIndex j × D.SmallClasses ↦ SmallFormValues j

variable (ϑ : D.Twist)

/-- The splitting V_j = V″ ⊕ V° as a datum `DividedSplitting` for the pair (W_j, V_j) twisted by ϑ,
with 3m chosen coordinates of V″. -/
def splittingV : DividedSplitting (BigIndex j) D.SmallIndex D.CarrierIndex (D.auxPair ϑ j)
  inl := have := rank_bounds_card_bigIndex j; ⟨.trans (.sumComm ..) (.trans
    (.sumAssoc ..) (.sumCongr 1 (equivFinOfCardEq (by simp [*]; lia)))), by tauto, inl.trans inl,
    (nonempty_of_card_le (by simp; lia)).some, by
    simp [HasColumnsBelow, schurDetExp, FitsRanks, funext_iff, *]; grind [auxPair]⟩

/-- The level J_s (`rowFixingLevel`, rows s and ϖ·1) on V″ is free: the stabiliser in the rational
unitary group of every coset gJ_s is trivial. -/
lemma classAut_rowFixingLevel_eq_bot s : ∀ g, classAut (stdSpace ..).embFin.range
  (rowFixingLevel _ ((splittingV j ϑ).stackOverGenScalar s) (splittingV j ϑ).fixedEmb) g = ⊥ :=
  D.classAut_eq_bot_of_le_chosenLevel (rowFixingLevel_le_levelOf ..)
  (by grind [rank_bounds_card_bigIndex j])

/-- For a choice i, a chosen lattice satisfying `DividedSplitting.IsGlued` for the untwisted
splitting and the matrix of i, read as a lattice for ϑ; its point γ is independent of ϑ. -/
def glueLattice (i : MemberIndex j) : {L // (splittingV j ϑ).IsGlued i.1 L} :=
  have H := (splittingV j 1).exists_isGlued _; ⟨{H.choose with}, {H.choose_spec with}⟩

/-- A chosen nonzero c such that the complex conjugates of the vectors c·`Data.lineMultiplier` have
gauge ≤ 1 at primes coprime to the twist, and squared norm ≤ exp(rB₀) under each automorphism of ℂ
when Q is empty. -/
def lineScale := Classical.indefiniteDescription _ (lineMultiplier_integral_and_small j)

attribute [local simp] apply_eq_evalForm map_classSum levelOf_le_Kf classSum
attribute [-simp] star_smul sum_ite_irrel ite_smul Sum.elim_inl isUnit_map_iff

set_option backward.isDefEq.respectTransparency false in
/-- The linear map sending a table ζ to g^loss ∑_{(i,c)} of the class sum over h, level
`rowFixingLevel`, of the point forms `DividedSplitting.productForm` of conj(β₁·yQ_i(h))·ζ(i, c)
(β₁ = `lineScale`, yQ_i = `Data.lineMultiplier` ϑ j i, g = `Data.gProd`, loss =
`DividedSplitting.loss`) at
(h, c). -/
@[simps -isSimp] def comparisonForm : Tables j →ₗ[ℂ] (D.auxPair ϑ j).FormV where
  toFun ζ := (D.gProd ^ (splittingV j ϑ).loss : ℂ) • ∑ b, stdClassSum (rowFixingLevel _ ((splittingV
    j ϑ).stackOverGenScalar b.1.1) (splittingV j ϑ).fixedEmb) fun h ↦ (splittingV j ϑ).productForm
    (glueLattice j ϑ b.1) (h, b.2.out) (star ((lineScale j).1 • lineMultiplier ϑ j b.1 h)) (ζ b)
  map_add' := by simp [↓classAut_rowFixingLevel_eq_bot]
  map_smul' a := by simp [↓classAut_rowFixingLevel_eq_bot, smul_comm a, ← smul_sum]

/-- Let β₁ = `lineScale`, β_L = `DividedLattice.weilScalar`, yQ_i = `Data.lineMultiplier` ϑ j i.
If F♮_i = κ·`cosetKernelSum` of the vectors yQ_i for all choices i, then for good F: κ̄⟨F,
(θ_j^*)^† gl ζ⟩ = #Γ·g^loss·conj(β₁)·∑_i conj(β_{L_i}) ∫ conj(F F♮_i)·θo(ζ(i, ·)), with
L_i = `glueLattice`, gl = `comparisonForm`, Γ the r×r matrices mod ϖ² congruent to 1 mod ϖ. -/
lemma inner_adjoint_comparisonForm {κ} (e : ∀ i g, D.fNatural j i g =
  κ * cosetKernelSum _ (bigChar ϑ j) ((splittingV j ϑ).stackOverGenScalar i.1)
  (.trans inl inl) (lineMultiplier ϑ j i) g) F ζ : conj κ * inner ℂ F ((D.goodLift ϑ j).adjoint
  (comparisonForm j ϑ ζ)) = Nat.card (splittingV j 1).congruenceGroup * D.gProd ^
  (splittingV j 1).loss * conj (lineScale j).1 * ∑ i, conj (glueLattice j 1 i).1.weilScalar *
  ∫ g, conj (F.1.1 g * D.fNatural j i g) * tableTheta j (ζ ⟨i, ·⟩) g ∂(D.spaceW j).quotMeasure := by
  obtain _ := rank_bounds_card_bigIndex j, D.card_V, D.m_eq_two_mul_varrho_add_two
  let V := splittingV j 1
  have k b h Q := star_mul' (_ * D.fNatural j b) _ ▸ star_mem_rapidOfLevel
    (mul_modKernel_mem_rapidOfLevel (T := stdSpace _ D.SmallIndex) (a := (untwistedAuxPair j).a)
    D.ideal_untwistedModulus_eq_span (hb := hasWeight_upsilonU1_zpow (D.m / 2 - j))
    (mul_fNatural_mem_rapidOfLevel_and_hol F b).1 (Pi.single (inclMatrix _ inl) 1) Q (1, h))
  have i Y := Space.mem_levelSpace_formRep_iff.1 F.1.2 _ (mem_levelOf.2 ⟨(liftMod _).2,
    funext (V.reduceAt_liftMod_congruenceGroup Y)⟩)
  have R (x : (_ × _) × V.congruenceGroup) := (k x.1.1 x.1.2.out
    (letterPoly (D.signsW j) (untwistedAuxPair j).ord (-1) _ (star (ζ x.1)))).1.elim fun A r ↦
    (Space.integral_comp_mul_right (liftMod x.2.1) A.2 A.1).imp_right (·.2 (r.integrable A.1))
  erw [adjoint_inner_right, inner_auxLift, ← integral_const_mul]
  refine (congrArg _ (funext fun g ↦ ?_)).trans ((integral_finsetSum univ fun x _ ↦
    (R x).2.const_mul
    (D.gProd ^ V.loss * conj ((glueLattice j 1 x.1.1).1.weilScalar * lineScale j))).trans ?_)
  erw [comparisonForm_apply, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply,
    funext fun _ ↦ DividedSplitting.theta_stdClassSum_productForm _ (glueLattice j ϑ _).2 ..]
  simp [*, mul_assoc, mul_sum, ← sum_prod_type', mul_left_comm (conj (F.1.1 _)),
    mul_left_comm _ (conj κ)]
  rfl
  simp [bigChar, bigCharExp, rankTwist, mul_assoc, ← zpow_natCast, ← zpow_add, *]; congr; omega
  simp [↓R, ↓integral_const_mul, @sum_prod_type _ _ V.congruenceGroup,
    @sum_prod_type _ _ D.SmallClasses, ← mul_sum, mul_assoc, mul_left_comm _ (conj (lineScale j).1)]
  left; congr!
  simpa [tableTheta, mul_assoc] using! (integral_mul_sum_const_mul (c := 1) fun _ ↦ k ..).symm

/-- Let p be prime to the norm N(Q) of the twist ϑ and φ a p-adic place. If each conj ζ(a) is
integral (`weylGauge` ≤ 1) at its class representative for φ∘conj, then the form `comparisonForm` ζ
is integral at φ. -/
lemma comparisonForm_mem_integralForms ζ p [Fact p.Prime] (φ : PadicPlace p) (q : p.Coprime
  ϑ.levelNorm) (hζ : ∀ a, weylGauge (ι := ⟨φ.ιₚ.comp conj⟩) _ 0 a.2.out (star (ζ a)) ≤ 1) :
  comparisonForm j ϑ ζ ∈ LevelForm.integralForms φ := by
  simp_rw [comparisonForm_apply, classSum, finsum_eq_sum_of_fintype, smul_sum]
  refine sum_mem fun b _ ↦ sum_mem fun _ _ _ ↦ ?_
  simp [↓classAut_rowFixingLevel_eq_bot j ϑ b.1.1]
  grw (transparency := default) [weylGauge_smul, weylGauge_deltaForm_le isOfFinOrder_level_char,
    weylGauge_mul, (splittingV j ϑ).weylGauge_cartanProduct_le (M := D.gProd)
    (D.ideal_untwistedModulus_eq_span.ge (by simp [← piGBar_mul_star, Ideal.mul_mem_right]))
    (glueLattice ..).2, ((lineScale j).2.2
    ..).1 _ q, hζ] <;> simp [Kf_le_localLevel _, mul_inv_le_one]; simp [weylGauge]

/-- At the trivial twist, for every table ζ and automorphism σ of ℂ: 𝖧·‖gl ζ‖²_σ ≤ exp(2rB₀)·∑_a
‖σζ_a‖², with 𝖧 the hook number (`hookNumber`) of the weight of the table vectors on V° and
gl = `comparisonForm`. -/
lemma normSqAt_comparisonForm_le ζ σ : smallHookNumber j * (comparisonForm j 1 ζ).normSqAt σ ≤
  exp (2 * (D.r * D.B₀)) * ∑ a, weylNormSq (σ ∘ ζ a) := by
  rw [two_mul, exp_add, mul_assoc]; set S := exp _ * Finset.sum ..
  obtain ⟨_, M, g, this⟩ := (by simp [S, exp_pos, Finset.sum_nonneg] : 0 ≤ S),
    NeZero.pos D.chosenGroupOrder, NeZero.pos D.gProd, rank_bounds_card_bigIndex j
  have hm τ i : (untwistedAuxPair j).colsMinus τ i ≤
    D.h := by grind [add_mul, auxPair, rowParameter]
  have c {n} [Fintype n] {K} (h : principalLevel n (D.piGBar ^ 2) ≤ K) hn :=
    (D.card_stdClasses_le_exp_mul_log (D.gProd ^ 2) hn ((principalLevel_le_of_dvd
    (by simp [← piGBar_mul_star])).trans h)).trans (exp_le_exp.2 (D.le_of_hasLogBound (G := D.b)))
  simp [comparisonForm_apply, LevelForm.normSqAt, ← mul_classSum, -classSum]
  grw [← exp_log (Int.cast_pos.2 hookNumber_pos), classSum_le_card_mul_sq fun _ ↦
    (sqrt_weylNormSq_sum_le ..).trans (sum_le_card_nsmul _ _ _ fun _ _ ↦
    (sqrt_weylNormSq_classSum_le σ (B := √(D.chosenGroupOrder ^ 2 * S)) fun _ ↦
    sqrt_le_sqrt ?_).trans (by grw [c (by
    with_unfolding_all use Modulus.principalLevel_le_levelOfSubgroup
                         (D.ideal_untwistedModulus_eq_span.ge (by simp))) (by lia)]))]
  simp (disch := positivity) only [card_univ, card_eq_nat_card,
    Nat.card_prod, Matrix, Nat.card_fun, nsmul_eq_mul, Nat.cast_mul, mul_pow, sq_sqrt, ← mul_assoc]
  grw [c (principalLevel_le_levelOf (Sum.rec (Ideal.pow_mem_of_mem _ ·.2.2.1 2 two_pos) nofun)),
    c le_rfl,
    c le_rfl, Modulus.card_resRing_le (levelModulus_ideal_le norm_mul_gProd_pow_mem_modulus),
    DividedSplitting.loss, (card_detIndex j _).elim (·.ge.trans), hm, hookNumber_le (sum_le_sum
    fun _ _ ↦ sum_le_sum fun _ e ↦ mul_le_mul' (mem_range_le e) (hm ..)), ← le_exp_of_log_le]
  simp (disch := positivity) [log_mul, this, twist_one_spec, add_assoc]
  grw +useKAbstract [@log_le_self (_ + _), @log_le_self (_ * _), ← sq, Nat.sub_sub, Nat.sub_sub,
    reducedHalfGap, Nat.sub_le, Nat.sub_le]
  simpa using D.le_of_hasLogBound; any_goals first | positivity | simp [*, twist_one_spec] <;> lia
  simp [DividedSplitting.productForm]
  grw (transparency := default) [weylNormSq_deltaForm_le isOfFinOrder_level_char, map_cartanProduct
    (f := σ.toRingHom), weylNormSq_cartanProduct, ((lineScale j).2.2 ..).2 rfl, single_le_sum (f :=
    (weylNormSq <| σ ∘ ζ ·)) (by simp), Nat.le_of_dvd M (card_classAut_dvd_chosenGroupOrder ..)] <;>
    simp [this, (splittingV j 1).low, HasColumnsBelow]; lia

set_option backward.isDefEq.respectTransparency false in
/-- If Ξ is a good form on V_j, killed by the Hecke polynomial at a split place w off the level,
evaluated at `AuxPair.testValue` w, and
orthogonal to the lifts of good forms, then the functions θ°ζ_i (`Data.tableTheta`) of the table
ζ = gl* Ξ, gl = `comparisonForm`, all vanish. -/
lemma tableTheta_adjoint_eq_zero {w} {hw : _ ≠ w} {hS Ξ} (h : Ξ ∈ (groupAlgAction _ D.e₀).range ⊓
  ((D.auxPair ϑ j).heckePolyOnForms hw hS ((D.auxPair ϑ j).testValue w)).ker ⊓
  (D.goodLift ϑ j).rangeᗮ) i g : tableTheta j ((comparisonForm j ϑ).adjoint Ξ ⟨i, ·⟩) g = 0 := by
  obtain ⟨⟨⟨x, a⟩, z⟩, N, _⟩ := h, rank_bounds_card_bigIndex j, D.card_V
  have H := (splittingV j ϑ).stdClassSum_inner_productForm_eq_zero (D.fitsParams_auxPair _ j)
    ((liftTamePart_eq_of_mem_Q ..).trans_ne <| ϑ.psi_ne_one _ ·.2) (fun i _ h ↦ range_le_ker_iff.2
    ((map_mul ..).symm.trans (by erw [D.reflectionSum_mul_e₀ i (D.omega_zpow_mul_pow_eq_one j (ϑ.1.5
    _ fun h ↦ (D.levelNorm_mem_and_notMem_of_mem_Q ϑ (.inl h)).2.1 i.2.2.1)) h rfl, map_zero])) x)
    (by rw [← (exists_theta_to_principalForms ..).choose_spec j.2,
    inner_self_eq_zero.1 ((adjoint_inner_left ..).symm.trans ((D.isCentralProj_e₀.1.map
    _).mem_range_iff.1 x ▸ (innerAt_groupAlgAction _ D.isCentralProj_e₀ ..).symm.trans (z _ ⟨⟨_, _,
    rfl⟩, groupAlgAction_auxLift ..⟩)))]; rfl) a (by omega) D.ideal_untwistedModulus_eq_span
  simp [↓D.classAut_eq_bot_of_le_chosenLevel (n :=
    D.SmallIndex) (D.principalLevel_le_chosenLevel ⟨_, sq _⟩) (by simp [N]; omega)] at H
  refine .trans ?_ ((adjoint_inner_right (comparisonForm j ϑ) (.toLp 2 fun b ↦
    ite (b.1 = i) (star ∘ kernelVector (untwistedAuxPair j) (upsilonU1 ^ (D.m / 2 - j : ℤ))
    (D.untwistedModulus 2) (Pi.single (inclMatrix _ .inl) 1) _ g b.2.out) 0) Ξ).trans ?_)
  · rw [PiLp.inner_apply, sum_prod_type, Fintype.sum_eq_single i (by simp +contextual)]
    simp [tableTheta, kernelVector, inner, letterPoly, toPoly, linearCombination_apply,
      ← modKernelBilin_apply, entrywise]; rfl
  simp [comparisonForm_apply, @sum_prod_type _ _ D.SmallClasses, ← classSum_sum, -classSum]
  simpa [↓classAut_rowFixingLevel_eq_bot, inner_smul_left, sum_inner] using
    .inr (sum_eq_zero fun _ _ ↦ sum_eq_zero fun _ _ ↦ by split_ifs; exacts [H .., by simp])

/-- Comparison forms: there are γ_ϑ ≠ 0 with |γ_ϑ/γ_1|² = Γ(ϑ)/Γ(1) (`Data.heckeValueProd`), a
linear surjection A from tables onto good forms on U(W_j), and linear Ξ_ϑ with u_ϑ*Ξ_ϑ = γ_ϑA
(`Data.goodLift`), Ξ_ϑA*y tested, Ξ_ϑζ φ-integral for l prime to `ϑ.levelNorm` and ζ̄ integral at
φ∘conj, and 𝗁‖Ξ_1ζ‖²_σ ≤ exp(2rB₀)∑_a‖σζ_a‖² (𝗁 = `smallHookNumber`).

Integral comparison forms seeing the twist through one number. -/
lemma exists_comparison_forms : ∃ (γ : _ → ℂ) (A : Tables j →ₗ[ℂ] D.goodForms _) (gl : ∀ _, _
    →ₗ[ℂ] _), (∀ ϑ, γ ϑ ≠ 0 ∧ ‖γ ϑ / γ 1‖ ^ 2 = Data.heckeValueProd j ϑ / Data.heckeValueProd j 1) ∧
  (∀ ϑ : D.Twist, (D.goodLift ϑ j).adjoint ∘ₗ gl ϑ = γ ϑ • A) ∧ Function.Surjective A ∧ (∀ (ϑ :
  D.Twist) y, AuxPair.IsTested _ D.e₀ (D.goodLift ϑ j).rangeᗮ (gl ϑ (A.adjoint y))) ∧
  (∀ ϑ ζ l [Fact l.Prime] (φ : PadicPlace l), l.Coprime ϑ.levelNorm → (∀ a, weylGauge (ι :=
  ⟨φ.ιₚ.comp conj⟩) _ 0 a.2.out (star (ζ a)) ≤ 1) → gl ϑ ζ ∈ LevelForm.integralForms φ) ∧ ∀ ζ σ,
  smallHookNumber j * (gl 1 ζ).normSqAt σ ≤ exp (2 * (D.r * D.B₀)) * ∑ a, weylNormSq (σ ∘ ζ a) := by
  choose _ κ hn e using cosetKernelSum_eq_fNatural (a := D.CarrierIndex ⊕ BigIndex j) j
  replace e ϑ i g := e ϑ (.fromCols 1 0) i g ((splittingV j ϑ).stackOverGenScalar i.1)
    (by erw [Matrix.fromCols_mul_fromRows, Matrix.zero_mul]; simp)
  have hκ ϑ : κ ϑ ≠ 0 := fun h ↦
    D.finrank_rows_ne_zero ((D.finrank_rows_eq_finrank_goodForms j).trans
    (finrank_zero_iff_forall_zero.2 (eq_zero_of_integral_fNatural_tableTheta · (by simp [e ϑ, h]))))
  have U ϑ := inner_adjoint_comparisonForm j ϑ (e ϑ)
  refine ⟨(conj <| κ 1 / κ ·), (D.goodLift _ j).adjoint ∘ₗ comparisonForm j 1, _, fun ϑ ↦ ?_,
    fun ϑ ↦ ext fun ζ ↦
    ext_inner_left ℂ fun F ↦ by simpa [inner_smul_right, hκ, field, mul_comm] using (U ϑ ..).trans
                                  (U 1 ..).symm, range_eq_top.1 (orthogonal_eq_bot_iff.1
    (bot_unique fun F m ↦ eq_zero_of_integral_fNatural_tableTheta F fun i ζ ↦ ?_)),
    fun ϑ F _ _ _ Ξ m ↦ ?_, comparisonForm_mem_integralForms j, normSqAt_comparisonForm_le j⟩
  · simp; clear * - hn hκ
    grind [Complex.ofReal_eq_zero, norm_eq_zero]
  · have := (U ..).symm.trans (mul_eq_zero_of_right _
      (inner_eq_zero_symm.1 (m _ ⟨.toLp 2 fun b ↦ ite (b.1 = i) ζ 0 b.2, rfl⟩)))
    rw [Fintype.sum_eq_single i (by simp +contextual [tableTheta, ← modKernelBilin_apply])] at this
    simpa [(lineScale j).2.1, DividedLattice.weilScalar, NeZero.ne]
  · rw [← adjoint_inner_left, adjoint_inner_right, inner_eq_zero_symm]
    simpa [hκ, tableTheta_adjoint_eq_zero _ _ m] using U 1 F ((comparisonForm j ϑ).adjoint Ξ)
