/- GID: D5/S3/Zeros/GRH/New/Rows/HeckeValueHeight
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/HeckeValueHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.HeckeValueHeight. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/HeckeValueHeight.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.MemberOrthogonality
import D5.S3.Zeros.GRH.New.Rows.Separation
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Each ratio of Hecke values repays one direction. At the chosen twists, with valuations bounded
by test forms and class group characters, the inverse of a ratio of twisted to untwisted Hecke
L-values has height at most a small error minus the cost of one direction of a lift, so the product
of about k such ratios has height at most a small error minus k·`Data.dirCost`. Norms of lifts of
Hecke characters as
L-values, their divisibility via congruences and divisibility at inert primes are known. Related
work: Prasanna, Integrality of a ratio of Petersson norms, 2006; Coates–Liang–Sujatha,
Tate–Shafarevich group for elliptic curves with CM II, 2010 (after Katz, 1977); Y.-S. Lee, Hida
family of theta lift from U(1) to definite U(2), 2024.

This file: Inverse ratio of twisted Hecke values has height repaying one direction; product
version. -/

open AutChar DoubleCoset Finset Fintype IsUltrametricDist LValueData Matrix LevelPlaces
  QuotientGroup Real Submodule Data.Pair

variable {P} {D : Data P} {l : ℕ} [Fact l.Prime] {E κ n : Type} [Fintype n] {X :
  LValueData D.E n} {m}
  {q : D.Pair} {ϑ} {F : Gf D.E (Fin m) → X.auxPair.FormV} (H : q.IsFlat (Fin m)) {p q₂ q₃ : D.Pair}

open IsMulCommutative in
/-- Let K ⊂ U(1)(𝔸_f) contain the principal level at places w_i ∈ S, with trivial stabilisers, and n
the class number. Then for some z and some weight-zero χ tame on S, the class sum of
(χs)(gz), divided by n, is ι-adically at least as large as s(1). -/
lemma exists_twisted_classSum_ge [Field E] [CMType E] (w : κ → _) S (hS : ∀ i,
  w i ∈ S) (ι : ℂ →+* ℂ_[l]) (s : Gf E Unit → ℂ) {Γ K} (hΓ : stdRatPoints ≤ Γ) (hK : levelOf w ⊥ ≤
  K) [HasFiniteType Γ K] (a : ∀ g, classAut Γ K g = ⊥) : ∃ z, ∃ χ : tameChars S, ‖ι (s 1)‖ ≤ ‖ι
  (classSum Γ K (fun g ↦ χ.1.1.1 (detFin 1 (g * z)) * s (g * z)) / classSum Γ K 1)‖ := by
  have c u i j : (scalarFin (E := E) Unit u).1.1 i j = u := ite_eq_left rfl
  have := @ofFinite _ ‹HasFiniteType ..›.1; unfold classSum DoubleCoset.Quotient at *
  rw [show setoid Γ K = leftRel (Γ ⊔ K) by ext a; simp only [rel_iff, eq_comm, leftRel_apply,
    Γ.mem_sup, mul_left_comm a, eq_inv_mul_iff_mul_eq, mul_assoc]] at *
  choose χ k using fun ψ : AddChar (Additive _) ℂ ↦ (AutChar.exists_mem_tameChars
    (ψ.toMonoidHom.comp (map _ (Γ ⊔ K) ((scalarFin _).comp (Unitary.map ⟨.snd .., by simp⟩).1)
    (sup_le (fun _ ⟨_, h⟩ ↦ le_sup_of_le_left hΓ (mem_stdRatPoints_iff.2 fun _ _ ↦ ⟨_,
    (c ..).substr congr($h.2)⟩)) fun _ h ↦ le_sup_of_le_right hK (mem_levelOf.2 ⟨mem_Kf.2 fun _ _ ↦
    (c ..).substr h.1, by ext; simp; exact congr(reduceAt _ ⟨$(c ..), _⟩).trans (h.2 _
    (hS _))⟩))))).imp fun _ h g ↦ (h (detFin 1 g)).trans (congrArg (ψ <|
    .ofMul ⟦·⟧) (by ext; simp [G.det, U.det, Gf.atPlace, c]; rfl : _ = g))
  refine ⟨(1 : _ ⧸ Γ ⊔ K).out⁻¹, (exists_norm_finsetSum_le ⊤ _).imp' χ fun _ ↦ (·.2.trans_eq' ?_)⟩
  simp [a, ← map_sum, ← sum_div, sum_comm, ← sum_mul, AddChar.sum_apply_eq_ite, k]
  erw [mul_div_cancel_left₀]; simp

namespace Data

/-- Multiplicative pigeonhole: let G be a finite group, ι: ℂ → F a ring homomorphism to a normed
field, and V^|G| = ∏_χ a(χ)b(χ). Then every ψ in G is a product φχ with ‖ι V‖ ≤
‖ι(a(φ)b(χ))‖. -/
lemma exists_factorisation_le {G F} [Group G] [Fintype G] [NormedField F] (ι : ℂ →+* F) {a b :
  G → ℂ} {V} (e : V ^ card G = ∏ χ, a χ * b χ) ψ : ∃ φ χ, φ * χ = ψ ∧ ‖ι V‖ ≤ ‖ι (a φ * b χ)‖ :=
  (exists_max_image _ _ univ_nonempty).elim fun χ h ↦ ⟨_, χ, div_mul_cancel ..,
  le_of_pow_le_pow_left₀ card_ne_zero (by bound) (((prod_le_prod₀ (by bound) h.2).trans_eq
  (prod_const _)).trans' (by simp [← norm_pow, ← map_pow, e, ← (Equiv.divLeft ψ).prod_comp a]))⟩

/-- For a pair q with c = ⌊m/2⌋: `Data.chosenGroupOrder` times the class sum over h of den·(∏_{w∈Q}
Nw)^{1−m}·⟨1, den·Ξ(h)⟩·F(h), with Ξ = `Data.Pair.trivialLift` and den = `Data.Pair.denomBound`. -/
noncomputable def Pair.xiSum ϑ (F : _ → X.auxPair.FormV) :=
  D.chosenGroupOrder • stdClassSum (lValueData H.2 ϑ).auxPair.levelGroup fun h ↦ (q.denomBound /
  ϑ.levelNorm ^ (m - 1) * gramForm 1 ((q.denomBound : ℂ) • trivialLift H.2 ϑ h)) • F h

lemma Pair.xiSum_mem [PadicPlace l] (hl : l.Coprime ϑ.levelNorm) {N : Submodule embValRing _} (h :
  ∀ h, F h ∈ N) : xiSum H ϑ F ∈ N := smul_classSum_mem N (D.card_classAut_dvd_chosenGroupOrder
  (H.2.1 ▸ D.nat_le_of_hasLogBound) levelOf_le_Kf) (N.smul_mem ⟨_, mul_mem
  (by simp [← NNReal.coe_le_coe, norm_natCast_le_one, hl.norm_natCast_eq_one, -Nat.cast_prod])
  (by simpa [trivialLift_apply, smul_sum] using sum_mem fun _ _ ↦ gramForm_mem_embValRing _ (by
  simp [weylGauge, weylRep, schur_eq_one, H]) (weylGauge_pointKernel_le_one (hl := hl) ..))⟩ <| h ·)

lemma Pair.smul_apply_xiSum g {A B} {L : _ →L⋆[ℂ] ℂ} (e : ∀ h i, L (F h) =
  B * (A * (lValueData H.2 ϑ).kernelForm g h i)) : ((stdClassSum (lValueData H.2 ϑ).chosenLevel 1 *
  P.vacuumScale D.s ^ m) • L) (xiSum H ϑ F) = B * intAlgPart H.2 ϑ * A := by
  have t := congr(star $(inner_trivialLift _ g (lValueData H.2 ϑ).trivialLift))
  simp [theta_eq_inner_kernelForm, mul_comm' _ g, ← twistedCentralOp_kernelForm,
    ← inner_twistedCentralOp, twistedCentralOp_trivialLift] at t
  simp [inner, LevelForm.innerAt_eq_stdClassSum, xiSum, intAlgPart, trivialLift, norm_smul, mul_pow,
    t, ← Complex.mul_conj', apply_eq_evalForm,
    map_classSum, ↓classSum_mul, mul_classSum, division_def, H.1, gramForm_apply, mul_sum, sum_mul,
    dot_mulVec_eq_sum_sum, -norm_pow]; congr! 6; rw [e]; ring!

seal Finset.univ Finset.sum Finset.prod in
open _root_.Nat in
/-- Let p have rank one, blocks of ranks 12, 4, 4 and 2z − 20, ϑ a twist prime to l, degrees and
characters matching. Some integral test form at l pairs with the theta kernel to explicit constants
times three norms `Data.Pair.intAlgPart` times the rank-12 kernel of monomial α. -/
lemma exists_test_form_inner_kernelForm (H : q.IsFlat (Fin (2 * p.z - 20))) (H₂ : q₂.IsFlat (Fin 4))
  (H₃ : q₃.IsFlat (Fin 4)) {j α b} [PadicPlace l] (hE : p.IsRankOne j) (ϑ : D.Twist) (hl :
  l.Coprime ϑ.levelNorm) x₀ : let X := lValueData hE.1 ϑ; let u := @.one P D; (∀ τ, ∑ i, α (τ, i,
      ()) = X.jetDeg τ) → b * ((lValueData H₂.2 ϑ).auxPair.b * (lValueData H₃.2 u).auxPair.b) *
      (lValueData H.2 u).auxPair.b = X.auxPair.b → ∃ Ξ, (∀ g, inner ℂ Ξ (X.kernelForm g) *
      (stdClassSum X.chosenLevel 1 ^ 3 * P.vacuumScale D.s ^ (2 * p.z - 20 + 8)) = (∏ τ, (X.jetDeg
      τ)! :) / α.prod (fun _ k ↦ ↑k !) * q.intAlgPart H.2 u * q₃.intAlgPart H₃.2 u * q₂.intAlgPart
      H₂.2 ϑ * modKernel (stdSpace ..) (stdSpace _ (Fin 12)) 1 b (X.levelModulus 1 false)
      (Pi.single x₀ 1) (.monomial α 1) (1, g) (1, 1)) ∧ X.auxPair.IsTestForm l Ξ := by
  intro X u hα hb; have hG i : ¬D.IsChosen (X.twistPlace i) :=
    (D.levelNorm_mem_and_notMem_of_mem_Q ϑ (.inl i.2)).2.1
  obtain ⟨⟨c, hc, hr⟩, k, e⟩ := exists_int_vector_harmonicPoly_eq X (.trans .inl .inl) hα,
    (.prod_right nofun : l.Coprime u.levelNorm), (⟨nofun⟩ : IsEmpty (D.levelPlaces u).TwistIndex)
  let F h₁ h₂ h₃ := pointForm (O := X.auxPair) (Y := fun i ↦
    fromRows (fromRows (x₀.map (modulusResidue _ (places_levelModulus_false.ge ⟨_,
    rfl⟩))) (fromRows (inclMatrix _ chosenIndexEmb) (inclMatrix _ chosenIndexEmb)))
    (inclMatrix _ (lValueData H.2 u).auxPair.incl)) (U.blockSumOne (U.blockSumOne (1, U.blockSumOne
    (h₂, h₃)), h₁)) (fun _ _ _ h ↦ inclMatrix_mulVecLin_injective _ _ congr($h ∘ .inr))
    (chosenIndexEmb.trans (.trans .inl (.trans .inr .inl))) ((↑) ∘ c)
  refine ⟨xiSum H₂ ϑ fun h₂ ↦ xiSum H₃ u fun h₃ ↦ xiSum H u (F · h₂ h₃), fun g ↦ .trans (by
    simp [-classSum_mul]; ring!) (smul_apply_xiSum _ g fun _ _ ↦ smul_apply_xiSum _ g fun _ _ ↦
    smul_apply_xiSum (L := innerSLFlip ℂ _) _ g fun _ _ ↦ ?_), fun _ ↦ xiSum_mem _ hl fun _ ↦
    xiSum_mem _ k fun _ ↦ xiSum_mem _ k fun _ _ ↦
    (weylGauge_deltaForm_le isOfFinOrder_level_char).trans ?_, fun w hw hS ↦ (restrictScalars_mem
    embValRing ..).1 (xiSum_mem _ hl fun _ ↦ xiSum_mem _ k fun _ y hy ↦ inner_eq_zero_symm.1 ?_)⟩
  · erw [innerSLFlip_apply_apply, ← inner_conj_symm, ← X.theta_eq_inner_kernelForm, theta_pointForm,
      hc, ← modKernelBilin_apply]
    rw [mul_assoc (modKernel ..), ← hb]
    simp +singlePass (disch := simp +instances [levelModulus, levelPlaces, X, sq, ↓prod_of_isEmpty,
      *, funext_iff, Ideal.mul_le_left.trans]) only [↓kernelForm_of_jetDeg_eq_zero, modKernel,
      ← modDatum_factor (𝔪' := X.levelModulus 2), ← modKernel.eq_1]
    simp_rw [← modKernelI_block (.refl _)]
    simp [prod_eq_zero_iff, AuxPair.a]; congr! 2; obtain ⟨T, rfl⟩ :=
      _root_.Ideal.Quotient.mk_surjective.comp_left.comp_left ‹_›
    simp [(X.levelModulus 1 false).matrix_ext_modulusResidue X.isConjApart_chosenPlace.1, ← ext_iff,
      AuxPair.resDetDatum, X, ψ_eq_one, hG, univ_eq_empty, forall_and, ← ite_and]; congr! 1; tauto
  · erw [weylGauge_mul _ (Kf_le_localLevel _), weylGauge, hr] <;> simp [← map_inv, U.sum,
      funext_iff, pi_norm_le_iff_of_nonneg, norm_intCast_le_one]
  simp [xiSum, Pair.trivialLift, apply_eq_evalForm, LValueData.trivialLift, map_classSum, mul_assoc,
    ← mul_classSum, classSum_comm (K' := levelOf _ ⊥), ← innerSLFlip_apply_apply]; repeat right
  refine finsum_eq_zero_of_forall_eq_zero fun g ↦
    smul_eq_zero_of_right _ (stdClassSum_period_eq_zero X.fitsParams_auxPair (by simpa [X, ψ_eq_one,
    hG] using! (ϑ.psi_ne_one _ ·.2)) (fun i _ v ↦ hy.1.1.choose_spec ▸ ?_) hy.2
    hy.1.2 (by simp; grind [IsRankOne, le_m]) (.refl _) _ (.toSpanSingleton .. ∘ₛₗ gramForm (κ :=
    (lValueData H.2 u).auxPair.κ).flip 1) (fun _ _ _ f ↦ ?_) ?_ (one_mem _) (fun _ ↦ by
    simp [kernelForm_of_jetDeg_eq_zero, kernelVector, nablaBasis_eq_one, H.1, funext_iff,
      gramForm_apply, ← apply_eq_evalForm, dot_mulVec_eq_sum_sum,
    ← mul_sum, ← sum_mul, AuxPair.a]; ring!) rfl fun j hj ↦ ?_)
  · erw [← Module.End.mul_apply, ← map_mul,
      piTensorElem_mul_eq_zero i (reflectionSum_mul_labelIdem ((isApt_rank_one _
      hE).isLabel_twistedLabel (O := X.auxPair) i ∘ by simp +contextual [twistedLabel]) v)]; simp
  simp [conjWeylRep, hr, f]
  iterate 2 simp [weylRep, schur_eq_one, H.1, places_levelModulus, X, u, levelPlaces,
    twist_one_spec]
  have J i := mem_stabilizer_col_iff.1 ((mem_levelOf.1 hj).2 (.inl i) ⟨⟩)
  use by simp_all [AuxPair.resDetDatum, ↓Matrix.map_mul, ↓reductionK₀_map_modulusResidue,
    inv_mul_eq_iff_eq_mul_of_invertible, Kf.reduceFamily, univ_eq_empty, -Sum.elim_inl], by
    simpa using (map_block_eq_blockGL (reduceAt w) _ 1 j).1, fun i ↦ ?_
  simp; erw [(map_block_eq_blockGL _ _ 1 j).2, fromBlocks_mul_fromRows]
  simpa +instances [fromRows_ext_iff] using! J i

seal Finset.univ Finset.sum Finset.prod in
/-- For m-fold twists θ(ι) satisfying `Data.IsFitFamily`, 1 ≤ j ≤ m and a pair p of rank one for j
(`Data.Pair.IsRankOne`), the inverse L-value ratios 1/ρ_p(θ(ι)^j), ρ = `Data.Pair.ratio`, have
height (`HeightLe`) at most 6B₀ − 𝖴, 𝖴 = `Data.dirCost`.

Each ratio of Hecke values repays one direction. -/
lemma heightLe_inv_ratio {θ} (o : D.IsFitFamily θ) (j : D.LiftIndex) (p : D.Pair) (hE :
  p.IsRankOne j) : HeightLe (6 * D.B₀ - D.dirCost) fun ι ↦ (p.ratio ((θ ι).powTwist j))⁻¹ := by
  obtain ⟨f, _, A, H, _⟩ := ofFinite (tameChars D.finite_isChosen.toFinset), D.le_m,
    D.classAut_eq_bot_of_le_chosenLevel le_rfl (card_unit.trans_le D.nat_le_of_hasLogBound), id hE
  choose _ c₁ H₁ using D.exists_isFlat (Fin (2 * p.z - 20))
  have Z := D.exists_isFlat (Fin 4)
  obtain ⟨⟨q₂, c₂, H₂⟩, t, t0, ht, hd⟩ := Z ⟨(D.χ, D.ω), D.chi_hasWeight, by simp_all⟩,
    D.depth_indicator_jet (p.c · - p.z) fun τ ↦ by
      grw [nominalWeight_le_w_sub _ j, ← @w_le_nominalWeight_add _ D j (by grind)]
      norm_cast; grind
  choose _ c₃ H₃ using Z
  obtain ⟨⟨γ, g, G⟩, V, e⟩ := o.2 j, IsAlgClosed.exists_pow_nat_eq (∏ χ, Pair.intAlgPart (H₃ χ).2
    .one * (Pair.intAlgPart (H₁ χ).2 .one * (t * q₂.intAlgPart H₂.2 .one))) f.card_pos
  let N := Nat.card (StdClasses (n := Unit) D.chosenLevel)
  have K (l : PrimePadicIso) [PadicPlace l.1] : let ϑ := (θ l).powTwist j; ∃ Ξ,
      AuxPair.IsTestForm _ l.1 Ξ ∧ ‖ιₚ V‖ *
      l.1 ^ (-D.forcedPart l.1) ≤ ‖ιₚ (N ^ 2 * inner ℂ Ξ (Pair.trivialLift H ϑ) / q₂.ratio ϑ)‖ := ?_
  have hV (σ : ℂ ≃+* ℂ) : ‖σ V‖ ≤ exp D.B₀ := by
    choose _ _ _ h using exists_factorisation_le (σ : ℂ →+* ℂ) e 1
    simp at h; grw [h, ht]; repeat grw [norm_conj_intAlgPart_le]
    use D.le_of_hasLogBound D.lt_of_hasLogBound; all_goals apply_assumption
  refine (((heightLe_norm_trivialLift_sq hE).mul
    ((o.3 j q₂ 1 (by simpa [Pair.IsRamified, c₂] using D.omega_zpow_ne_one 1)).pow 2)).mul
    (y' := fun ι ↦ (q₂.ratio ((θ ι).powTwist j) / ‖Pair.trivialLift H ((θ ι).powTwist j)‖) ^ 2 /
    N ^ 3) ⟨V * star V, _, fun l ↦
    γ l + 2 • (D.forcedPart l * log l), by simpa [prod_eq_zero_iff, t0] using congr($e = 0), fun σ ↦
    exp_add .. ▸ map_mul σ .. ▸ norm_mul_le_of_le (hV σ) (hV (.trans starRingAut σ)), fun ι ↦ by
    choose Ξ b h using (@K ι ⟨(complexToCp ι.2).comp ·⟩)
    have := mul_le_mul (h 1) (h starRingAut.toRingHom) (by bound) (by bound)
    grw [exp_add, exp_nsmul, ← show ‖ι.2 (N * _)‖ ≤
      _ from ((G ι).2 p hE).rank_one_bound _ A (b 1) (b _)]
    simp [rpow_def_of_pos, ι.1.2.pos, exp_neg, ratio_ne_zero_and_real, field, -map_natCast, N,
      ← span_singleton_smul_eq (left_ne_zero_of_smul (trivialLift_ne_zero H .one)).isUnit
      (LValueData.trivialLift _), starProjection_singleton, ↓← Pair.trivialLift.eq_1] at this ⊢
    grw [this]; ring_nf; rfl, Filter.eventually_atTop.2 ⟨⌈D.x₁⌉₊, fun U hU ↦ by
    simp [dirCost, forcedPart, sum_mul, mul_sum, (filter ..).sum_comm, mul_assoc,
      D.primeSum_eq_sum_localAsk hU, (D.le_of_hasLogBound : D.nominalWeight _ ≤ D.a)]
    grw [g, (D.le_of_hasLogBound : D.x ^ 999 ≤ D.B₀)]; linarith; simp⟩⟩).mono (add_sub_cancel ..).le
    fun ι ↦ ?_
  have := @ratio_ne_zero_and_real
  have := @NeZero.ne ℕ
  simp [ratio_eq_intAlgPart_div H, Pair.intAlgPart, denomBound, twist_one_spec, field, *]
  repeat grw [norm_natCast_le_one]; simp
  intro ϑ; let b := (lValueData H ϑ).auxPair.b / (lValueData H₂.2 ϑ).auxPair.b
  obtain ⟨α, x₀, hα, hd⟩ :=
    hd (D.𝔪 ϑ 1 false) (pow_one D.piGBar ▸ D.ideal_untwistedModulus_eq_span) _
  obtain ⟨z, ψ, hr⟩ := exists_twisted_classSum_ge (D.levelPlaces ϑ).chosenPlace _
    (D.finite_isChosen.mem_toFinset.2 ·.2.2.1) ιₚ (modKernel (stdSpace ..) (stdSpace ..) 1 b _
    (Pi.single x₀ 1) (.monomial α 1) ⟨1, ·⟩ 1) le_rfl le_rfl A
  obtain ⟨ψ₃, ψ₁, hψ, h⟩ := exists_factorisation_le ιₚ e ψ
  refine (exists_test_form_inner_kernelForm (H₁ ψ₁) H₂ (H₃ ψ₃) (b := b / ψ.1.1) hE ϑ (o.1 l) x₀ hα
    (by simp [b, AuxPair.b, ← hψ, c₁, c₃, twist_one_spec, div_div, mul_assoc])).imp fun Ξ ⟨E, T⟩ ↦
    ⟨T, ?_⟩
  have n : stdClassSum (lValueData H ϑ).chosenLevel 1 =
    (N : ℂ) := show stdClassSum D.chosenLevel 1 = _ by simp [classSum, A, N]; rfl
  simp [MvPowerSeries.coeff_apply, Space.jetSeries_apply, modKernel, pairTheta, pairWeil, modDatum,
    n] at hd hr E
  grw [hd, hr, h, ratio_eq_intAlgPart_div H₂.2, Pair.trivialLift, inner_smul_right,
    ← inner_conj_symm, inner_trivialLift _ z]
  simp [map_classSum, hα, theta_eq_inner_kernelForm, division_def, ← mul_classSum, ← classSum_mul,
    α.degree_eq_sum, sum_prod_type, eq_div_of_mul_eq (by simp [N]) (E _)]
  field_simp [t0]
  ring_nf; rfl

/-- For m-fold twists θ(ι) satisfying `Data.IsFitFamily` and 1 ≤ j ≤ m, the numbers
(Γ(θ(ι)^j)/Γ(1))⁻¹, Γ = `Data.heckeValueProd`, have height (`HeightLe`) at most
10m·x^999 + k(6B₀ − 𝖴), 𝖴 = `Data.dirCost`.

Each ratio of Hecke values repays one direction. -/
lemma heightLe_inv_heckeValueProd_div {θ} (hf : D.IsFitFamily θ) j :
  HeightLe (10 * D.m * D.x ^ 999 + D.k * (6 * D.B₀ - D.dirCost)) fun ι ↦ (heckeValueProd j
  ((θ ι).powTwist j) / heckeValueProd j 1)⁻¹ := hf.heightLe_of_eq_zpow_mul (((HeightLe.prod (s :=
  Ioc (7 * (D.m / 2)) D.heckeCount) fun z _ ↦ heightLe_inv_ratio hf j ((linePair j none).lowerPoint
  z) (by simp [IsRankOne, HasLiftRank, Pair.lowerPoint, linePair]; grind [heckeCount, le_m])).mul
  (.prod (s := univ.sigma (Ioc 0 <| Option.elim · (7 * (D.m / 2)) D.eSign)) fun x _ ↦
  hf.3 j ((linePair j x.1).lowerPoint x.2) (x.1.getD 1)
  (by cases x.1 <;> exact omega_zpow_ne_one _ (by simp [Int.natAbs_mul]; grind)))).pow
  2) (by simp [eSign, heckeCount, Even.two_dvd, m_even, k_even]; grind) fun ι n ↦
  ⟨-∑ i, (linePair j i).z ^ 2, by
  simp [heckeValueProd,
    twist_one_spec, ↓lValueProd_eq _ _ ((θ ι).powTwist j).1, ↓_root_.zpow_neg, ↓zpow_natCast,
    Finset.prod_sigma, prod_pow, heckeCount, ← prod_Ioc_consecutive _ zero_le le_self_add, show ∀ s,
    Icc 1 (linePair j s).z = Ioc 0 (s.elim D.heckeCount D.eSign) by rintro ⟨⟩ <;> rfl] at n ⊢
  simp [*, field]; ring!⟩
