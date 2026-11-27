/- GID: D5/S3/Zeros/GRH/New/Selmer/ValueFamilies
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/ValueFamilies
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.ValueFamilies. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/ValueFamilies.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.Corepresentable
import D5.S3.Zeros.GRH.New.Rows.Carrier
import D5.S3.Zeros.GRH.New.Selmer.AptTuples
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: general results applied to the objects of this proof.

Also holds known results stated on this proof's data: Integral group-ring elements interpolating
twisted Hecke L-values, with norm relations. Source: N. Katz, p-adic L-functions for CM fields,
Invent. Math. 49 (1978); construction as theta elements: Bertolini, Darmon, Invent. Math. 126
(1996), adelic form Chida, Hsieh, J. reine angew. Math. 741 (2018); Euler factor: Tamagawa, Ann. of
Math. 77 (1963). Form here: Tame anticyclotomic twists of a fixed modulus, integral at all primes
away from it at once. At integers from 2 on the element is the squared norm of a theta lift from
U(1); at 1 it is a theta period on U(2) times its conjugate and gives the squared value. Adding a
place multiplies by Euler factors.

This file: Group-ring interpolation of twisted Hecke values, carried to the Galois side as
families. -/

open AutChar AlgHeckeChar Complex Data Finset HeckeChar Matrix

variable {P} {D : Data P} {ℓ} [ThePrime ℓ]

/-- For a ramified pair (ν, z) there are F on tame characters, K ⊆ {0, 1} and m with: F(1) ≠ 0;
F is an integral measure at each modulus; adding v to the modulus of ϑ multiplies F by
∏_{k∈K} ∏_± (1 − y^{±1}q_v^{k−z}), y the base change of νϑ at v; on twists F(ϑ) =
F(1)·N(Q)^m·ρ(ϑ)^{m+1}, ρ = `Data.Pair.ratio`.

Known result: Integral group-ring elements interpolating twisted Hecke L-values, with norm
relations. -/
lemma Data.Pair.exists_isIntegralMeasure (p : D.Pair) (r : p.IsRamified) : ∃ F K m, F .one ≠ 0 ∧
    (∀ ϑ : D.TameChar, ϑ.IsIntegralMeasure F) ∧ (∀ ϑ ϑ', ∀ v ∉ ϑ.Q, ϑ'.Q = insert v ϑ.Q →
  ϑ'.toAutChar = ϑ.toAutChar → ϑ'.ψ = ϑ.ψ → F ϑ' = F ϑ * ∏ k ∈ K, ∏ ε : ℤˣ,
  (1 - (p.ν * ϑ.toAutChar).baseChange.atUnif v ^ ε.1 / v.q ^ (p.z - @Fin.val 2 k))) ∧
  ∀ ϑ : D.Twist, F ϑ = F .one * (ϑ.levelNorm ^ m * p.ratio ϑ ^ (m + 1)) := by
  have s ϑ : ∀ w ∉ (D.𝔪 ϑ 2).places,
    (p.ψ * ϑ.ψ) w = 1 := by simp_all [places_modulus_eq_union, p.6, ϑ.5]
  cases' p.z_mem.1.lt_or_eq' with hz hz
  · use p.intAlgPart ⟨card_fin _, hz⟩, {0}, 0, by simp,
      isIntegralMeasure_intAlgPart _, ?_, by grind -abstractProof [ratio_eq_intAlgPart_div, intAlgPart_ne_zero]
    introv _ _ _ _
    obtain ⟨⟨_, ⟨⟩⟩⟩ := p.intAlgPart_eq_mul_L ⟨card_fin _, hz⟩, ϑ'.6 v,
      @levelNorm_mem_and_notMem_of_mem_Q _ D ϑ' v, @levelNorm_mem_and_notMem_of_mem_Q _ D ϑ'
      (star v), (p.hasWeight.mul ϑ.hasWeight).atUnif_star (w := v)
    simp [mul_assoc, L, *]
    convert (eulerProd_erase (p.hasWeight.mul ϑ.hasWeight).inv.isHeckeOfType.norm_heckeCoeff_le {v,
      star v}).2.2 p.z (mod_cast hz)
    · simp [funext_iff, heckeCoeff, Set.indicator]; grind -abstractProof [star_star]
    repeat simp_all [atUnif, heckeCoeff, cpow_neg, Ne.symm, places_modulus_eq_union,
      IsChosen] <;> grind -abstractProof
  let c := (p.c · - 1)
  have h ϑ := ((p.hasWeight.mul (TameChar.hasWeight ϑ)).mul_upsilonU1_pow 1).of_weight_eq (e' :=
    (-c ·)) (by grind -abstractProof [le_c, add_zero])
  obtain ⟨⟨N, _, J⟩, C, K⟩ := exists_modKernel_integral_bound (Fin 2) (Fin 2) D (univ.sum c * 2),
    stdClassSum_det_modKernel_eq _ even_two c
  let Λ ϑ := detPeriod (Fin 2) (p.ν * ϑ.toAutChar * WeilData.upsilonU1 ^ 1) c (D.𝔪 ϑ 2) (p.ψ * ϑ.ψ)
  choose γ b e using (K <| isTameFor_of_hasWeight (c := 2) · (h _) r)
  have a ϑ : ‖_ * Λ _‖ = _ := congr(‖$(e ϑ 1)‖)
  simp [places_modulus_eq_union, inv_mul_cancel_comm] at a b
  refine ⟨(‖D.chosenGroupOrder * N * Λ ·‖ ^ 2), univ, 1, by simp [NeZero.ne]; grind -abstractProof [norm_zero],
    fun ϑ ↦ let g (x : StdClasses (Kf ..) × GL _ (D.𝔪 ϑ 2).ResRing) := x.1.out * (liftMod x.2).1
    .norm_sq _ ⟨_, inferInstance, (detFin 1 <| g ·), _, fun x ↦ mul_mem (div_mem_integralAway
    ((D.card_classAut_dvd_chosenGroupOrder (by simpa using
      D.nat_le_of_hasLogBound) le_rfl x.1.out).mul_right (_ ^ 0))) fun l _ k j ↦
    congr(‖j (N * $(detKernel_embFin_mul (Pi.single 1 1) ..))‖).ge.trans
      (@(J _ _ _ (h .one) (h _) D.norm_mul_gProd_pow_mem_modulus (by simp [ite_mem]) _ _ _
      (by simp [letterMinor, det_apply', prod_pow_eq_pow_sum, prod_smul, ← smul_sum,
      smul_pow, pow_mul, sq, mul_smul])).1 l _ ⟨j⟩ k (by simp) (exists_mul_mem_integralAbove l (g x)
    1).choose_spec.1 ⟨∏ τ, det (of (.X ⟨τ, ·, ·⟩)) ^ c τ, by simp [letterMinor, det_apply]⟩), by
    rintro ⟨⟩ rfl
    simp [Λ, ↓detPeriod_eq_stdClassSum_sum (s _), classSum, detKernel, mul_sum, modKernel_twist,
      Fintype.sum_prod_type, Rat.smul_def, division_def]
    ac_rfl⟩, ?_, fun ϑ ↦ ?_⟩
  · introv _ _ _ c
    simp [Λ, ↓← mul_conj', ↓detPeriod_insert (c ▸ s ϑ) v, AutChar.frobValue, AutChar.spaceChar,
      IsChosen, *, ← ofReal_pow,
      prod_range, inv_eq_conj, places_modulus_eq_union, D.levelNorm_mem_and_notMem_of_mem_Q ϑ']
    ring
  have := And.intro (p.lValueProd_eq 1 ϑ) (b 1)
  simp [ratio, lowerPoint, hz, twist_one_spec] at this ⊢
  norm_cast at *; grind -abstractProof

lemma coprime_q_of_isAuxiliary {I} (c : IsAuxiliary (badPlaces D ℓ) I) :
    ℓ.Coprime (∏ w ∈ I, w.q) ∧ (D.gProd * D.N).Coprime (∏ w ∈ I, w.q) := Nat.coprime_mul_iff_left.1
    (.symm (.prod_left fun w h ↦ (c w h).2.1.coprime_iff_not_dvd.2 ((c w h).1 <| by
    simpa [badPlaces] using w.1.mem_of_dvd ·.natCast w.1.absNorm_mem)))

/-- A weight-zero character χ whose tame part is trivial off an auxiliary set I, regarded as a
tame character (`Data.TameChar`) for D with set of places Q = I. -/
@[simp] noncomputable def tameCharOfAuxiliary I (c : IsAuxiliary (badPlaces D ℓ) I) (χ :
  tameChars I) : D.TameChar := ⟨_, I, _, χ.2.1, χ.2.2, by grind, (coprime_q_of_isAuxiliary c).2⟩

lemma invAvatar_eq_of_artinMap_eq [PadicIso ℓ] {τ : D.TameChar} {x} {g : AbsGal D} (H :
  artinMap (AbsGal D) x = g) : τ.invAvatar g = ιℓ
  (τ.toAutChar.baseChange.finPart x)⁻¹ := ((exists_avatar.choose_spec _).2 x g H).trans
  (by simp [HasWeight.toAlgebraic, IsHeckeOfType.toAlgebraic])

lemma exists_tameChar_invAvatar_eq [PadicIso ℓ] {I} (hI : IsAuxiliary (badPlaces D ℓ) I) {ψ} (h :
  IsFromU1 (placesDividing _ ℓ) I ψ) : ∃ τ :
  D.TameChar, τ.Q = I ∧ ψ = τ.invAvatar := have ⟨_, φ, a, b, c⟩ := h
  (AutChar.exists_mem_tameChars (.comp ιℓ.symm (QuotientGroup.lift _ (φ.comp (.comp (Units.map
    (.snd ..)) Unitary.toUnits)) (sup_le (fun u h ↦ (exists_unitary_of_mem_rationalU1 h).elim fun y
    h ↦ congr(φ $(Units.ext (by simp [← h]))).trans (a (Unitary.toUnits y))) fun u ⟨h, k⟩ ↦
    b _ (idelesUnitOff_mono bot_le (coe_idelesUnitOff_empty.ge ⟨h, star_mem_Ô h⟩))
    (residue_eq_iff_valuation_sub_lt_one.1 <| k · ·.1))))).elim fun μ e ↦ ⟨tameCharOfAuxiliary _ hI
    μ⁻¹, rfl, MonoidHom.ext ((artinMap_surjective ..).elim fun x k ↦ invAvatar_eq_of_artinMap_eq k ▸
    c x · k ▸ congr(φ $(by bound)).trans (ιℓ.symm_apply_eq.1 ((inv_inv _).trans (e _)).symm))⟩

/-- For chosen w ∤ ℓ with tame generator σ, ramified p and a sign s, some family (ν, L)
(`IsFamily`) has all v(ν_i(σ) − 1) ≤ v(Nw − 1), and vL(Q, avatar of τ⁻¹) ≤ c + vL(∅,1)
implies v(ιρ) ≤ c, for c ≥ 0, twists τ with Q auxiliary, ρ = `Data.Pair.ratio` p τ s. -/
lemma exists_isFamily [PadicIso ℓ] {w} (hw : D.IsChosen w) (hℓ : w ∉ placesDividing _ ℓ) (p :
  D.Pair) s (hp : p.IsRamified) : ∃ ν val, IsFamily (T := Fin 2 × ℤˣ) (badPlaces D ℓ) ν val ∧
  (∀ i, ellVal ((ν i w.isPlaceOver_placeOver.tameGenerator).1 - 1) ≤ @ellVal ℓ _ (w.q - 1)) ∧ ∀ τ :
  D.Twist, IsAuxiliary (badPlaces D ℓ) τ.Q → ∀ c : NNReal, ellVal (val τ.Q τ.invAvatar) ≤
  c + ellVal (val ∅ 1) → ellVal (ιℓ (p.ratio τ s)) ≤ c := by
  obtain ⟨⟨_, U, h₀, o, hu⟩, F, K, m, n, H, law, hF⟩ :=
    w.isPlaceOver_placeOver.exists_localArtin_eq_tameGenerator, p.exists_isIntegralMeasure hp
  set γ : (ResField w)ˣ := (LocInt w).unitGroupToResidueFieldUnits _
  choose α _ u c hc b using (H <| tameCharOfAuxiliary · · 1⁻¹)
  choose y k using fun u ↦ (exists_divStar u).imp fun y k (τ : D.TameChar) ↦ show τ.toAutChar.1 u =
    (τ.toAutChar.baseChange.finPart
    y).1 by simpa [field] using! eq_of_mem_integralU1 τ.5 τ.4.2 _ (mem_integralU1_of_snd_eq_one _ k)
  let val I (χ : AbsGal D →* _) := ∑ᶠ h, ∑ a,
    ιℓ (c I h a) * χ ((artinMap _ (y (u I h a))).out ^ (-s.1))
  have key {I} h {τ} e : val I (TameChar.invAvatar τ) =
    ιℓ (F (tameCharOfAuxiliary I h (⟨(_, _), τ.4, e⟩ ^
    s.1))) := by simp [val, h, b I, ↓k, invAvatar_eq_of_artinMap_eq (Quotient.out_eq _).symm]
  have k : val ∅ 1 = ιℓ (F .one) := by simp [val, IsAuxiliary, b ∅ nofun, twist_one_spec]
  refine ⟨fun i ↦ ((p.hasWeight.zpow i.2).toAlgebraic 0 (-↑(p.z - i.1))).avatar, val, ⟨by fun_prop,
    fun I h ↦ ⟨_, _, _, _, by simpa using (hc I h · ℓ (coprime_q_of_isAuxiliary h).1 (complexToCp
    ιℓ)), fun _ ↦ finsum_eq_single _ h nofun⟩, ?_, by simpa [k]⟩, fun (i, e) ↦ ?_, fun τ c _ ↦ ?_⟩
  · introv _ hI hχ hA _ hc
    obtain ⟨J, _⟩ : IsAuxiliary (badPlaces D ℓ) I ∧ ↑ℓ ∉ P.1 ∧ ¬D.IsChosen P ∧ ¬D.IsChosen
      (star P) ∧ star P ∉ I := by clear * - hI; grind [isChosen_iff, placesAboveG, placesDividing]
    obtain ⟨⟨τ, rfl, rfl⟩, φ, rfl⟩ := exists_tameChar_invAvatar_eq J hχ, inv_surjective φ
    grw [key hI, law (tameCharOfAuxiliary _ J (⟨(_, _), τ.4, τ.5⟩ ^ s.1)), ← prod_product', map_mul,
      map_prod, ellVal_mul_le, apply_prod_le_sum_apply _ _ (by simp [ellVal]) (@ellVal_mul_le _ _),
      sum_le_card_nsmul _ _ _ fun (k, ε) _ ↦ (hc (k, -ε) (s * ε)).trans_eq' (by
     simp (maxDischargeDepth := 5) [TameChar.invAvatar, avatar_frob _ hA,
       HasWeight.charUnramifiedAt_toAlgebraic, τ.5, p.6, *]
     simp [atUnif, heckeCoeff, HasWeight.toAlgebraic, mul_zpow, _root_.zpow_mul, ↓← ofReal_zpow]
     ring), card_le_univ] <;> norm_num +contextual [τ.5, add_le_add, mul_le_mul', *]
  · apply ellVal_le_ellVal; simp [hu, HasWeight.toAlgebraic,
      avatar_localArtin _ w.isPlaceOver_placeOver (.inl hℓ) h₀, p.6, hw.not_star,
      p.hasWeight.baseChange_finPart_locIdele (hw.not_star <| ·.substr hw)]
    refine .trans (by simp [card_ResField, Nat.card_units])
      (norm_natCast_le_norm_sub_of_pow_eq_one (x := ιℓ (p.ψ w γ) ^ _) ?_
      (one_pow (.card (ResField w)ˣ)) ?_) <;> fin_cases e <;> simp [← map_pow,
      ← γ.val_pow_eq_pow_val, ιℓ.map_eq_one_iff, by simpa [MulChar.eq_iff o] using (hp w).2 hw]
  rw [ellVal_le_add_iff (k ▸ (H _).norm_apply_one_le _), key c τ.1.5,
    hF ⟨_, by fin_cases s <;> simpa using τ.2⟩]
  simp [k, (coprime_q_of_isAuxiliary c).1.norm_natCast_eq_one, -Nat.cast_prod]; field_simp [n]
  simpa [← norm_pow, ← ellVal_le_iff, add_mul, Pair.ratio, -map_div₀] using le_of_add_le_right
