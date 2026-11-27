/- GID: D5/S3/Zeros/GRH/New/Filling/AmplitudeSums
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/AmplitudeSums
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.AmplitudeSums. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/AmplitudeSums.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.UnipotentCovolume
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Second moment of the Poincaré series with constant one (see New.Filling.Moments).

Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Blocks of the unfolded moment: convergence, cut, weight change, moves, identity term. -/

open NumberField MeasureTheory Measure Complex ENNReal Classical Finset Fintype

namespace Filling

variable {E} [Field E] [CMType E] {𝔰} {S :
  Filling E 𝔰}

lemma isStable_besselS : S.IsStable (S.ratMiddle E).besselS := by
  simp +contextual [IsStable, mul_mem_cancel_right, mul_mem_cancel_left]

attribute [local simp] mul_assoc SMul.smul
variable {A : Subgroup 𝔰.G₁} (ν : Measure A) [h : IsUnimodularHaar ν]

instance : SigmaFinite (orbitMeasure ν (@volume 𝔰.G₁ _)) :=
  .withDensity_of_ne_top ((epsilon_spec h.out).ae_lt_top.mono (by order))

lemma measurePreserving_pi_orbitMeasure {P} [Fintype P] :
  MeasurePreserving (fun p ↦ (p.2 · |>.1) * p.1) (.prod (.pi fun _
  ↦ orbitMeasure ν volume) (.pi fun _ ↦ ν)) (@volume (P → 𝔰.G₁) _) := (measurePreserving_pi _ _
  fun _ ↦ measurePreserving_orbitMeasure).comp (measurePreserving_arrowProdEquivProdArrow ..).symm

lemma tsum_integral_apply {X J I} [MeasurableSpace X] {μ : Measure X} [Countable J] [Fintype I]
    {g : J → X → EuclideanSpace ℂ I} (m : ∀ j, Measurable (g j)) (h : ∑' j, ∫⁻ x, ‖g j x‖ₑ ∂μ < ∞)
    i : (∑' j, ∫ x, g j x ∂μ) i = ∫ x, ∑' j, g j x i ∂μ := .trans ((funext fun j ↦
  eval_integral_piLp (.eval_piLp ⟨by fun_prop, (ENNReal.le_tsum j).trans_lt h⟩) i) ▸
  (EuclideanSpace.proj i).map_tsum (.of_enorm (ne_of_lt (by grw [enorm_integral_le_lintegral_enorm,
  h])))) (integral_tsum (by fun_prop) (ne_of_lt (by grw [PiLp.enorm_apply_le, h]))).symm

variable [σ : Side]

noncomputable instance : Fintype S.GRes := .ofFinite _

lemma besselFn_mul_of_mem_classUnip {c} (u : S.classUnip c) y : S.besselFn (S.ratToInf u * y) =
  S.besselFn y := have := u.2
  by simp_all [classUnip, besselFn_ratToInf_mul,
    unipotentChar_eq_of_mem_principalLevel (one_mem _) _ c.out]

lemma besselKernel_besselU_mul {u u'} (a : u ∈ besselU) (a' : u' ∈ besselU) γ y :
  S.besselKernel (u * γ * u'⁻¹) (S.ratToInf u * y) =
  ((S.unipotentChar (S.ratToFin u))⁻¹ * S.unipotentChar (S.ratToFin u')) • S.besselKernel γ y := by
  ext; simp [besselKernel, *, besselFn_ratToInf_mul, unipotentChar, ← inv_eq_conj, field]

variable [StablyUnram E] [S.IsAdmissible] (T c s c')

omit [Side] in
lemma lintegral_classCutoff_mul_prod {w : _ → _} (hm : ∀ v, Measurable (w v)) (hU : ∀ v,
  besselU.FixesLeft (w v)) c : ∫⁻ y, S.classCutoff c y * ∏ v, w v (y v) =
  .ofReal S.unipCovolume * ∏ v, ∫⁻ y, w v y ∂besselQuotMeasure := by simp (disch := measurability)
  [← (measurePreserving_pi_orbitMeasure 𝔰.besselHaar).lintegral_comp, lintegral_prod, Pi.mul_def,
  hU, lintegral_mul_const, lintegral_classCutoff_eq_unipCovolume, lintegral_pi_prod]

/-- Under `Filling.IsAdmissible`, for the full or cut W and γ over the terms of T over (c, s, c'):
∑β_c'(γ⁻¹y)∏_v‖W_v((γ⁻¹y)_v)‖ is bounded in y, and amplitudes converge absolutely. For fixed
c, s, ∑_{c',γ}∫β_c(y)β_c'(γ⁻¹y)‖kernel − cut kernel‖dy ≤ νb^(−k³f)/2. Here β_c =
`Filling.classCutoff` c and ν = `Filling.unipCovolume`. -/
lemma amplitudeAbs_lt_top_and_cut_le : let X d := T ∩ S.termsOver c s d; (∀ c',
    (∃ M : NNReal, ∀ y, ∑' γ : X c', S.classCutoff c'
    ((S.ratToInf γ)⁻¹ * y) * ∏ v, ‖(S.besselSys v).W σ (((S.ratToInf γ)⁻¹ * y) v)‖ₑ ≤ M) ∧ ∑' γ :
    X c', S.amplitudeAbs c c' γ < ∞) ∧ ∑' (d) (γ : X d), ∫⁻ y, S.classCutoff c y * S.classCutoff d
    ((S.ratToInf γ)⁻¹ * y) * ‖S.besselKernel γ y - S.besselKernel (σ := .cut) γ y‖ₑ ≤
    .ofReal (S.unipCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := S.of_size_bounds <| by
  intros; rename_i X; obtain ⟨⟨r, k⟩, f⟩ := S.pow_le_k.dest, S.k_le_f
  choose A m hm hU hW hA _ l using (S.besselSys · |>.tail.exists_majorant)
  let Q (z : InfinitePlace E → 𝔰.G₁) := Set.univ.pi fun v ↦ {g | InCut (z v * g) S.b}
  have R {z} : MeasurableSet (Q z) := .univ_pi (by measurability)
  choose! u a b using fun {d z g} (h : (Q z).indicator (fun _ ↦ S.classCutoff d z * 1) g ≠ 0) ↦
    exists_classUnip_mul_mem_boxedPoints d (Set.mem_of_indicator_ne_zero h · ⟨⟩)
  have n y := lintegral_mono (μ := .pi m) fun g ↦ tsum_classCutoff_box_le (V := ⊤) (y' :=
    y) Sigma.subtype_ext (fun (p : Σ d, X d) h ↦ ⟨.mul p.2.2.2 (.inv (a h).2), by simp [a h], by
    simpa using! b h, Set.indicator_le_self _ _ g⟩) (by simp)
  simp (disch := fun_prop (disch := tauto)) only [Q, pi_pi, mul_one, lintegral_const,
    lintegral_indicator_const R, lintegral_tsum, ENNReal.tsum_sigma'] at n
  have o {n} := one_le_ofReal.2 (one_le_pow₀ (n := n) ‹_›)
  grw [← hA] at n
  have e τ (y : _ → _) := prod_mono' fun v ↦ hW v τ (y v)
  simp [↓prod_mul_distrib, prod_ite] at e
  have h1 := lintegral_mono (μ := volume) fun y ↦
    mul_le_mul_right (n y) (S.classCutoff c y * ∏ v, A v (y v))
  simp (disch := fun_prop) only [← ENNReal.tsum_mul_left, lintegral_tsum, lintegral_mul_const,
    mul_mul_mul_comm _ _ (classCutoff ..), lintegral_classCutoff_mul_prod _ hU, pi_univ] at h1
  grw [mul_comm, mul_mul_mul_comm, ← prod_mul_distrib, l, prod_mul_distrib, prod_const,
    ← Nat.cast_prod, ← Fintype.card_pi] at h1
  have p γ y := have q τ := mul_le_mul' (e τ y) (e τ ((S.ratToInf γ)⁻¹ * y))
    (mul_le_iff_le_inv (one_pos.trans_le o).ne' ofReal_ne_top).1 ((add_le_add (q σ)
    (q .cut)).trans' (byCases (by
    simp_rw [mul_mul_mul_comm _ (univ.prod _), ← mul_add, ← enorm_besselKernel]
    grw [← pow_add, ← enorm_sub_le, ← le_self_pow o ·])
      (by cases σ <;> simp +contextual [besselKernel, besselFn])))
  use fun c' ↦ ?_, ?_; grw [← ENNReal.le_tsum c', ← le_mul_of_one_le_left' (one_le_pow₀ o)] at *
  simp_rw [amplitudeAbs, enorm_besselKernel]; grw [e, e, e, n, h1]
  use ⟨_, fun _ ↦ (coe_toNNReal ?_).ge⟩ <;> finiteness
  grw [p]; simp (disch := finiteness) only [mul_left_comm _ (_⁻¹ * _), ← two_mul,
    ← mul_assoc _⁻¹, lintegral_const_mul', ENNReal.tsum_mul_left]
  grw [h1]
  simp (disch := finiteness) [le_ofReal_iff_toReal_le, field, -Fintype.card_pi]
  grw [IsAdmissible.card_besselCoord_le, ‹2 ≤ S.b›]
  simp [← pow_mul, ← pow_add, ← k]
  gcongr; lia

/-- Under the standing hypotheses, for any set T of rational elements, the amplitudes of the
terms of T over (c, s, c') form a summable family. -/
lemma summable_amplitude : Summable fun γ : ↥(T ∩ S.termsOver c s c') ↦ S.amplitude c c' γ :=
  .of_enorm (ne_of_lt (by grw [enorm_amplitude_le, ((amplitudeAbs_lt_top_and_cut_le ..).1 _).2]))

variable {T} (hT : S.IsStable T)
include hT

/-- Change of weight: for stable T and measurable φ(γ,y) ≥ 0 of sum 1 on 𝖴_c(g)×𝖴_c'(g)-orbits,
the integrals ∫φ(γ,y)W(y)⊗W(γ⁻¹y)^*dy over terms of T over (c,s,c') converge and sum to
A_T(c,s,c'), and ∑_γ∫φ‖full kernel − cut kernel‖ ≤ νb^(−k³f)/2. -/
lemma hasSum_amplitudeSum_change_of_weight c s c' (φ : _ → _ → _) (h : ∀ γ ∈ T ∩ S.termsOver c s c',
  ∀ y, ∑' u : S.classUnip c × S.classUnip c',
  φ (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1) (hm : ∀ γ, Measurable (φ γ) := by measurability) :
  let X := T ∩ S.termsOver c s c'; HasSum (fun γ : X ↦ ∫ y, (φ γ y).toReal • S.besselKernel γ y)
    (S.amplitudeSum T c s c') ∧ (∀ γ : X, Integrable fun y ↦ (φ γ y).toReal • S.besselKernel γ
    y) ∧ ∑' γ : X, ∫⁻ y, φ γ y * ‖S.besselKernel γ y - S.besselKernel (σ := .cut) γ y‖ₑ ≤
    .ofReal (S.unipCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := by
  intro X; let Δ := S.classUnip c × S.classUnip c'; let : MeasurableSpace (S.G E) := ⊤
  let : MulAction Δ X := by refine' { smul u γ := ⟨_, (hT _ u.1⁻¹.2.1 _ u.2⁻¹.2.1 _).2 γ.2.1, by
    simpa using termsOver.mul (.mul u.1.2.2 γ.2.2) u.2⁻¹.2.2⟩, .. } <;> simp [HSMul.hSMul, Δ]
  let Y := InfinitePlace E → 𝔰.G₁
  let : MulAction Δ Y := .compHom _ ((S.ratToInf.domRestrict _).comp (.fst ..)); let := this.toSMul
  let K [Side] := fun ((γ : X), y) ↦ S.besselKernel γ y; let ρ := (@count X _).prod (@volume Y _)
  have p (u : Δ) : MeasurePreserving (u • ·) ρ ρ :=
    (measurePreserving_count (MulAction.toPerm u)).prod (measurePreserving_mul_left ..)
  have := MeasurableSMul₂.mk (measurable_from_prod_countable_right (p · |>.1))
  have := (((smulInvariantMeasure_tfae Δ ρ).out 7 1).1 p :)
  have k [Side] (u : Δ) p : K (u • p) =
    K p := by simp +zetaDelta [besselKernel, HSMul.hSMul, besselFn_mul_of_mem_classUnip]
  have mK [Side] : Measurable K := by fun_prop [besselKernel]
  have b : IsCutoff (@count Δ _) fun ((γ : X), y) ↦
    S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y) :=
    ⟨by fun_prop, by simp +zetaDelta [HSMul.hSMul, tsum_classCutoff_eq_one]⟩
  have q {β} (h : IsCutoff _ β) : _ ∧ _ ∧ _ :=
    have w {F} hF (hi := by simp [k]) := lintegral_withDensity_eq_lintegral_mul ρ h.1 hF ▸
      ((identDistrib_orbitMeasure h hF hi).symm.trans (identDistrib_orbitMeasure b hF
      hi)).lintegral_eq.trans_le ((lintegral_withDensity_le_lintegral_mul _ b.1 F).trans
      ((lintegral_prod_le _).trans_eq (lintegral_count _)))
    have i := integrable_toReal_smul h.1 (by fun_prop)
      ((w mK.enorm).trans_lt ((amplitudeAbs_lt_top_and_cut_le ..).1 _).2)
    ⟨by simpa using
      ((h.integral_orbitMeasure k mK).trans (integral_prod _ i) ▸ hasSum_integral_measure
      i.integral_prod_left :), ae_count_iff.1 i.prod_right_ae, have d := (mK.sub (@mK .cut)).enorm
      by simpa [ρ, ↓lintegral_prod _ (h.1.mul d).aemeasurable] using (w d).trans (.trans
        (by exact ENNReal.le_tsum (f := fun d ↦ ∑' γ : ↑(T ∩ S.termsOver c s d), ∫⁻ y,
        S.classCutoff c y * S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
        ‖S.besselKernel γ y - S.besselKernel (σ := .cut) γ y‖ₑ) c')
        (amplitudeAbs_lt_top_and_cut_le T c s).2)⟩
  exact ((q b).1.tsum_eq ▸ @q (Function.uncurry (φ ·)) ⟨measurable_from_prod_countable_right
    (hm ·), ((lintegral_count _).trans <| h _ ·.1.2 _)⟩ :)

/-- Let T be stable, σ over (c,t,c₁) and σ' over (c',t',c₁') lie in S, with γ ∈ T iff σγσ'⁻¹ ∈
T. If a continuous linear L takes the kernel at (γ,y) to that at (σγσ'⁻¹,σy), then A_T(c,
tst'⁻¹, c') = L A_T(c₁,s,c₁') for the amplitude sums. -/
lemma amplitudeSum_move {c t c₁ σ c' t' c₁' σ'} (h : σ ∈ besselS) (o : σ ∈ S.termsOver c t c₁) (h' :
  σ' ∈ besselS) (o' : σ' ∈ S.termsOver c' t' c₁') (e : ∀ γ, γ ∈ T ↔ σ * γ * σ'⁻¹ ∈ T) (L : _ →L[ℂ]
  _) (hL : ∀ γ y, S.besselKernel (σ * γ * σ'⁻¹) (S.ratToInf σ * y) = L (S.besselKernel γ y)) s :
  S.amplitudeSum T c (t * s * t'⁻¹) c' = L (S.amplitudeSum T c₁ s c₁') := by
  have m {c t d σ c' t' d' τ s γ} o o' : γ ∈ S.termsOver d s d' ↔
    σ * γ * τ⁻¹ ∈ S.termsOver c (t * s * t'⁻¹)
    c' := ⟨(.mul · (.inv o')) ∘ .mul o, (by simpa using termsOver.mul (.inv o) <| .mul · o')⟩
  have b {c t c₁ σ} h o y := (((MulAut.conj σ).subtypeEquiv (p := (· ∈ S.classUnip c₁)) fun γ ↦
    .trans (.and (besselS_le_normalizer_besselU h γ) (m (t := t) o o)) (by simp; rfl)).tsum_eq
    _).trans (tsum_classCutoff_eq_one c (S.ratToInf σ * y))
  simp [-Subtype.forall] at b
  refine (hasSum_amplitudeSum_change_of_weight hT _ s _ (fun γ y ↦
    S.classCutoff c (S.ratToInf σ * y) * S.classCutoff c' (S.ratToInf (σ' * γ⁻¹) * y))
    (by simp [b h o, b h' o'])).elim fun k f ↦ (((.mulRight σ'⁻¹ * Equiv.mulLeft σ).subtypeEquiv
    (by simp [← e, m o o', -mul_assoc])).hasSum_iff.1 ((k.mapL _).congr_fun fun γ ↦
    (integral_mul_left_eq_self _ (S.ratToInf σ)).symm.trans ?_)).tsum_eq
  simp [↓← L.integral_comp_comm (f.1 γ), ← hL]

lemma amplitudeSum_besselU_mul {u u' : S.latStabilizer} (hu : u.1 ∈ besselU) (hu' :
  u'.1 ∈ besselU) c s c' : S.amplitudeSum T c (S.reduction u * s * (S.reduction u')⁻¹) c' =
  ((S.unipotentChar u)⁻¹ * S.unipotentChar u') • S.amplitudeSum T c s c' := by
  obtain ⟨⟨x, _, ⟨k, _⟩, _⟩, _, a', ⟨k', _⟩, _⟩ := exists_rat_approx_unipotentChar_eq c hu,
    exists_rat_approx_unipotentChar_eq c' hu'
  apply amplitudeSum_move hT _ ⟨u * k, _⟩ (mem_unitriGroup_of_mem_besselU a') ⟨u' * k', _⟩
    (hT x⁻¹ _ _ _ · |>.symm) (.lsmul ℂ ℂ _) <;> simp_all [↓besselKernel_besselU_mul]

/-- If T is stable under 𝖴(E⁺) on both sides and s does not agree, that is the character of Ū
differs from its conjugate by s on Ū ∩ sŪs⁻¹, then the sum of amplitudes of T over (c, s,
c') vanishes. -/
lemma amplitudeSum_eq_zero_of_not_agrees (hs : ¬S.Agrees s) : S.amplitudeSum T c s c' = 0 :=
  by_contra (hs fun _ _ _ _ _ ↦
  eq_of_inv_mul_eq_one <| smul_left_injective _ · (by simp [← amplitudeSum_besselU_mul, *]))

omit σ hT

/-- Let T be the group of rational points of the Bessel subgroup 𝖴H. The sum of the amplitudes
of the elements of T over (c, 1, c') has (i, j) entry ν = `Filling.unipCovolume` if
c = c' and i = j, and 0 otherwise. -/
lemma amplitudeSum_besselS_one i j : S.amplitudeSum (σ := .full) (S.ratMiddle E).besselS c 1 c' (i,
  j) = ite (c = c' ∧ i = j) S.unipCovolume 0 := by
  obtain h | rfl := ne_or_eq c c'
  rw [amplitudeSum, tsum_congr fun γ ↦ (h (γ.2.elim eq_and_mem_classUnip_of_besselS).1).elim,
    tsum_zero]
  simp [h]
  obtain ⟨k, f, -⟩ := hasSum_amplitudeSum_change_of_weight isStable_besselS c 1 c
    (if 1 = · then S.classCutoff c else 0) fun γ h y ↦ by
    lift γ to S.classUnip c using (h.elim eq_and_mem_classUnip_of_besselS).2
    norm_cast
    simp [ite_apply, ↓eq_mul_inv_iff_mul_eq, tsum_classCutoff_eq_one]
  rw [k.unique (hasSum_single ⟨1, one_mem _, (classUnip ..).one_mem.2⟩ (by aesop)),
    eval_integral_piLp (f _).eval_piLp,
    ← ((measurePreserving_pi_orbitMeasure 𝔰.besselHaar).fubini ((f _).eval_piLp _)).2]
  simp [besselKernel, besselFn, ← prod_mul_distrib, Pi.mul_def,
    ((besselSys ..).tail.isBesselFunction _).2, mul_conj', integral_complex_ofReal, mul_mul_mul_comm
    _ _ (starRingEnd _ _), apply_ite ofReal, integral_toReal (Measurable.aemeasurable (by fun_prop))
    (ae_lt_top (by fun_prop) (S.lintegral_classCutoff_eq_unipCovolume c _ ▸ ofReal_ne_top)),
    lintegral_classCutoff_eq_unipCovolume, Fintype.prod_boole, (integral_fintype_prod_eq_prod
    _).trans congr(∏ v, $((S.besselSys v).orthonormal ..)), S.unipCovolume_pos.le, funext_iff]
