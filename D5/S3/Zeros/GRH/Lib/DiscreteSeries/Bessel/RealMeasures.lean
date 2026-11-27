/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bessel/RealMeasures
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Bessel/RealMeasures
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Bessel.RealMeasures. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Bessel/RealMeasures.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bessel.UnipotentCoords
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar.RegularRepL2
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Bessel subgroup of a real unitary group, with coordinates, Haar measure and Bessel
functions. No Bessel model is constructed in these files. They give only coordinates and
Lebesgue–Haar measure on the unipotent radical, a measure on the Bessel subgroup that unfolds the
quotient, and Bessel functions for a compact small group with the invariance of their norms. Source:
for the setting, H. Xue, Bessel models for real unitary groups: the tempered case, Duke Math. J. 172
(2023) 995-1031; R. Beuzart-Plessis, Astérisque 418 (2020).

This file: Haar measure on unipotent subgroups is Lebesgue in free entries, bi-invariant,
conjugation-invariant. Haar measures on the real unitary group are σ-finite. -/

open Subgroup ENNReal FI Finset Fintype Function Matrix MeasureTheory MeasureTheory.Measure
  Norms.L2Operator

attribute [local simp] Fin.exists_fin_succ' Fin.forall_fin_succ' continuous_U_iff_matrix funext_iff
  mul_assoc

variable {𝔰 : Shape} {S : Subgroup 𝔰.G₁} {P : _ → _ → Prop} {T : ℝ} (hS : ∀ {u}, u ∈ S ↔ ∀ i j,
  P i j → u.1.1 i j = (1 : Matrix ..) i j) {p : Fin 𝔰.ϱ × 𝔰.BesselIndex → Prop}

lemma mem_besselU0_iff_apply {u : 𝔰.G₁} : u ∈ besselU0 ↔ ∀ i j, level j ≤ level i ∨ j ∈ Set.range
  𝔰.besselFrame → u.1.1 i j = (1 : Matrix ..) i j := by simp_rw [or_imp, forall_and]; rfl

@[fun_prop] lemma continuous_embedH :
  Continuous (@embedH 𝔰) := by simp [coe_embedH, actOnCols]; fun_prop

/-- The measure ν on the subgroup S of G₁ is a σ-finite Haar measure, right and inversion
invariant, with a cutoff: a measurable weight on G₁ of integral 1 on each S-orbit. -/
class IsUnimodularHaar (ν : Measure S) : Prop extends ν.IsHaarMeasure, ν.IsMulRightInvariant,
  ν.IsInvInvariant, SigmaFinite ν, HasCutoff ν 𝔰.G₁

/-- For T ≥ 1 some d in G₁ has ‖d‖ ≤ T^ϱ, conjugation u ↦ d⁻¹ud multiplies the entry (i, j) by
T^{lev i − lev j}, and ‖d⁻¹ud‖ ≤ 1 + N²‖u‖/T for u in 𝖴, N the rank of G₁. -/
lemma exists_dilation (hT : 1 ≤ T) : ∃ d : 𝔰.G₁, ‖d.1.1‖ ≤ T ^ 𝔰.ϱ ∧
  (∀ u i j, (d⁻¹ * u * d).1.1 i j = T ^ (level i - level j : ℤ) * u.1.1 i j)
  ∧ ∀ u ∈ besselU, ‖(d⁻¹ * u * d).1.1‖ ≤ 1 + 𝔰.r ^ 2 * (‖u.1.1‖ / T) := by
  have ⟨t, _⟩ : Complex.ofReal T ≠ 0 ∧ |T| = T := by simp; grind
  refine (exists_U_coe_eq (x := diagonal fun i ↦ T ^ (𝔰.ϱ - level i : ℤ)) (by
    simp [← ext_iff, level, ← zpow_add₀ t]; grind [zpow_zero])).imp fun d e ↦ ⟨by simp [
      pi_norm_le_iff_of_nonempty, ← zpow_natCast, zpow_le_zpow_right₀, *], ?c, fun u hu ↦ .trans
    (norm_le_insert' _ 1) (add_le_add (by simp) (sq (_ : ℝ) ▸ l2_opNorm_le_of_apply fun i j ↦ ?_))⟩
  · simp [inv_diagonal, Ring.inverse, Pi.isUnit_iff, zpow_sub₀, field, *]
  simp [↓Matrix.sub_apply, ↓?c]; by_cases level j ≤
    level i <;> split <;> simp [mem_besselU.1, field, *]
  grw [norm_apply_le_l2_opNorm, (by lia : _ - _ ≤ -1)]; simp [field]

include hS

/-- Let S be the subgroup of G₁ of elements that agree with the identity matrix at a given set
of positions, normalised by the Bessel subgroup `besselS`. Then conjugation by any s in the
Bessel subgroup preserves every Haar measure μ on S. -/
lemma measurePreserving_conj_bessel {μ s} [IsHaarMeasure μ] (n : besselS ≤ normalizer S) (h :
  s ∈ besselS) : MeasurePreserving (fun u : S ↦ ⟨s * u.1 * s⁻¹, (n h u).1 u.2⟩) μ μ := by
  have := isClosed_of_entries_eq_one hS
  let c s : S ≃ₜ* S := by use S.normalizerMonoidHom s <;> exact .subtype_mk (by fun_prop) _
  let χ := MonoidHom.mk' (fun s ↦ Units.mk0 _ (mulEquivHaarChar_pos (c s)).ne')
    fun _ _ ↦ .trans (by ext; simp [← mulEquivHaarChar_trans, c]; rfl) (mul_comm ..)
  use by fun_prop, (one_smul ℝ≥0∞ _).symm.trans ((ENNReal.mul_eq_right (a := χ (inclusion n
    ⟨s, h⟩)) (b := ⨆ t, χ (inclusion n t) * μ {y | ‖y.1.1.1‖ ≤ 2})
    (by simpa using measure_sublevel_ne_zero _) (ne_top_of_le_ne_top
    ((isCompact_U_norm_le _).preimage_val.measure_ne_top (μ := μ)) (iSup_le fun ⟨t, m⟩ ↦ by
    obtain ⟨u, h, w, rfl⟩ := exists_besselU_mul_toBesselH m
    refine (exists_dilation (U.one_le_norm u)).elim fun d ⟨_, a, b⟩ ↦
      (mulEquivHaarChar_smul_preimage ..
      ).le.trans' (mul_le_mul' (mod_cast (fun v w d ↦ show χ (v * w) ≤ χ (w * (d⁻¹ * v * d)) by
      simp [mul_comm (χ v)]) ⟨_, n (mem_unitriGroup_of_mem_besselU h)⟩ ⟨_,
      n (mem_unitriGroup_of_mem_floorGroup (toBesselH_mem w))⟩ ⟨d, mem_normalizer_iff''.2 fun v ↦ by
     simp_rw [hS, a, one_apply]; congr! 3; split <;> simp [*, zpow_ne_zero]⟩) (μ.mono fun y k ↦ ?_))
    specialize b _ h; grw [div_self_le_one, ← norm_embedH_mul] at b
    exact norm_mul_le_of_le (norm_mul_le_of_le b k) ((U.norm_inv _).trans_le b)))).1 (.trans (by
    simp [mul_iSup]) (Equiv.mulLeft ⟨s, h⟩).iSup_comp) ▸ mulEquivHaarChar_smul_map ..)

lemma exists_measurePreserving_freeEntries (hp : ∀ a i, p (a, i) ↔ ¬P (.inl a) i ∧ level i < 2 *
  𝔰.ϱ - a) {g : 𝔰.G₁} (hg : g ∈ besselU) : ∃ T, MeasurePreserving T ∧ ∀ u ∈ S, freeEntries p (u *
  g) = T (freeEntries p u) := let Z a j (x : Subtype p) := ite (x.1.1 = a) ((g.1.1 - 1) x.1.2 j) 0
  let Y := 1 + of fun x : Subtype p ↦ Z x.1.1 x.1.2
  ⟨_, .add_right _ (freeEntries p g) (.comp (.skew_product (f := Y.mulVec) ⟨by fun_prop, by
    simp [map_mulVec_haar, det_eq_one_of_unitriangular (Z := Y) (lev := (-level ·.1.2 : _ → ℤ))
      (by simp_all [Y, Z, mem_besselU])]⟩ (by fun_prop) (.of_forall fun v ↦ map_add_right_eq_self _
    fun a ↦ (Z a (eStar a) ⬝ᵥ v).im)) (measurePreserving_sub_right _ (freeEntries p 1))), fun u h ↦
    eq_add_of_sub_eq (.symm (by
  erw [← map_sub, ← sub_one_mul, ← add_sub_cancel 1 g.1.1, mul_add]
  ext <;> simp [Y, ← map_sub] <;> [skip; congr 1] <;> apply sum_bij_ne_zero
    fun x _ _ ↦ x.1.2 <;> simp_all [Z, mem_besselU, level, -Sum.forall] <;> grind))⟩

/-- Let S ≤ 𝖴 be defined by prescribing entries of the identity matrix and be normalised by the
Bessel subgroup. If the remaining free entries are injective on S and carry ν to Lebesgue
measure, ν is a σ-finite Haar measure, bi-invariant and inversion invariant. -/
lemma IsUnimodularHaar.of_freeEntries (hp : ∀ a i, p (a, i) ↔ ¬P (.inl a) i ∧ level i < 2 * 𝔰.ϱ - a)
    (n : besselS ≤ normalizer S.carrier) (l : S ≤ besselU) {ν : Measure S} (hi : Injective fun u :
  S ↦ freeEntries p u) (v : MeasurePreserving (freeEntries p ·.1) ν) : IsUnimodularHaar ν := by
  have := isClosed_of_entries_eq_one hS; have := this.polishSpace
  have : (haar : Measure S).IsMulRightInvariant := ⟨fun ⟨g, m⟩ ↦ by simpa using!
    ((measurePreserving_conj_bessel hS n (mem_unitriGroup_of_mem_besselU (l (inv_mem m)))).mul_left
    _ ⟨g, m⟩).2⟩
  obtain ⟨d, rfl⟩ := have := v.sigmaFinite; exists_eq_smul_haar haar (ν := ν) ⟨fun g ↦
      (exists_measurePreserving_freeEntries
    hS hp (l g.2)).elim fun _ t ↦ (v.1.measurableEmbedding hi).map_injective (by
    simpa [map_map v.1, measurable_mul_const, v.2, comp_def, t] using (t.1.comp v).2)⟩
  have g := isUnit_iff.1 (.of_mul_eq_one _ (by
    simpa using (v.lintegral_comp (by fun_prop)).trans lintegral_gaussian_eq_one))
  exact have := IsHaarMeasure.smul (G := S) haar g.1 g.2; { hasCutoff_of_proper with }

omit hS

@[fun_prop] lemma continuous_unipotentOf :
  Continuous (@unipotentOf 𝔰) := by simp [unipotentOf]; fun_prop

@[fun_prop] lemma continuous_liftUnitri :
  Continuous (@liftUnitri 𝔰) := by simp [liftUnitri]; fun_prop

attribute [local simp] level Injective Prod.ext_iff inclMatrix

/-- The free entries (`freeEntries` at `IsFreeEntry₀`) determine an element of 𝖴⁰, and they carry
the measure `Shape.besselHaar₀` on 𝖴⁰ to Lebesgue measure.

Known result: Bessel subgroup of a real unitary group: coordinates, Haar measure, Bessel
functions. -/
lemma besselHaar₀_spec : (Injective fun u : (𝔰.middleGram 1).besselU0 ↦
  freeEntries IsFreeEntry₀ u.1.1.1) ∧ MeasurePreserving (freeEntries IsFreeEntry₀ ·.1.1.1)
  𝔰.besselHaar₀ := let g :=
    (mulRightLinearMap _ ℝ 𝔰.definiteColsᴴ).coprod (mulRightLinearMap _ ℝ 𝔰.dualColsᴴ ∘ₗ skewOfReal)
  have t (g : _ → ℝ) (y : _ → _ → _) (h : ∀ a, ∀ b > a, g (a, eStar b) = y b a + y a b) : ∑ x :
    Subtype IsFreeEntry₀, g x.1 + ∑ a, y a a = ∑ a, ∑ i, g (a, 𝔰.indexX₀ i) + ∑ a, ∑ b, y b a := by
    simpa +contextual [← subtype_univ, sum_filter, add_assoc, h, ite_add_zero, sum_prod_type,
      ← filter_lt_eq_Ioi, eq_sub_iff_add_eq, compl_eq_univ_sdiff] using
      sum_sum_Ioi_add_eq_sum_sum_off_diag y
  let E := ((freeEntries IsFreeEntry₀).1 ∘ₗ mulLeftLinearMap _ ℝ 𝔰.isotropicCols ∘ₗ
    g).linearEquivOfInjective (by
    simp [g, skewOfReal, entrywise, -Complex.re_sum, -Complex.im_sum, Complex.ext_iff]; grind) (by
    rify; simpa [Module.finrank_matrix] using (t 2 1 (by bound)).symm)
  let c a := E.symm.1 (freeEntries IsFreeEntry₀ (unipotentOf (a, 0)).1.1)
  have e q : E (q.1, q.2 + (c q.1).2) = freeEntries IsFreeEntry₀ (unipotentOf
    q) := have : E (c q.1) = _ := E.4 _; by simp_all [E, g, unipotentOf, mul_apply, sub_eq_add_neg]
  have hc : Continuous c := E.symm.1.continuous_of_finiteDimensional.comp (by fun_prop)
  by refine ⟨by simp +contextual [mem_besselU0_iff_unipotentOf, ← e, -Prod.ext_iff], .map_of_comp
    (.congr ((HasGaussianIntegral.measurePreserving E fun q ↦ by
    convert t (‖uncurry (g q) ·‖ ^ 2) (q.2ᵀ · · ^ 2) _ <;> simp [E, g, mul_apply, uncurry,
      skewOfReal, div_pow, RCLike.norm_sq_eq_def]; grind).comp (.skew_product (.id _) ?_ (.of_forall
    (map_add_right_eq_self _ <| c · |>.2)))) ?_ (.of_forall e)) ?_ ?_⟩ <;> first
      | exact Continuous.measurable (by fun_prop) | fun_prop

instance isUnimodularHaar_besselHaar₀ : IsUnimodularHaar 𝔰.besselHaar₀ :=
  .of_freeEntries mem_besselU0_iff_apply (by simp; lia) besselS_le_normalizer_besselU0 inf_le_left
  besselHaar₀_spec.1 besselHaar₀_spec.2

/-- The free-entry coordinates for `IsFreeEntry` are injective on the unipotent group U
(`besselU`) of G₁. -/
lemma injective_freeEntries_besselU : Injective fun u : (𝔰.middleGram 1).besselU ↦
  freeEntries IsFreeEntry u.1.1.1 := fun u v h ↦ by
  have ⟨T, _, t⟩ := exists_measurePreserving_freeEntries (p :=
    IsFreeEntry) mem_besselU (by simp; lia) v⁻¹.2; apply_fun T at h
  simp_all [← t]; simpa [mul_inv_eq_one] using
    @besselHaar₀_spec.1 ⟨_, mem_besselU0_iff_apply.2 fun i j c ↦ by_cases
    (mem_besselU.1 (u * v⁻¹).2 i j) (by revert i j; simp_all; lia)⟩ 1 (by aesop)

/-- For T ≥ 8r, r the rank, there are a compact B ⊂ {‖y‖ ≤ T^{20(ϱ+1)}} in G₁ and a measurable
Ω ⊂ 𝖴⁰ with 0 < ν(Ω) < ∞, Ω·{‖y‖ ≤ T} ⊂ B, and ν{u : uy ∈ B} ≤ T·ν(Ω) for all y;
ν = `Shape.besselHaar₀`. -/
lemma exists_tube (hM : 8 * 𝔰.r ≤ T) : ∃ B Ω, IsCompact B ∧ MeasurableSet Ω ∧ 𝔰.besselHaar₀ Ω ≠ 0 ∧
  𝔰.besselHaar₀ Ω ≠ ∞ ∧ (∀ y ∈ B, ‖y.1.1‖ ≤ (T ^ 𝔰.n) ^ 20) ∧
  (∀ u ∈ Ω, ∀ y, ‖y.1.1‖ ≤ T → u.1 * y ∈ B) ∧ ∀ y, ∫⁻ u, B.indicator 1 (u * y) ∂𝔰.besselHaar₀ ≤
  .ofReal T * 𝔰.besselHaar₀ Ω := have m : 8 ≤ T := by simp at hM; bound
  (@exists_dilation 𝔰 (T ^ 6) (by bound)).elim fun d ⟨hd, _, e⟩ ↦ by
    let N := 5 * (2 * 𝔰.r ^ 2)
    have r : N + 2 ≤ T ^ 2 := by push_cast [N]; nlinarith
    let j := (MulAut.conj d⁻¹).toMonoidHom.domRestrict besselU0
    let A (i : ℕ) := {u | ‖(j u).1.1‖ ≤ i + 2}
    obtain ⟨i, n, h⟩ := by simpa using (mul_right_mono (a := .ofReal T).seq_pos_lt_seq_of_le_of_lt
      (n := N) (x := (.ofReal T ^ · * 𝔰.besselHaar₀ (A 0))) (y :=
      (𝔰.besselHaar₀ <| A ·)) (by bound) (by simp) (by simp [pow_succ']) · |>.not_ge
      (.trans (by simpa [← pow_mul, -card_sum, m.trans'] using
      measure_ball_le_covering _ j 1 le_rfl (by bound) (by grw [r]; nlinarith : _ ≤ T ^ 5)) (by
      gcongr; exact fun u h ↦ (norm_le_insert' _ 1).trans (by simp at h ⊢; grind))))
    grw [← n] at r; have k : IsCompact (A i) := ((isCompact_U_norm_le _).preimage_smul
      (ConjAct.toConjAct d⁻¹)).preimage_val (isClosed_of_entries_eq_one mem_besselU0_iff_apply)
    refine ⟨_, _, k.smul_set (isCompact_U_norm_le T), k.measurableSet,
      measure_sublevel_ne_zero _ (by simp; bound) (by
      simp [j]; fun_prop), k.measure_ne_top, fun y ⟨u, h, z, c, f⟩ ↦ f ▸ (norm_mul_le ..).trans (by
      grw [(by simp [j] : u.1.1.1 = d * j u * d⁻¹), norm_mul₃_le, U.norm_inv, hd, hd, h.out, r,
        c.out]
      ring_nf; bound), fun u a ↦ (⟨u, a, ·, ·, rfl⟩), fun y ↦ (lintegral_indicator_one_le _).trans
      (h.trans' (measure_le_of_div_mem fun u ⟨s, _, z, c, f⟩ ↦
      ⟨s⁻¹ * u, fun v ⟨q, h, w, k, l⟩ ↦ le_trans
      (by simp [j, division_def]) ((norm_mul_le_of_le h (e _ (q⁻¹ * v * u⁻¹ * s).2.1)).trans ?_)⟩))⟩
    grw [(le_div_iff₀' _).2 hM, (_ : Units.val _ = w.1.1 * z⁻¹), norm_mul_le, U.norm_inv,
      c.out, k.out] <;> simp [field, eq_inv_mul_of_mul_eq f, eq_inv_mul_of_mul_eq l]
    nlinarith

/-- The free entries (`freeEntries` at `IsFreeEntry`) carry the measure `Shape.besselHaar` on 𝖴 to
Lebesgue measure.

Known result: Bessel subgroup of a real unitary group: coordinates, Haar measure, Bessel
functions. -/
lemma measurePreserving_freeEntries_besselHaar : MeasurePreserving (freeEntries IsFreeEntry ·.1.1.1)
  𝔰.besselHaar := by refine (.map_of_comp (((((volume_measurePreserving_piCongrLeft _
  (.ofBijective (Subtype.coind ((fun y ↦ (y.1.1.castPred (by grind), 𝔰.besselFrame y.1.2)) ⊕ᵥ
  (↑)) ?_) ?_)).symm.trans (volume_measurePreserving_sumPiEquivProdPi _)).prod (.id _)).trans (e :=
  .prodCongr _ (.refl _)) volume_preserving_prodAssoc).comp_left_iff.1 (.congr (.skew_product
  (.id _) ?_ (.of_forall fun x ↦ (exists_measurePreserving_freeEntries mem_besselU0_iff_apply
  (by simp; lia) (liftUnitri_mem_besselU x)).elim fun _ t ↦ congr(map $(funext (t.2 _ ·.2)) _).trans
  (t.1.comp besselHaar₀_spec.2).2)) ?_ (.of_forall fun x ↦ Prod.ext (funext fun y ↦
  .trans ?_ (congr($(frameMatrix_mul (liftUnitri_mem_besselU x.1)) y.1.1 y.1.2).symm.trans (by
  erw [frameMatrix, submatrix_apply, besselFrame_castSucc ⟨_, _⟩]; rfl))) rfl))) ?_ ?_) <;> first
  | fun_prop | simp [Bijective, Surjective, Subtype.coind, mem_besselU0_iff.1, unitriMatrix]; lia

instance : IsUnimodularHaar 𝔰.besselHaar :=
  .of_freeEntries mem_besselU (by simp; lia) besselS_le_normalizer_besselU le_rfl
  injective_freeEntries_besselU measurePreserving_freeEntries_besselHaar

instance sigmaFinite_G₁ {𝔰 : Shape} {μ : MeasureTheory.Measure 𝔰.G₁} [μ.IsHaarMeasure] :
    MeasureTheory.SigmaFinite μ := inferInstance
