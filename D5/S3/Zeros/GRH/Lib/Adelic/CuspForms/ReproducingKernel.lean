/- GID: D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/ReproducingKernel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/CuspForms/ReproducingKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.CuspForms.ReproducingKernel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/CuspForms/ReproducingKernel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.CuspStep
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

Part of: Comparison of simple trace formulas for unitary groups that differ only at real places
(known result; see Lib.LocalGL.TraceFormula.TraceComparison).

This file: Forms reproduced by a cusp kernel decay rapidly; finite dimension at fixed level. A
bounded Poincaré series projected term by term is a form of given level. Poincaré series of the
idempotent kernel is a form of level K. -/

open Classical ENNReal Ideal MeasureTheory Set

attribute [local simp] NumberField.rootDiscr Space.firstMinimum_pos abs_of_nonneg cuspConst le_of_lt

variable {E : Type} {n s} [Field E] [CMType E] [Fintype n] {V : Space E n s} {e :
  GInf E s → ℂ} {F B} (he : IsCuspKernel B e) (K : OpenSubgroup (Gf E n))

/-- Uniform decay: for a cusp kernel e, an open subgroup K of G_f and natural A there is R such
that every form F of type e and level K with |F| ≤ c satisfies |F(g)|·ht(g)^A ≤ cR for all
g. -/
lemma Space.exists_norm_mul_height_pow_le {B : ℕ} (he : IsCuspKernel B e) (K :
  OpenSubgroup (Gf E n)) A : ∃ R, ∀ {F c}, V.IsForm e F → HasLevel F K → (∀ g, ‖F g‖ ≤ c) →
  ∀ g, ‖F g‖ * V.height g ^ A ≤ c * R := by
  obtain ⟨⟨α, H⟩, M, hM, _⟩ := he.3, exists_principalLevel_subset K.mem_nhds_one
  have ⟨D, d, hD⟩ :=
    V.exists_height_le_mul (.prod ((isCompact_closedBall 1 1).mul α.2).inv isCompact_Kf)
  have ⟨δ, _, W⟩ := Metric.nhds_basis_closedBall_inv_nat_succ.mem_iff.1
    (eventually_norm_realConv_sub_le K α.integrable (ε := |D|⁻¹ ^ A / 2) (by positivity)).curry_nhds
  refine ⟨_, @fun F c y k l t ↦ .trans ?_ (le_of_halving (f :=
    fun g ↦ ‖F g‖ * (V.height g ⊓ V.height t) ^ A) (by grw [inf_le_right, l ·] <;> simp) ?_
    (fun C _ b g ↦ (lt_or_ge ..).imp ((le_div_iff₀ ?P).1 <| y.norm_le_of_firstMinimum_lt he
    (absNorm_mem _) hM (by tauto) (by bound) ?_ · fun u hu ↦ (by simpa [H, y.3 he.1.2]
    using (realConv_realConv y.isBoundedMeasurable α.integrable he.1.2 1)) ▸ ((W hu).self_of_nhds _
    y.isBoundedMeasurable k g fun x i ↦ (le_div_iff₀ ?P).2 (by grw [← one_mul (V.height t), ← d,
    hD 1 _ g ⟨(i.ne_or_ne 0).elim (⟨u, _, _, subset_closure ·, _⟩) (⟨1, _, _, subset_closure ·, _⟩),
    _⟩, ← mul_inf₀, mul_pow, mul_left_comm, b] <;> simp [d.trans', hu.trans, field])).trans ?_) (by
    grw [inf_le_left, height, ← ·, l] <;> simp [field])) t)⟩ <;> simp [field, *, (l 1).trans']

include he

/-- If e is a cusp kernel on G_∞, every form F of type e for V decays rapidly: |F| times any
power of the height is bounded.

Known result: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular
forms. -/
lemma Space.IsForm.mem_rapidFunctions (h : V.IsForm e F) : F ∈ V.rapidFunctions :=
    ⟨h.1, (⟨_, exists_norm_mul_height_pow_le he _ · |>.choose_spec h h.exists_level.choose_spec
  h.2.choose_spec⟩)⟩

/-- If e is a cusp kernel on G_∞ and K is an open subgroup of G_f, the forms of type e fixed by
K make up a finite-dimensional complex vector space. -/
lemma Space.finite_levelSpace : Module.Finite ℂ (levelSpace (V.formRep e) K) :=
  (exists_norm_mul_height_pow_le he K 1).elim fun R d ↦
  (V.mahler_criterion (2 * R)).elim fun C ⟨c, hC⟩ ↦ (compact_covered_by_mul_left_translates c ⟨1,
  mem_interior_iff_mem_nhds.2 (eventually_norm_realConv_sub_le K
  he.1.2 one_half_pos)⟩).elim fun t ht ↦ .of_injective (.domRestrict (.domRestrict (.funLeft _ _
  (·.1⁻¹ : t → _)) _) _) (.of_ker _ fun ⟨⟨F, y⟩, k⟩ h ↦ have k := mem_levelSpace_formRep_iff.1 k
  by congr; simpa [funext_iff] using le_of_halving y.2.choose_spec le_rfl fun M _ b g ↦
    or_not.imp_right fun _ ↦ have ⟨_, _, m⟩ := hC g (by nlinarith [d y k b g, V.height_pos g])
    have ⟨a, ha, m⟩ := mem_iUnion₂.1 (ht m)
    by simpa [(congr($h ⟨a, ha⟩) : F _ = 0), y.rat_mul, *, y.3 he.1.2, inv_mul_eq_div] using
        m M y.isBoundedMeasurable k a⁻¹)

/-- Let e be a cusp kernel on G_∞. If F is automorphic and x ↦ e(x)F(gx) is integrable on G_∞
for every g, then R(e)F is a form of type e; in particular it is bounded. -/
lemma Space.isForm_realConv : V.IsAutomorphic F → (∀ g, Integrable fun x ↦ e x * F (g * (x, 1))) →
    V.IsForm e (realConv e F) | ⟨c, r, K, l⟩, ht => have := finite_levelSpace he
  have m g t : MeasurableSet {x | ‖F (g * (x, 1))‖ ≤ t} := by measurability
  (by refine ((Submodule.subtype _ ∘ₗ (levelSpace (V.formRep e)
    K).subtype).range.closed_of_finiteDimensional.mem_of_tendsto (tendsto_pi_nhds.2 (.congr ?_ <|
    AECover.integral_tendsto_of_countably_generated (l := .atTop) ⟨.of_forall (by aesop), m ·⟩ (ht
    _))) (.of_forall fun t ↦ exists_form_eq_realConv K ⟨c.stronglyMeasurable.indicator
    (c.norm.measurable (measurableSet_Iic (a := t))), |t|, ?_⟩ ?_ ?_ he.1)).elim (·.1.2 |> ·.subst)
    <;> simp +contextual [realConv, indicator, *, apply_ite, ← integral_indicator]; grind)

omit he

/-- Poincaré series: let e be a kernel on G_∞, c right invariant under an open K ⊆ G_f, and ∑_Γ
c(γg) = ∑_i W_i(g) with countably many measurable W_i and ∑|W_i| bounded. Then ∑ R(e)W_i is
a form of type e. -/
lemma Space.exists_form_eq_tsum {s} {V : Space E n s} {e} (he : IsIdempotentKernel e) (K :
  OpenSubgroup _) {ι} [Countable ι] {W : ι → _} (hc : ∀ i, Measurable (W i)) {c} (hK : HasLevel c K)
  (hP : ∀ g, ∑' γ : V.Γ, c (↑γ * g) = ∑' i, W i g) {M} (hM : M ≠ ⊤) (h : ∀ g, ∑' i, ‖W i g‖ₑ ≤ M) :
  ∃ y : levelSpace (V.formRep e) K, y.1.1 = fun g ↦ ∑' i, realConv e (W i) g := by
  convert exists_form_eq_realConv K ⟨by fun_prop, _,
    (toReal_mono hM <| enorm_tsum_le_tsum_enorm.trans <|
    h ·)⟩ (fun γ m g ↦ by rw [← hP, ← (Equiv.mulRight ⟨γ, m⟩⁻¹).tsum_eq]; simp [hP])
    (by simp +contextual [← hP, ← mul_assoc, hK]) he
  simp [realConv, ← tsum_mul_left]; have := he.1.measurable
  rw [(hasSum_integral_of_lintegral _).tsum_eq]
  simp; grw [h, lintegral_mul_const'] <;> finiteness [he.2.2]

/-- Poincaré series: for a cusp kernel e, x ∈ G and a level K (`IsLevel`), there is a
K-fixed form k of type e on V with conj k(g) = ∑_{γ∈Γ} e((xγg)_∞)·1_K((xγg)_f) for all g ∈
G. -/
lemma Space.exists_kernel_form {s} (V : Space E n s) {e B} (he : IsCuspKernel B e) x (K : Subgroup
  (Gf E n)) [l : IsLevel K] : ∃ k : levelSpace (V.formRep e) K, ∀ g, starRingEnd ℂ (k.1 g) = ∑' γ :
  V.Γ, e (x * γ * g).1 * indicator K 1 (x * γ * g).2 := have ⟨α, H⟩ := he.exists_bump
  have s := (α.2.prod l.isCompact).preimage_smul x
  (exists_form_eq_tsum he.1 ⟨K, l.2⟩ (c := indicator _ (star α.toBoundedContinuousFunction <| x.1 *
    ·.1)) (by fun_prop (disch := exact s.measurableSet)) (fun _ k ↦ by simp [indicator, ← mul_assoc,
    K.mul_mem_cancel_right k]) (congrFun rfl) (mul_ne_top coe_ne_top
    (ProperSMul.isCompact_setOfPred_inter_nonempty s s).measure_ne_top) fun g ↦ by
    grw [← lintegral_count, ← lintegral_mul_right_eq_self, ← lintegral_indicator_const_le]
    gcongr; delta indicator; split
    grw [enorm_eq_nnnorm, ite_eq_left ⟨_, ⟨_, epsilon_spec_aux ⟨1⟩ (· • g ∈ _) ⟨_, ‹_›⟩,
      smul_smul ..⟩, ‹_›⟩, BoundedContinuousFunction.nnnorm_coe_le_nnnorm]
    simp).imp fun k h g ↦ by
    rw [h, Complex.conj_tsum]; congr with γ
    rw [← H, ← integral_mul_const, ← integral_mul_left_eq_self _ (x * γ * g).1]
    simp [realConv, indicator, mul_assoc, he.apply_inv, apply_ite, ← integral_conj]
    grind -ac [image_eq_zero_of_notMem_tsupport]
