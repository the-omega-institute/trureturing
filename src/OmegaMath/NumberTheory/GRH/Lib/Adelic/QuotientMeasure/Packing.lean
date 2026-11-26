import OmegaMath.NumberTheory.GRH.Lib.General.Measure.SubgroupIntegral
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of real and complex analysis (textbook or folklore).

Part of: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity (known
result; see Lib.Adelic.QuotientMeasure.Unimodular).

This file: Quotient integral via weights: independence of the weight and Weil's unfolding
formula. -/

open Classical Filter MeasureTheory Metric Module ProbabilityTheory Real MeasureTheory.Measure

to_additive_name_hint Quot AddQuot

variable {H X W Y} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace W] [MeasurableSpace Y]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [BorelSpace W] {F : X → Y} {f : X → W}

/-- Let ν on H have a cutoff on X, σ carry ρ to ν, and (z, l) ↦ σ(l)·T(z) carry m × ρ to μ, with
m, ρ s-finite, T measurable. For measurable H-invariant F, F under `orbitMeasure` ν μ and F∘T
under m are identically distributed. -/
@[to_additive identDistrib_addOrbitMeasure_of_unfold] lemma identDistrib_orbitMeasure_of_unfold
  [SMul H X] [MeasurableSMul₂ H X] {ν μ Z L} [MeasurableSpace Z] [MeasurableSpace L] {ρ} [SFinite ρ]
  [c : HasCutoff ν X] {σ : L → H} (s : MeasurePreserving σ ρ ν) {T m} [@SFinite Z _ m] (h :
  MeasurePreserving (fun p ↦ σ p.2 • T p.1) (m.prod ρ) μ) (hF : Measurable F) (hT :
  Measurable T) (hi : ∀ (h : H) x, F (h • x) = F x) : IdentDistrib F (F ∘ T) (orbitMeasure ν μ) m :=
  (fun ⟨b, _⟩ _ ↦ ⟨by fun_prop, by fun_prop, ext_of_lintegral
  _ (by simp +contextual (disch := fun_prop) [lintegral_map, lintegral_withDensity_eq_lintegral_mul,
  *, ← h.lintegral_comp, lintegral_mul_const, lintegral_prod, Function.comp_def,
  s.lintegral_comp (b.fun_comp (measurable_smul_const _))])⟩) (epsilon_spec c.1) s.1

variable [Group H] [MulAction H X] [MeasurableInv H] [MeasurableSMul₂ H X] {ν} [@SFinite H _ ν]
  {μ : Measure X} [SFinite μ] [SMulInvariantMeasure H X μ] {β} [IsInvInvariant ν] {S : Subgroup H}

@[to_additive] instance : MeasurableSMul₂ S X := ⟨.smul (by fun_prop) measurable_snd⟩

/-- Let a group H act measurably on X, ν an s-finite measure on H, μ an s-finite H-invariant
measure on X, β : X → [0,∞] measurable. Then (x,h) ↦ hx pushes (βμ) × ν forward to μ with
density x ↦ ∫ β(h⁻¹x) dν(h). -/
@[to_additive] lemma measurePreserving_smul_prod {ν : MeasureTheory.Measure H} [@SFinite H _ ν]
    {μ : Measure X} [SFinite μ] [SMulInvariantMeasure H X μ] {β : X → ENNReal} (m : Measurable β) :
    MeasurePreserving (fun p ↦ p.2 • p.1) ((μ.withDensity β).prod ν)
    (μ.withDensity fun x ↦ ∫⁻ h, β (h • x) ∂ν.inv) := ⟨by fun_prop,
  by ext; erw [map_apply, prod_apply_symm, withDensity_apply, lintegral_lintegral_swap,
       lintegral_map]; congr!
     rw [← (measurePreserving_smul ‹_› _).setLIntegral_comp_preimage, withDensity_apply]
     repeat measurability⟩

@[to_additive] lemma IsCutoff.measurePreserving :
    IsCutoff ν β → MeasurePreserving (fun p ↦ p.2 • p.1) ((μ.withDensity β).prod ν) μ
    | ⟨m, _⟩ => by convert measurePreserving_smul_prod m <;> simp_all

/-- Independence of the cutoff: for H acting measurably on X, ν inversion invariant on H, μ
H-invariant on X (both s-finite) and any cutoff β, an H-invariant measurable F has the same
distribution under βμ as under the quotient measure `orbitMeasure`. -/
lemma identDistrib_orbitMeasure (hβ : IsCutoff ν β) : Measurable F →
  (∀ (h : H) x, F (h • x) = F x) → IdentDistrib F F (orbitMeasure ν μ) (μ.withDensity β) :=
  (identDistrib_orbitMeasure_of_unfold (c := ⟨_, hβ⟩) (.id _) hβ.measurePreserving · measurable_id)

lemma IsCutoff.ae_lt_top : IsCutoff ν β → ∀ᵐ x ∂μ, β x < ⊤ | h@⟨_, _⟩ => by simp (disch :=
  measurability) [← h.measurePreserving.hasLaw.ae_iff, ae_prod_iff_ae_ae, MeasureTheory.ae_lt_top]

lemma IsCutoff.integral_orbitMeasure (h : IsCutoff ν β) (i : ∀ (h : H) y, f (h • y) = f y) (m :
  Measurable f := by fun_prop) : (orbitMeasure ν μ)[f] = ∫ y, (β y).toReal • f y ∂μ :=
  (identDistrib_orbitMeasure h m
  i).integral_eq.trans (integral_withDensity_eq_integral_toReal_smul h.1 h.ae_lt_top _)

variable {V} {I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {f : I → V} {m R A c : ℝ} (hm : 0 < m) [c : HasCutoff ν X]

/-- Unfolding: let H act measurably on X with a cutoff, ν s-finite and inversion invariant on H,
μ s-finite and H-invariant on X. Then (x, h) ↦ hx is measurable and carries βμ × ν to μ,
where βμ is `orbitMeasure` for the chosen cutoff β.

Known result: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity. -/
@[to_additive measurePreserving_addOrbitMeasure] lemma measurePreserving_orbitMeasure :
  MeasurePreserving (fun p ↦ p.2 • p.1)
  ((orbitMeasure ν μ).prod ν) μ := (epsilon_spec c.1).measurePreserving

/-- Let the action of H on X have a cutoff and let the invariant measure μ be positive on
nonempty open sets. An H-stable property that holds almost everywhere for the quotient
measure `orbitMeasure` holds on a dense subset of X. -/
lemma dense_of_ae_orbitMeasure [TopologicalSpace X] [BorelSpace X] [μ.IsOpenPosMeasure] {p : X → _}
    (i : ∀ (h : H) x, p x → p (h • x)) (e : ∀ᵐ x ∂orbitMeasure ν μ, p x) : Dense {x | p x} :=
  .of_closure
  (dense_of_ae ((measurePreserving_orbitMeasure.hasLaw.ae_iff measurableSet_closure.mem).1
  ((quasiMeasurePreserving_fst.ae e).mono (by grind [subset_closure]))))

/-- Unfolding: let H act measurably on X preserving the s-finite μ, with ν an s-finite
inversion-invariant measure on H admitting a cutoff. For measurable f : X → [0,∞],
integrating x ↦ ∫_H f(hx) dν over H\X gives ∫_X f dμ. -/
@[to_additive lintegral_addOrbitMeasure_lintegral] lemma lintegral_orbitMeasure_lintegral {f} :
    Measurable f → ∫⁻ x, ∫⁻ h, f (h • x) ∂ν ∂orbitMeasure ν μ = ∫⁻ x, f x ∂μ :=
    (.trans (lintegral_lintegral (by fun_prop)) <| measurePreserving_orbitMeasure.lintegral_comp ·)

/-- Let u ≥ 1 be measurable, ν{u ≤ R} ≤ (K R^e)^d · V for R ≥ 1, ed < A, V finite, K ≥ 0 and A ≤
c(A − ed). Then u^(−A) is integrable and ∫ u^(−A) dν ≤ K^d c V. -/
lemma integral_rpow_neg_le_of_layers {K} (A : ℝ) {e d : ℕ} {S} {_ : MeasurableSpace S} {ν :
  Measure S} {u : S → ℝ} {V} (h : ∀ s, 1 ≤ u s) (H : ∀ R ≥ 1, ν {s | u s ≤ R} ≤ .ofReal
  ((K * R ^ e) ^ d) * V) c (hV : V ≠ ⊤) (m : Measurable u := by fun_prop) (hK : 0 ≤ K := by bound)
  (hA : e * d < A := by norm_cast; lia) (hc : A ≤ c * (A - e * d) := by norm_cast; lia) :
  Integrable (u · ^ (-A)) ν ∧ ∫ s, u s ^ (-A) ∂ν ≤ K ^ d * c * V.toReal := by
  have : 0 ≤ c := by nlinarith
  suffices : lintegral .. ≤ .ofReal c * ∫⁻ _, .ofReal (1 ^ (A - e * d)) ∂(.ofReal K ^ d * V) •
    .dirac ()
  grw [Integrable, integral_eq_lintegral_of_nonneg_ae, hasFiniteIntegral_iff_ofReal, this]
  case' this => simp_rw [rpow_neg_eq_inv_rpow]
                repeat rw [lintegral_rpow_eq_lintegral_meas_le_mul]
                nth_grw 1 [hc, ENNReal.ofReal_mul, mul_assoc, setLIntegral_mono' _ fun t o ↦ ?_]
  all_goals simp [*, EventuallyLE, (h _).trans', m.aemeasurable, hA.trans_le', mul_nonneg, field,
    rpow_nonneg, (m.pow_const (-A)).aestronglyMeasurable] <;> try finiteness
  by_cases t ≤ 1 <;> simp_all [le_inv_comm₀ o.out, (h _).trans_lt', ← one_le_inv₀, mt (h _).trans]
  grw [H] <;> simp (disch := bound) [*, rpow_sub, rpow_mul, mul_pow, division_def]
  ac_nf

/-- Packing bound: in a finite-dimensional real normed space V, if the points f(i), i in S, have
pairwise distances at least m > 0 and norms at most R, with R ≥ 0, then S has at most (1 +
2R/m)^{dim V} elements. -/
lemma encard_le_of_separated (hm : 0 < m) (hR : 0 ≤ R) {S} (hf : Set.Pairwise S (m ≤ ‖f · - f ·‖))
    (hs : ∀ i ∈ S, ‖f i‖ ≤ R) : S.encard ≤ ENNReal.ofReal ((1 + 2 * R / m) ^ finrank ℝ V) := by
  borelize V
  grw [← ENNReal.mul_le_mul_iff_left, ← addHaar.addHaar_ball_mul_of_pos 0 _ (m / 2),
    ← Set.iUnion_subset fun i ↦ ball_subset (ε₁ := m / 2) _,
    ← tsum_meas_le_meas_iUnion_of_disjoint _ (by measurability) (hf.subtype.mono _)]
  any_goals simp [addHaar_ball_center, field]
  repeat grind [measure_ball_pos, measure_ball_ne_top, ball_disjoint_ball, dist_eq_norm]

/-- Let points f_i of a real normed space of dimension d have mutual distances at least m > 0,
with ‖f_i‖ ≤ R u_i, u_i ≥ 1, R ≥ 0. If A > d and A ≤ c(A − d), then ∑ u_i^(−A) converges and
is ≤ (1 + 2R/m)^d c. -/
lemma tsum_le_of_separated {c : ℝ} (hm : 0 < m) (hR : 0 ≤ R) (hf : Pairwise (m ≤ ‖f · - f ·‖)) {u :
    I → _} (h1 : ∀ i, 1 ≤ u i) (hu : ∀ i, ‖f i‖ ≤ R * u i) (hA : finrank ℝ V < A) (hc : A ≤ c * (A -
    finrank ℝ V)) : Summable (u · ^ (-A)) ∧ ∑' i, u i ^ (-A) ≤ (1 + 2 * R / m) ^ finrank ℝ V * c :=
    .elim (by simp [count, integral_sum_measure ‹_›, integrable_count_iff.1 · |>.of_norm]; tauto)
    (integral_rpow_neg_le_of_layers A (e := 1) (ν := @count I ⊤) (V := 1) h1 (by
    simp_intro .. [count_apply]; grw [encard_le_of_separated hm _ (by tauto) (by grw [hu]; bound)]
    gcongr; grind; bound) c nofun)

include hm in
/-- Let points f_i of a real normed space of finite dimension d have norms and mutual distances
at least m > 0. For an integer n ≥ d + 2, ∑ ‖f_i‖^(−n) converges and is at most (5/m)^n. -/
lemma tsum_inv_pow_le_of_separated (hf : Pairwise (m ≤ ‖f · - f ·‖)) (h0 : ∀ i, m ≤ ‖f i‖) {n}
    (hn : finrank ℝ V + 2 ≤ n) : Summable (‖f ·‖⁻¹ ^ n) ∧ ∑' i, ‖f i‖⁻¹ ^ n ≤ (5 / m) ^ n := by
  have := tsum_le_of_separated hm hm.le hf ((one_le_inv_mul₀ hm).2 <| h0 ·) (by simp [field])
    (c := 1 + n * 2⁻¹) (A := n) (mod_cast by lia) (by rify at *; nlinarith)
  simp_all [mul_pow, tsum_mul_right, summable_mul_right_iff, ne_of_gt]
  grw [div_pow, le_div_iff₀, this.2, one_add_mul_le_pow, le_of_add_le_left hn, ← mul_pow] <;> bound
