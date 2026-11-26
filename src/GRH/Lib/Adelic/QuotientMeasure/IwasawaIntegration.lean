import GRH.Lib.Adelic.QuotientMeasure.Unimodular
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity (known
result; see Lib.Adelic.QuotientMeasure.Unimodular).

This file: Iwasawa integration formula; quotient integral of N-invariant functions in coordinates n
m k. -/

open MeasureTheory Measure ENNReal NeZero ProbabilityTheory Function
variable {G M} [Group G] [Group M] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] (w)
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace M] [PolishSpace M]
  [IsTopologicalGroup M] [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M] (μ : Measure G)
  [IsHaarMeasure μ] [IsMulRightInvariant μ] (ν : Measure M) [IsHaarMeasure ν] {N K Γ : Subgroup G}
  [IsMulRightInvariant ν] [CompactSpace K] (κ : Measure K) [IsHaarMeasure κ] {lam : Measure N}
  [IsHaarMeasure lam] (i : M →* G) (hN : @IsClosed G _ N) (hw : Continuous w) (h₀ : ∀ m, 0 < w m)
  (hi : Continuous i) (H : ∀ g, ∃ᵉ (n : N) (m) (k : K), g = n * i m * k)
  (L : ∀ m f, Measurable f → ∫⁻ n, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n, f n ∂lam)
include hN hw h₀ hi H L

omit hw in
/-- Iwasawa integration formula. Let G = N·i(M)·K with G, M, N unimodular, N closed, K compact,
conjugation by i(m) scaling integrals over N by w(m) > 0. Then ∫∫∫ f(i(m)nk) dn dm dk = d∫f
for some d in [0, ∞] and all measurable f ≥ 0. -/
lemma lintegral_iwasawa [IsMulRightInvariant lam] : ∃ d, ∀ f, Measurable f →
    ∫⁻ k, ∫⁻ m, ∫⁻ n, f (i m * n * k) ∂lam ∂ν ∂κ = d * ∫⁻ g, f g ∂μ := by
  have ⟨_, β, _, b⟩ : SFinite ν ∧ HasCutoff μ G := ⟨inferInstance, inferInstance⟩
  choose n m k t using H
  let J (f : G → _) y := ∫⁻ h, f (i h.2.1 * h.2.2 * y * h.1⁻¹) ∂κ.prod (ν.prod lam)
  have e y f (_ : Measurable f) : .ofReal (w (m y)) * J f y = J f 1 := by
    nth_rw 2 [t y]; unfold J; rw [← lintegral_mul_right_eq_self _ (k y, (m y, n y)⁻¹)]
    simp (disch := fun_prop) [lintegral_prod, ← mul_assoc, ← lintegral_const_mul' _ _ ofReal_ne_top,
      ↓← fun a b c ↦ L (m y) (f <| a * · * b * c)]
  have ⟨g, _, r⟩ : ∃ g, Measurable g ∧ ∀ y f, Measurable f → g y * J f y = β y * J f 1 := by_contra
    fun h ↦ h ⟨β, ‹_›, fun y f u ↦ congrArg _ (by_contra fun n ↦ h ⟨β * (J f 1 / J f ·), by
    fun_prop, fun x φ v ↦ by rw [Pi.mul_apply, ← e x f u, ENNReal.mul_div_cancel_right, mul_assoc,
      e x φ v] <;> exact n ∘ (by simpa [← e x f u, ·, (h₀ _).not_ge, mul_eq_top] using e y f u)⟩)⟩
  use ∫⁻ h, g ((i h.2.1 * h.2.2)⁻¹ * h.1) ∂κ.prod (ν.prod lam), fun f u ↦ ?_
  rw [← lintegral_inv_eq_self]
  trans ∫⁻ y, g y * J f y ∂μ
  simp (disch := fun_prop) [↓r, lintegral_mul_const, J, lintegral_prod, by simpa using b 1]
  simp (disch := fun_prop) [J, ← lintegral_const_mul]
  rw [lintegral_lintegral_swap, ← funext fun h ↦ (lintegral_mul_right_eq_self _
    h.1).trans (lintegral_mul_left_eq_self _ (i h.2.1 * h.2.2)⁻¹), lintegral_lintegral_swap]
  congr with x; any_goals fun_prop
  rw [t x, eq_comm, ← lintegral_mul_left_eq_self _ (k x, (m x)⁻¹, 1)]
  simp (disch := fun_prop) [mul_assoc, lintegral_prod, lintegral_mul_const, fun a b ↦ by
    simpa [mul_assoc] using L a (g <| (i a)⁻¹ * ·⁻¹ * b), ← fun a b ↦
    lintegral_mul_left_eq_self (μ := lam) (fun y ↦ g (a * (y.1⁻¹ * (n x * b)))) (n x)]

/-- In Iwasawa coordinates G = N i(M) K, let Γ be discrete, contain all i(δ_d), lie in ⋃N·i(δ_d)⁻¹,
with Γ∩N cocompact in N. For F invariant under N, Γ: ∫F over the quotient is c∫w(m)F(i(m)k), if
convergent, m over a measure unfolding ν along δ; c ≠ 0. -/
lemma integral_orbitMeasure_iwasawa (j : ∀ a, i a ∈ N → a = 1) {D} [Countable D] {δ : D → M} (hd :
  Injective δ) α [SFinite α] (hα : ∀ f, Measurable f → ∫⁻ m, f m ∂ν = ∫⁻ m, ∑' d, f (δ d * m) ∂α)
  (hΔ : ∀ d, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d, g * i (δ d) ∈ N) [DiscreteTopology Γ]
  (hv : (Γ.subgroupOf N).Cocpt) : ∃ c ≠ (0 : ℝ), ∀ F : G → ℂ, Measurable F → N.FixesLeft F →
  Γ.FixesLeft F → let Θ (p : M × K) := w p.1 * F (i p.1 * p.2)
  Integrable Θ (α.prod κ) → Integrable F (Γ.qms μ) ∧ (Γ.qms μ)[F] = c * integral (α.prod κ) Θ := by
  set S := Γ.subgroupOf N
  obtain ⟨v, m⟩ := isFiniteMeasure_quotMeasure_of_cocompact lam hv,
    hw.fst' (Y := K).measurable.ennreal_ofReal
  have ⟨c, I⟩ := have :=
      isMulRightInvariant_of_finite_covolume v; lintegral_iwasawa w μ ν κ i hN h₀ hi H L
  use update id 0 1 (c⁻¹ * S.qms lam ⊤).toReal, by grind, fun F hF F1 _ _ ↦
    have h := (identDistrib_orbitMeasure_of_unfold (μ := c • μ) (.id (@count Γ _)) ⟨by fun_prop,
      ext_of_lintegral _ fun f _ ↦ ?_⟩ ?_ ?_ (by bound)).trans (.trans (.of_ae_eq ?_ (.of_forall
      (F1 _ ·.2.2 _))) (.comp (u := fun p ↦ F (i p.1 * p.2)) (HasLaw.identDistrib ⟨?_, map_fst_prod⟩
      .id) ?_)); fun a e t ↦ by by_cases c = ∞ <;> simp_all [Integrable, -withDensity_apply,
      HasFiniteIntegral, lt_top_iff_ne_top, mul_eq_top, le_of_lt, mul_assoc, ne, toReal_eq_zero_iff,
      hF.aestronglyMeasurable, integral_withDensity_eq_integral_toReal_smul, left_ne_zero_of_mul (mt
      (I 1 measurable_one).trans (by simp [ne]))] (h.integrable_iff.2 (.smul_measure
    ((integrable_withDensity_iff_integrable_smul' m (by simp)).2 (by simpa [*, le_of_lt])) v.1.ne))
    h.symm.integral_eq (enorm_integral_le_lintegral_enorm (μ := Γ.qms μ) F)
  simp (disch := fun_prop) [lintegral_prod, lintegral_map, ← I]
  rw [lintegral_withDensity_eq_lintegral_mul, lintegral_prod_symm, funext fun _ ↦ hα ..]
  congr! with k m; any_goals fun_prop
  simp (disch := fun_prop) [fun a ↦ by simpa [mul_assoc] using L m (f <| a * · * i m * k),
    Subgroup.smul_def, mul_assoc,
    ← (Equiv.ofBijective (fun p : D × S ↦ (⟨_, hΔ p.1⟩ * ⟨_, p.2.2⟩ : Γ)) ⟨fun (_, _) (_, _) h ↦ by
    simpa [hd (inv_mul_eq_one.1 (j _ (by simpa [QuotientGroup.eq] using congr(($h : G ⧸ N)))))]
      using h, fun g ↦ (hΓ _ g⁻¹.2).elim fun d h ↦ ⟨(d, ⟨⟨_, h⟩, mul_mem g⁻¹.2 (hΔ d)⟩⁻¹),
    by simp⟩⟩).tsum_eq, lintegral_tsum, ← lintegral_orbitMeasure_lintegral (ν := @count S _)]
