import OmegaMath.NumberTheory.GRH.Lib.Adelic.QuotientMeasure.IwasawaIntegration
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity (known
result; see Lib.Adelic.QuotientMeasure.Unimodular).

This file: Unfolding quotient integrals in stages; pushing quotient measures along surjections.
Unfolding a sum over an orbit or block to the stabiliser quotient. Quotient integral vanishes when
averaging eigenvalue differs from modulus, or nontrivial phase. Continuous invariant functions for
cocompact subgroups are integrable; cocompactness of products. -/

open Classical ENNReal Function MeasureTheory MulAction ProbabilityTheory Topology
  MeasureTheory.Measure

variable {G H V} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Γ : Subgroup G} [DiscreteTopology Γ] (Λ : Subgroup H)
  [DiscreteTopology Λ] (μ : Measure G) [IsHaarMeasure μ] (ν : Measure H) [IsHaarMeasure ν]

section

attribute [local simp ←] map_mul mul_assoc

/-- Let π : H → G be a continuous surjective homomorphism of locally compact groups with
bi-invariant Haar measures, Λ ⊂ H, Γ ⊂ G discrete, π(Λ) ⊂ Γ. Some real c gives ∫_{Λ\H} F∘π =
c ∫_{Γ\G} F for all measurable left Γ-invariant F. -/
lemma exists_integral_quotMeasure_push [μ.IsMulRightInvariant] [ν.IsMulRightInvariant] {π : H →* G}
    (hπ : Continuous π) (hs : Surjective π) (hΛ : Λ ≤ Γ.comap π) : ∃ c :
    ℝ, ∀ F, Measurable F → Γ.FixesLeft F → ∫ r, F (π r) ∂Λ.qms ν = (c • (Γ.qms μ)[F] : V) :=
    (exists_eq_smul_haar μ ⟨hs.forall.2 fun a ↦ ext_of_lintegral _ fun f _ ↦ by
    simp (disch := fun_prop) [lintegral_map, lintegral_prod, subgroup_smul_def]
    exact .trans (by grind) (identDistrib_orbitMeasure_mul_right a fun ⟨δ, h⟩ r ↦ .trans
      (by simp [map_mul]) (Equiv.tsum_eq (.mulRight ⟨_, hΛ h⟩) _)).lintegral_eq⟩).imp'
  (·.toReal) fun _ e F hF _ ↦ (identDistrib_orbitMeasure_of_unfold (.id (@count Γ _)) ⟨by fun_prop,
  e⟩ hF (by fun_prop) (by simpa)).integral_eq.symm.trans (by simp)

/-- Unfolding in stages. Let i : H → G be injective, Λ and Γ = i(Λ) discrete, ν Haar on H, m
s-finite, (z,h) ↦ i(h)T(z) carry m × ν to μ. For measurable Γ-invariant F integrable on Γ\G,
z ↦ ∫_{Λ\H} F(i(h)T(z)) is m-integrable with integral ∫_{Γ\G} F. -/
lemma integral_quotMeasure_stages {Z} [MeasurableSpace Z] {m μ} [@SFinite Z _ m] (T : Z → G) {i :
  H →* G} (hi : Injective i) (h : MeasurePreserving (fun p ↦ i p.2 * T p.1) (m.prod ν) μ) (hΓ :
  Λ.map i = Γ) {F : G → V} (hF : Measurable F) (hi' : Γ.FixesLeft F) (hI : Integrable F (Γ.qms μ)) :
  let f x := ∫ h, F (i h * T x) ∂Λ.qms ν
  Integrable f m ∧ (Γ.qms μ)[F] = integral m f := (fun I ↦ have J := I.integrable_snd hI
  ⟨J.integral_prod_left, I.integral_eq ▸ integral_prod _ J⟩) (identDistrib_orbitMeasure_of_unfold
  (measurePreserving_count ((Λ.equivMapOfInjective _ hi).trans (.subgroupCongr hΓ)).1)
  (by simpa [subgroup_smul_def] using! h.comp (.comp (.prod (.id _) measurePreserving_orbitMeasure)
  (measurePreserving_prodAssoc ..))) hF h.1 (by simpa))

/-- Unfolding in stages: i : L × H → G closed, L, H unimodular, Λ ⊂ H discrete, Γ = i(Λ), Re ρ ≥ 0,
nonzero near a point. Some R ≠ 0 gives ∫_{Γ\G} F = Rc for continuous integrable F whenever each g
has k in L × H with ∫_L ∫_{Λ\H} F(lakg) = ρ(g)c. -/
lemma exists_integral_stages_eq_mul {L} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [PolishSpace L] [LocallyCompactSpace L] [MeasurableSpace L] [BorelSpace L] κ [IsHaarMeasure κ]
  [κ.IsMulRightInvariant] [ν.IsMulRightInvariant] (i : L × H →* G) (hi : IsClosedEmbedding i) {g₀}
  (ρ : _ → ℂ) (h₀ : ∀ g, 0 ≤ (ρ g).re) (h₁ : ∀ᶠ g in 𝓝 g₀, (ρ g).re ≠ 0) : let Γ := Λ.map (i.comp
  (.inr ..)); ∃ R ≠ 0, ∀ F, Continuous F → Γ.FixesLeft F → Integrable F (Γ.qms μ) → ∀ c, (∀ g,
  ∃ k, ∫ l, ∫ a, F (i (l, a) * (i k * g)) ∂Λ.qms ν ∂κ = ρ g * c) → (Γ.qms μ)[F] = R * c := by
  intro Γ
  let := compHom G i
  obtain ⟨_ : SMulInvariantMeasure (L × H) G μ, _, j⟩ := ⟨by simp [compHom_smul_def]⟩,
    properSMul_of_isClosedEmbedding (X := G) i hi (by tauto), hi.1.comp (isEmbedding_prodMkRight 1)
  use update id 0 1 (orbitMeasure (κ.prod ν) μ)[ρ], by grind, fun F hF hΓ hI c h ↦ ?_
  obtain ⟨_ : DiscreteTopology Γ, _⟩ := (j.homeomorphImage Λ).discreteTopology, hi.measurable
  obtain ⟨I, J⟩ := integral_quotMeasure_stages _ _ (fun (g, y) ↦ i (y, 1) * g) j.2 (by
    simpa using! measurePreserving_orbitMeasure (c := hasCutoff_of_proper).comp
      (measurePreserving_prodAssoc _ κ ν)) rfl hF.measurable hΓ hI
  have K := I.integral_prod_left.div_const c
  have m u v g := (integral_mul_right_eq_self _ u).trans (congrArg _ (funext fun y ↦
    (identDistrib_orbitMeasure_mul_right v fun ⟨γ, h⟩ a ↦ .trans (by simp) (hΓ _ ⟨γ, h, rfl⟩ _)
    ).integral_eq) : _ = ∫ y, ∫ a, F (i (y, a) * g) ∂Λ.qms ν ∂κ)
  by_contra; simp_all [integral_prod]
  exact mem_closure_iff_frequently.1 (dense_of_ae_orbitMeasure (c :=
    hasCutoff_of_proper) (have := h <| i ·
      * ·; by aesop) ((integral_eq_zero_iff_of_nonneg h₀ K.re).1 (integral_re K ▸ by grind)) _) h₁

end

variable {Λ G : Type*} {Y} [Group Λ] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MulAction Λ Y] [Countable Y] {i : Λ →* G} (hi : (⇑i).Injective) {Γ S : Subgroup G}
  [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
  (hS : S ≤ Γ) (hC : ∀ᵉ (γ) (y ∈ C), γ • y ∈ C ↔ i γ ∈ S) (hD : ∀ y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C)
  {k : Y → G → ℂ} (hm : ∀ y, Measurable (k y)) (hk : ∀ γ y x, k (γ • y) (i γ * x) = k y x)

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [BorelSpace G] in
/-- For a countable family of a.e. strongly measurable complex functions k_y with ∫ Σ_y |k_y| dν
finite, the integrals ∫ k_y dν are summable with sum ∫ Σ_y k_y dν. -/
lemma hasSum_integral_of_lintegral {ν : Measure G} (h : ∫⁻ x, tsum (‖k · x‖ₑ) ∂ν < ∞) (hm : ∀ y,
    AEStronglyMeasurable (k y) ν := by fun_prop) : HasSum (ν[k ·]) (∫ x, tsum (k · x) ∂ν) := by
  rw [lintegral_tsum (by fun_prop)] at h
  rw [integral_tsum hm h.ne, (Summable.of_enorm (h.trans_le' _).ne).hasSum_iff]
  grw [enorm_integral_le_lintegral_enorm]

section

attribute [local simp] lintegral_map lintegral_prod lintegral_withDensity_eq_lintegral_mul
  subgroup_smul_def mul_smul Set.indicator mul_assoc

include hi hΓ hS hC hD hm hk in
/-- Unfolding over translates D of a block C: Λ ≅ Γ discrete, k measurable, equivariant, and for
y ∈ C, γy ∈ C iff γ ∈ S. If ∑_D|k_y| on Γ\G or ∑_C|k_y| on S\G has finite integral, ∑_C k_y
is integrable and ∫_{Γ\G}∑_D k_y = ∫_{S\G}∑_C k_y, also termwise. -/
lemma integral_tsum_block (h : ∫⁻ x, ∑' y : D, ‖k y x‖ₑ ∂Γ.qms μ < ∞ ∨ ∫⁻ x, ∑' y : C, ‖k y x‖ₑ
    ∂S.qms μ < ∞) : Integrable (∑' y : C, k y ·) (S.qms μ) ∧ ∫ x, ∑' y : D, k y x ∂Γ.qms μ = ∫ x, ∑'
    y : C, k y x ∂S.qms μ ∧ ∑' y : D, ∫ x, k y x ∂Γ.qms μ = ∫ x, ∑' y : C, k y x ∂S.qms μ := by
  let : MeasurableSpace Y := ⊤
  have := measurable_from_prod_countable_right (f := delta% k.uncurry) hm
  have I : IdentDistrib (fun (x, (y : D)) ↦ k y x) (fun (x, (y : C)) ↦ k y x) ((Γ.qms μ).prod
      count) ((S.qms μ).prod count) := ⟨by fun_prop, by fun_prop, ext_of_lintegral _ fun f _ ↦ by
    obtain ⟨⟨⟩, ⟨⟩⟩ := epsilon_spec (inf_of_le_right hS ▸ hasCutoff_count (_ ⊓ _)).1, hΓ
    simp (disch := fun_prop) [← lintegral_orbitMeasure_lintegral (ν := @count i.range _) (μ := μ)]
    simp_all [(tsum_subtype · fun y ↦ f <| k y ·), ← ENNReal.tsum_mul_left, i.ofInjective_apply,
      ← ENNReal.tsum_comm.trans (tsum_congr (toPerm · |>.tsum_eq _)), ← (i.ofInjective hi).tsum_eq]
    congr!
    split
    cases ‹_›
    rw [← ((i.ofInjective hi).symm.1.trans (.mulRight ‹_›)).tsum_eq,
      ← (S.inclusion_injective hS).tsum_eq]
    repeat aesop⟩
  have ⟨J, K⟩ := (inf_eq_sup.2 I.integrable_iff.eq).ge (by simpa (disch := fun_prop) [Integrable,
    HasFiniteIntegral, Measurable.aestronglyMeasurable])
  simpa [← integral_count_eq_tsum, ← integral_prod_symm _ J, integral_prod, *,
    K.integral_prod_left] using I.integral_eq

include hi hΓ hm hk in
/-- Unfolding over the orbit D of y, for Λ ≅ Γ discrete, S the stabiliser's image, k measurable,
equivariant. If ∫_{Γ\G} Σ_{z∈Y} |k_z| < ∞ or k_y is integrable on S\G, then it is, and
∫_{S\G} k_y = ∫_{Γ\G} Σ_{z∈D} k_z, also termwise. -/
lemma integral_tsum_orbit {y} (hy : (stabilizer Λ y).map i = S) (hD : ∀ z, z ∈ D ↔ y ∈ orbit Λ z) :
  S.FixesLeft (k y) ∧ (∫⁻ x, tsum (‖k · x‖ₑ) ∂Γ.qms μ < ∞ ∨ Integrable (k y) (S.qms μ) → Integrable
    (k y) (S.qms μ) ∧ ∫ x, ∑' z : D, k z x ∂Γ.qms μ = (S.qms μ)[k y] ∧ ∑' z : D, (Γ.qms μ)[k z] =
    (S.qms μ)[k y]) := ⟨by subst hy; simp_all; grind, (by convert (integral_tsum_block hi (C := {y})
  (h := ·) ..) <;> aesop_cat) ∘ Or.imp (by grw [← ·, ← tsum_comp_le_tsum_of_injective]; simp) (·.2)⟩

end

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup V]
  [NormedSpace ℂ V] [CompleteSpace V] (μ : Measure G) [IsHaarMeasure μ] {Γ : Subgroup G}
  [DiscreteTopology Γ] {F : G → V} (hi : Γ.FixesLeft F) (hF : Continuous F) {H : Subgroup G}

/-- Let Γ ≤ H ≤ G, Γ discrete, H closed, μ left invariant, F continuous, left Γ-invariant. If ∫
F(s j(x,b) x) dκ(b) = aF(sx) for s in H (κ a probability, j(x,b) in H) and ∫_H f(h j(x,b))
dh = d∫_H f with d ≠ a, then ∫_{Γ\G} F dμ = 0. -/
lemma integral_quotMeasure_eq_zero_of_mean (hi : Γ.FixesLeft F) (hF :
  Continuous F) [@IsClosed G _ H] (le : Γ ≤ H)
  {C} [MeasurableSpace C] κ [@IsProbabilityMeasure C ‹_› κ] (j : G → C → H) (d : NNReal) (hd :
  ∀ x b, haar.map (· * j x b) = d • haar) {a : ℂ} (ha : a ≠ d) (h : ∀ s x, ∫ b, F (↑(s * j x b) *
  x) ∂κ = a • F (s * x)) (hj : ∀ x, Measurable (j x) := by fun_prop) : (Γ.qms μ)[F] = 0 := by
  have ⟨_, b, e⟩ : HasCutoff (H := H) haar.inv G := inferInstance
  contrapose ha
  borelize V
  have ⟨x, n⟩ := exists_ne_zero_of_integral_ne_zero ((integral_quotMeasure_stages _ haar id ?_ ⟨?_,
    measurePreserving_smul_prod b (μ := μ).2.trans ?_⟩
    (Subgroup.map_subgroupOf_eq_of_le le) ?_ hi (.of_integral_ne_zero ha)).2 ▸ ha)
  rw [← smul_left_inj n]
  have k {b} := identDistrib_orbitMeasure_comp (.id (@count (Γ.subgroupOf H) _)) (F :=
    (F <| · * x)) ⟨?_, hd x b⟩ ?_ ?_
  repeat first
    | fun_prop | rw [integrable_prod_iff'] | simp [k.integral_eq, k.integrable_iff,
      k.norm.integral_eq, NNReal.smul_def, (Integrable.of_integral_ne_zero n).smul_measure_nnreal] |
      rw [integral_integral_swap] | simp_all [← h, ← integral_smul a, ← coe_nnreal_smul, mul_assoc]

/-- Let Γ be a discrete subgroup of G, μ left invariant, F continuous and left Γ-invariant. If
F(uy) = cF(y) for all y, for some u in G and c with |c| = 1, c ≠ 1, then ∫_{Γ\G} F dμ = 0. -/
lemma integral_quotMeasure_eq_zero_of_twist (hi : Γ.FixesLeft F) (hF :
  Continuous F) {u} {c : ℂ} (hc : ‖c‖ = 1) (hc' : c ≠ 1) (hu : ∀ y, F (u * y) = c • F y)
  : (Γ.qms μ)[F] = 0 := let ψ s y := dist (F (s * u * y)) (c • F (s * y))
  let S := (stabilizer Gᵈᵐᵃ ψ).unop.copy ((ψ <| · * ·) ⁻¹' _) rfl
  have : @IsClosed G _ S := isClosed_singleton.preimage (by fun_prop)
  let v : S := ⟨u, funext₂ (by grind [dist_smul₀])⟩
  integral_quotMeasure_eq_zero_of_mean μ hi hF (fun _ _ ↦ funext₂ (by grind [mul_assoc])) (dirac u)
    (a := c) (fun _ _ ↦ v) _ (fun _ _ ↦ isMulLeftInvariant_eq_smul ..) (fun _ ↦ by
    simp_all [← hc]) (by simpa [ψ, v, *] using congrFun₂ ·.2 1)

variable {H : Type*} [Group H] [TopologicalSpace H] [TopologicalSpace Λ] {Γ : Subgroup Λ}

lemma integrable_of_cocompact (h : Γ.Cocpt) [MeasurableSpace Λ] [OpensMeasurableSpace Λ] {μ}
  [@IsFiniteMeasure Λ ‹_› μ] {F : Λ → ℂ} (c : Continuous F) (i : Γ.FixesLeft F) : Integrable F μ :=
  .of_bound (by fun_prop) _
  (.of_forall ((h.choose_spec.1.image c.norm).bddAbove.some_mem <| by grind [h.choose_spec.2 ·]))

lemma cocompact_prod {Δ : Subgroup H} : Γ.Cocpt → Δ.Cocpt → (Γ.prod Δ).Cocpt
  | ⟨_, c⟩, ⟨_, d⟩ => ⟨_, c.1.prod d.1, by simp_all [Γ.mem_prod, and_and_and_comm]⟩
