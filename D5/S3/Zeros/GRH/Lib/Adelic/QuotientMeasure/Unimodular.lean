/- GID: D5/S3/Zeros/GRH/Lib/Adelic/QuotientMeasure/Unimodular
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/QuotientMeasure/Unimodular
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.QuotientMeasure.Unimodular. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/QuotientMeasure/Unimodular.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.QuotientMeasure.Packing
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.CuspKernel.CircleMean
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: invariant integration on a quotient (Weil's formula), unfolding and unimodularity.
For second countable groups, the quotient integral is integration against a measurable weight of
total mass one on each orbit, so no orbit space or section is needed to define it. Two vanishing
lemmas avoid unimodularity. Source: O. Kallenberg, Invariant measures and disintegrations with
applications to Palm and related kernels, Probab. Theory Related Fields 139 (2007) 285-310, Lemma
2.1 and Theorem 2.4 (as cited in D. Gentner, G. Last, Math. Z. 267 (2011), §2); for the classical
form, N. Bourbaki, Intégration VII, 1963.

Known result: Transference theorem comparing the covering radius of a lattice with the first minimum
of its dual. It is proved here with constant n squared in place of n/2, for any subgroup of a
Euclidean space whose dual has no short vector, by projecting along a short vector. It is applied to
hermitian lattices to give short bases. Source: Lagarias-Lenstra-Schnorr, Korkin-Zolotarev bases and
successive minima of a lattice and its reciprocal lattice, Combinatorica 10 (1990), 333–348 (sharp
form in Banaszczyk, Math. Ann. 296 (1993)).

This file: Proper actions have cutoff weights; discrete subgroups; unfolding a sum over a lattice.
Covering radius of a subgroup at most n² over the first minimum of its dual. Quotient measure under
equivariant measure-preserving maps and right translation. Groups with a lattice are unimodular;
cocompact discrete subgroups have finite covolume. -/

open Module Classical ENNReal Matrix MeasureTheory NeZero ProbabilityTheory Set Submodule
  LinearMap.BilinForm MeasureTheory.Measure

variable {I H X G} [MeasurableSpace I] [MeasurableSpace H] [Countable I] [Group G]
  [MeasurableSingletonClass I] [MeasurableSingletonClass H] [MeasurableSpace X] [TopologicalSpace G]

lemma measurePreserving_count (e : I ≃ H) : MeasurePreserving e count count :=
    ⟨.of_discrete, .trans (map_sum .of_discrete) (by simp [count, ← Function.comp_def])⟩

variable [Group H] [MeasurableMul H] [TopologicalSpace H] (Γ N : Subgroup G) [DiscreteTopology Γ]

lemma integral_count_eq_tsum (f : I → ℂ) : ∫ x, f x ∂count = ∑' x, f x := by
    simpa using! integral_sum_dirac (c := 1) nofun

lemma tsum_toReal_smul_of_tsum_eq_one {I} {f : I → ℝ≥0∞} (h : ∑' x, f x = 1) (z : ℂ) : ∑' x,
  (f x).toReal • z = z := by
  simp_all [tsum_mul_right, ← Complex.ofReal_tsum, ← tsum_toReal_eq, ENNReal.ne_top_of_tsum_ne_top]

/-- Proper actions have cutoffs. -/
@[to_additive hasAddCutoff_of_proper] instance hasCutoff_of_proper [MulAction H X]
    [MeasurableSMul₂ H X] {ν} [@SFinite H _ ν] [IsMulRightInvariant ν] [TopologicalSpace X]
    [c : SigmaCompactSpace X] [T2Space X] [OpensMeasurableSpace X] [ProperSMul H X]
    [IsFiniteMeasureOnCompacts ν] [NeZero ν] : HasCutoff ν X := have ⟨K, hK, _⟩ := c
  have p x : ∃ n, 0 < ν ((· • x) ⁻¹' K n) := by
    by_contra; simp_all [← preimage_iUnion, ← measure_iUnion_null_iff]
  have m n := measurable_measure_prodMk_right (measurable_smul (hK n).measurableSet)
  ⟨_, .find (fun n ↦ (m n).inv.indicator (hK n).measurableSet) (m · measurableSet_Ioi) p, by
  simpa [indicator, preimage, fun (x : X) n ↦ by simpa [mul_smul] using (measure_preimage_mul_right
    ν · {h | h • x ∈ K n})] using fun x ↦ (lintegral_indicator_const (measurable_smul_const x (hK
    _).measurableSet) _).trans (ENNReal.inv_mul_cancel (Nat.find_spec (p _)).ne' (by simpa using!
    (ProperSMul.isCompact_setOfPred_inter_nonempty isCompact_singleton (hK _)).measure_ne_top))⟩

@[to_additive] instance [DiscreteTopology H] : IsHaarMeasure (@count H _) := by
  refine' {..} <;> aesop (add simp isCompact_iff_finite)

/-- For a subgroup N of G, the bijection (G/N) × N → G sending (q, u) to u times the inverse of
the chosen representative of the coset q. -/
noncomputable abbrev cosetProdEquiv : (G ⧸ N) × N ≃ G := by use fun (q, u) ↦ u * q.out⁻¹,
          fun γ ↦ ⟨↑γ⁻¹, _, QuotientGroup.eq.1 ⟦γ⁻¹⟧.out_eq.symm⟩ <;> aesop_cat

instance : DiscreteTopology (Γ.subgroupOf N) := .preimage_of_continuous_injective Γ.carrier
    (by fun_prop) (by simp)

instance : DiscreteTopology ↥(Γ ⊓ N) := .of_subset ‹_› (by simp)

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] {S X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [LocallyCompactSpace X] [SetLike S X] {N : S} {μ : Measure G} [IsHaarMeasure μ] {E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Λ : Submodule ℤ E) [Module.Finite ℝ E] {ρ : ℝ}

@[to_additive] instance : Countable Γ := countable_of_Lindelof_of_discrete

instance instSecondCountableTopologySubtypeMem_new
    : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _

instance locallyCompactSpace_of_isClosed [hN : @IsClosed X _ N] :
    LocallyCompactSpace N := hN.locallyCompactSpace

@[to_additive addCutoff] instance hasCutoff_count : HasCutoff (@count Γ _) G := inferInstance

lemma quotMeasure_bot : Subgroup.qms ⊥ μ = μ := by
    simpa using (identDistrib_orbitMeasure ⟨measurable_one, by simp⟩ measurable_id (by simp)).3

/-- Unfolding: for a discrete subgroup Γ of a second countable locally compact group G with left
Haar measure μ and f integrable, g ↦ ∑_{γ∈Γ} f(γg) is integrable on Γ\G, with integral ∫_G f
dμ.

Known result: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity. -/
lemma integral_quotMeasure_tsum {f : G → ℂ} (h : Integrable f μ) :
  Integrable (fun g ↦ ∑' γ : Γ, f (γ * g))
  (Γ.qms μ) ∧ ∫ g, ∑' γ : Γ, f (γ * g) ∂Γ.qms μ = ∫ g, f g ∂μ := by simpa [← integral_count_eq_tsum]
  using! ((measurePreserving_orbitMeasure.fubini h).imp_left (·.integral_prod_left))

/-- Minkowski's bound. If the nonzero vectors of a lattice Λ with basis b in a Euclidean space
of dimension m ≥ 1 have length at least ρ > 0, then its covolume |det b|, in orthonormal
coordinates, is at least (ρ/√m)^m. -/
lemma minkowski_pow_le_abs_det [NormedAddCommGroup S] [InnerProductSpace ℝ S] [Module.Finite ℝ S]
  {ρ : ℝ} (hρ : 0 < ρ) {m} (hm : 0 < m) {o : OrthonormalBasis (Fin m) ℝ S} {b : Basis _ ℝ S}
  (h : ∀ y ∈ span ℤ (.range b), y ≠ 0 → ρ ≤ ‖y‖) : (ρ / √m) ^ m ≤ |det (of (o.repr <| b ·))| := by
  have := @countable_of_Lindelof_of_discrete
  simpa [*, mul_pow, mul_comm, ENNReal.mul_le_mul_iff_right] using!
    (exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (ZSpan.isAddFundamentalDomain'
    (b.map o.toBasis.equivFun) volume) (by simp) (convex_ball 0 (ρ / √m))).mt (by
    simp [← ZSpan.map]; intros
    grw [h, ← o.1.norm_map, PiLp.norm_eq_of_L2, norm_le_pi_norm] <;> simp_all [field])

/-- Weak transference. Let Λ be a subgroup of a Euclidean space of dimension m ≥ 1 whose dual
has no nonzero vector shorter than ρ > 0. Then Λ has a nonzero vector shorter than 2m / ρ. -/
lemma weak_transference (hρ : 0 < ρ) (h : ∀ y ∈ dualSubmodule (innerₗ E) Λ, y ≠ 0 → ρ ≤ ‖y‖)
    (hm : 0 < finrank ℝ E) : ∃ b ∈ Λ, b ≠ 0 ∧ ‖b‖ < 2 * finrank ℝ E / ρ := by
  by_contra! H
  have : DiscreteTopology Λ := .of_forall_le_norm (by bound) (H _ ·.2 ∘ by simp)
  have : IsZLattice ℝ Λ := ⟨orthogonal_eq_bot_iff.1 (subsingleton_iff_eq_bot.1
    (@PreconnectedSpace.trivial_of_discrete _ _ _ (.of_forall_le_norm hρ fun u ↦
    h u (by simp [real_inner_comm, u.2 · <| subset_span ·]) ∘ by simp)))⟩
  have e := (ZLattice.rank ℝ Λ ▸ finBasis ..).ofZLatticeBasis_span ℝ
  apply (mul_le_mul (minkowski_pow_le_abs_det hρ hm (by rwa [← e,
    dualSubmodule_span_of_basis _ (by simp_all [nondegenerate_iff', isSymm_inner])] at h))
    (minkowski_pow_le_abs_det _ hm (e.symm ▸ H)) ..).not_gt
  rw [← det_transpose, ← abs_mul, ← det_mul, mul_eq_one_symm]
  simp [field, one_lt_pow₀, hm.ne', ← mul_pow]
  exact Matrix.ext fun _ _ ↦ ((stdOrthonormalBasis ..).1.inner_map_map ..).trans
    (apply_dualBasis_left (B := innerₗ E) ..)
  repeat bound

/-- Weak transference for the covering radius. Let Λ be a subgroup of a Euclidean space of
dimension m whose dual has no nonzero vector shorter than ρ > 0. Then every vector u is
within m² / ρ of Λ.

Known result: Transference theorem: covering radius of a lattice against the first minimum of its
dual. -/
lemma weak_transference_covering_radius (hρ : 0 < ρ) (h : ∀ y ∈ dualSubmodule (innerₗ E) Λ, y ≠ 0 →
  ρ ≤ ‖y‖) u : ∃ x ∈ Λ, ‖u - x‖ ≤ finrank ℝ E ^ 2 / ρ := by
  induction' c : finrank ℝ E with n ih generalizing E
  simp_all [finrank_zero_iff_forall_zero]
  choose b _ o e using weak_transference Λ hρ h (by lia)
  choose x _ g using by simpa [starProjection_singleton, sub_sub_sub_comm u, ← sub_smul]
    using (ih (Λ.map (.restrictScalars ℤ (ℝ ∙ b)ᗮ.orthogonalProjectionOnto.1)) (fun y o ↦ h y
    (fun z a ↦ by simpa using o _ ⟨z, a, rfl⟩) ∘ by simp)
    (orthogonalProjectionOnto _ u) (finrank_orthogonal_span_singleton (_i := ⟨c⟩) o))
  exact ⟨x + (round _ : ℝ) • b, .symm ⟨by grw [← sub_sub, norm_sub_le_norm_sub_add_norm_sub,
   g, ← sub_smul, norm_smul, (abs_sub_round _ : ‖_‖ ≤ _), e, c]; field; grind, mod_cast by bound⟩⟩

variable {Γ : Subgroup G} [DiscreteTopology Γ] {H X : Type*} {H' Y Z} [MeasurableSpace H]
  [MeasurableSpace X] [MeasurableSpace H'] [MeasurableSpace Y] [MeasurableSpace Z] [Group H]

/-- Let σ : (H,ν) → (H',ν'), T : (X,μ) → (Y,μ') preserve measure, T(hx) = σ(h)T(x); ν, μ
s-finite, ν inversion invariant, μ H-invariant, ν, ν' with cutoffs. For measurable
H'-invariant F, F∘T and F are identically distributed for the quotient measures. -/
@[to_additive identDistrib_addOrbitMeasure_comp] lemma identDistrib_orbitMeasure_comp [MulAction H
  X] [MeasurableInv H] [MeasurableSMul₂ H X] {ν : Measure H} [@SFinite H _ ν] [ν.IsInvInvariant]
  {μ : MeasureTheory.Measure X} [SFinite μ] [SMulInvariantMeasure H X μ] [HasCutoff ν X]
  [SMul H' Y] [MeasurableSMul₂ H' Y] {ν' μ'} [HasCutoff ν' Y] {σ} (hσ : MeasurePreserving σ ν ν')
  {T} (hT : MeasurePreserving T μ μ') (h : ∀ h x, T (h • x) = (σ h : H') • T x) {F : Y → Z}
  (hi : ∀ (h : H') y, F (h • y) = F y) (hF : Measurable F := by fun_prop) : IdentDistrib (F <|
  T ·) F (orbitMeasure ν μ) (orbitMeasure ν' μ') := (identDistrib_orbitMeasure_of_unfold hσ
  (by simpa [← h] using! hT.comp measurePreserving_orbitMeasure) hF hT.1 hi).symm

variable [MulAction H X] [MeasurableInv H] [MeasurableSMul₂ H X] {ν} [@SFinite H _ ν]
  [ν.IsInvInvariant] {μ : MeasureTheory.Measure X} [SFinite μ] [SMulInvariantMeasure H X μ]
  [HasCutoff ν X] in
/-- Let H act on a group X, commuting with right multiplication and admitting a cutoff, with ν
inversion invariant and μ H-invariant and right invariant. For measurable H-invariant F, the
functions x ↦ F(xg) and F have the same distribution under `orbitMeasure` ν μ. -/
lemma identDistrib_orbitMeasure_mul_right [Group X] [MeasurableMul₂ X] [IsScalarTower H X X]
    [μ.IsMulRightInvariant] g {F} (hi : ∀ (h : H) y, F (h • y) = (F y : Z)) (hF : Measurable F :=
    by fun_prop) : IdentDistrib (F <| · * g) F (orbitMeasure ν μ) (orbitMeasure ν μ) :=
  identDistrib_orbitMeasure_comp (.id _) (measurePreserving_mul_right ..) (by aesop) hi

@[to_additive ne_addQuot] instance : NeZero (Γ.qms μ) :=
    ⟨(by simpa [·, ne'] using measurePreserving_orbitMeasure (ν := @count Γ _) (μ := μ).2)⟩

/-- A group with a lattice is unimodular: if Γ is discrete in the locally compact second
countable Hausdorff group G and Γ\G has finite volume for the left Haar measure μ, then μ is
right invariant. -/
lemma isMulRightInvariant_of_finite_covolume (_ : IsFiniteMeasure (Γ.qms μ)) :
    IsMulRightInvariant μ := ⟨(have := map_right_mul_eq_modularCharacterFun_smul μ ·
  have := (identDistrib_orbitMeasure_comp (.id (@count Γ _)) ⟨by fun_prop,
    this⟩ (by simp [mul_assoc]) (by simp) measurable_one).symm.lintegral_eq
  by simp_all [← coe_nnreal_smul, ne, ENNReal.mul_eq_right, -withDensity_apply])⟩

instance [CompactSpace G] : IsMulRightInvariant μ :=
  isMulRightInvariant_of_finite_covolume (quotMeasure_bot.substr inferInstance)

instance [IsMulRightInvariant μ] : IsInvInvariant μ := ⟨((haarMeasure_unique ..).congr
    (haarMeasure_unique _ (ofNonempty ⊔ .map _ continuous_inv (isOpenMap_inv G) ofNonempty))).2
    congr($(by simp [union_comm]) • _)⟩

variable (μ)

/-- A cocompact discrete subgroup has finite covolume: if Γ is discrete in a second countable
locally compact group G and a compact set meets every orbit Γg, the quotient of Haar measure
by Γ is finite. -/
@[to_additive isFiniteMeasure_addOrbitMeasure] lemma isFiniteMeasure_quotMeasure_of_cocompact :
  Γ.Cocpt → IsFiniteMeasure (Γ.qms μ) | ⟨_, c, h⟩ => ⟨by
  grw [← (measurePreserving_orbitMeasure (ν := @count Γ _) (μ := μ).measure_preimage_le _).trans_lt
    c.measure_lt_top, prod_apply_symm (c.measurableSet.preimage (by fun_prop)), lintegral_count,
    ← measure_iUnion_le, iUnion_eq_univ_iff.2 (by simpa)]⟩

/-- On a second countable locally compact group with a Haar measure μ that is also right
invariant, every s-finite right invariant measure ν is dμ for some d in [0, ∞]. -/
lemma exists_eq_smul_haar [μ.IsMulRightInvariant] {ν} [SFinite ν] (_ : ν.IsMulRightInvariant) :
  ∃ d : ENNReal, ν = d • μ := ⟨_, .symm (Measure.ext fun _ h ↦ by
    simpa [lintegral_mul_right_eq_self, h.inv, mul_comm (μ _)] using
    lintegral_orbitMeasure_lintegral (ν := μ) (μ := ν.inv) (measurable_one.indicator h.inv))⟩
