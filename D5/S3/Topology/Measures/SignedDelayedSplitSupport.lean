/- GID: D5/S3/Topology/Measures/SignedDelayedSplitSupport
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedDelayedSplitSupport
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Signed split source convergence and literal delayed columns -/

import D5.S3.Topology.Measures.SignedSplitSuccessor

/-! Common signed source limits and the literal delayed column construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Topology.Measures.SignedDelayedSplit

open SignedSplitSuccessor

universe u v w

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
variable {L : Type v} [TopologicalSpace L] [T2Space L]
  [MeasurableSpace L] [BorelSpace L]

/-- On the source clopen, the new true sheet is absent. The old signed F
therefore gives F for every successor lift on every infinite source refinement. -/
private theorem source_limit_on_split
    [T2Space K] [TopologicalSpace.MetrizableSpace K] [TotallyDisconnectedSpace K]
    (p : K → L) (hp : Continuous p)
    (P Q : Set L) (hP : IsClopen P) (hPQ : Disjoint P Q)
    (nu : ℕ → SignedMeasure L)
    (hbound : ∀ n, (nu n).totalVariation.real univ ≤ 1)
    (hnull : ∀ n, (nu n).totalVariation Pᶜ = 0)
    (J M : Set ℕ) (hM : M.Infinite) (hMJ : M ⊆ J)
    (oldF : ∀ s : ℕ → SignedMeasure K,
      (∀ n, (s n).map p = nu n) →
      (∀ n, (s n).totalVariation univ = (nu n).totalVariation univ) →
      ∃ mu : SignedMeasure K, Tendsto
        (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
        (atTop ⊓ 𝓟 J) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual))
    (Y Z : Set K) (hY : IsClosed Y) (hZ : IsClosed Z)
    (hclosed : IsClosed (splitCarrier Y Z)) (hZQ : Z ⊆ p ⁻¹' Q) :
    letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
    ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
      (∀ n, (sigma n).map (fun x => p x.1.1) = nu n) →
      (∀ n, (sigma n).totalVariation univ = (nu n).totalVariation univ) →
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
          (atTop ⊓ 𝓟 M) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
  classical
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
  intro sigma hmap hmass
  let projection : splitCarrier Y Z → K := fun x => x.1.1
  have hpj : Continuous projection := continuous_fst.comp continuous_subtype_val
  let mid : ℕ → SignedMeasure K := fun n => (sigma n).map projection
  have hmid (n : ℕ) := map_mass_through_factor projection hpj.measurable p hp.measurable
    (sigma n) (nu n) (hmap n) (hmass n)
  obtain ⟨oldMu, holdMu⟩ := oldF mid (fun n => (hmid n).1) (fun n => (hmid n).2)
  have holdM := holdMu.mono_left (inf_le_inf le_rfl (Filter.principal_mono.mpr hMJ))
  letI : Infinite ↥M := Set.infinite_coe_iff.mpr hM
  let enum : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet M
  have hmono : StrictMono enum := enum.strictMono
  have hrange : Set.range enum = M := Nat.orderEmbeddingOfSet_range M
  have henum : Tendsto enum atTop (atTop ⊓ 𝓟 M) := tendsto_inf.mpr
    ⟨hmono.tendsto_atTop, tendsto_principal.mpr (Eventually.of_forall
      fun k => hrange ▸ Set.mem_range_self k)⟩
  have hsigbound (k : ℕ) : (sigma (enum k)).totalVariation.real univ ≤ 1 := by
    simpa only [Measure.real, hmass] using hbound (enum k)
  have hside (k : ℕ) (A : Set K) :
      sigma (enum k) ({x | x.1.2 = true} ∩ projection ⁻¹' A) = 0 := by
    have hn := support_null (p ∘ projection) (hp.comp hpj) (sigma (enum k))
      (nu (enum k)) (hmap _) (hmass _) hP (hnull _)
    apply (sigma (enum k)).null_of_totalVariation_zero
    apply measure_mono_null _ hn
    intro x hx hxP
    have hxZ : x.1.1 ∈ Z := by
      rcases x.2 with hxY | hxZ
      · exact (Bool.false_ne_true (hxY.2.symm.trans hx.1)).elim
      · exact hxZ.1
    exact Set.disjoint_left.mp hPQ hxP (hZQ hxZ)
  obtain ⟨mu, hmu, hpos, hneg, hconv⟩ :=
    SignedSplitReferenceConvergence.exists_signed_limit_of_reference Y Z hY hZ
      1 (by norm_num) (fun k => sigma (enum k)) hsigbound oldMu
      (fun _ => ∅) (fun _ => MeasurableSet.empty) (fun _ _ _ => le_rfl)
      (fun _ => 0) tendsto_const_nhds (fun A hA => by
        have ht := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp (holdM.comp henum))
          (LocallyConstant.charFn ℝ hA).toContinuousMap
        change Tendsto (fun k => NormPreservingLifts.signedFunctional (mid (enum k))
          (LocallyConstant.charFn ℝ hA).toContinuousMap) atTop
          (𝓝 (NormPreservingLifts.signedFunctional oldMu
            (LocallyConstant.charFn ℝ hA).toContinuousMap)) at ht
        change Tendsto (fun k => mid (enum k) A) atTop (𝓝 (oldMu A))
        simpa only [ClopenCauchyConvergence.signedFunctional_charFn] using ht)
      (fun A _ => Eventually.of_forall fun k => by
        change |sigma (enum k) ({x | x.1.2 = true} ∩ projection ⁻¹' A) -
          oldMu (A ∩ ∅)| ≤ 0
        rw [hside k A, inter_empty, oldMu.empty, sub_self, abs_zero])
  refine ⟨mu, hmu, hpos, hneg, ?_⟩
  apply tendsto_def.mpr
  intro U hU
  obtain ⟨k, hk⟩ := eventually_atTop.mp (hconv hU)
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_ge_atTop (enum k)] with n hn hnM
  obtain ⟨m, rfl⟩ : n ∈ Set.range enum := hrange.symm ▸ hnM
  exact hk m (hmono.le_iff_le.mp hn)

private lemma split_locallyConstant_eventually
    {Γ : Type*} (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (p : K → L) (V : ℕ → Set L) (l : Filter ℕ)
    (Y Z : Set K) (hclosed : IsClosed (splitCarrier Y Z))
    (hE : ∀ c, ∀ᶠ n in l, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y)
    (hside : ∀ᶠ n in l, ∀ x y : splitCarrier Y Z,
      p x.1.1 ∈ V n → p y.1.1 ∈ V n → p x.1.1 = p y.1.1 → x.1.2 = y.1.2) :
    ∀ f : LocallyConstant (splitCarrier Y Z) ℝ, ∀ᶠ n in l,
      ∀ x y : splitCarrier Y Z, p x.1.1 ∈ V n → p y.1.1 ∈ V n →
        p x.1.1 = p y.1.1 → f x = f y := by
  letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
  let projection : splitCarrier Y Z → K := fun x => x.1.1
  let sc : Option Γ → C(splitCarrier Y Z, Bool) := fun c =>
    match c with
    | none => ⟨fun x => x.1.2, continuous_snd.comp continuous_subtype_val⟩
    | some c => ⟨fun x => coord c x.1.1,
        (coord c).continuous.comp (continuous_fst.comp continuous_subtype_val)⟩
  have hsc : Function.Injective (fun x : splitCarrier Y Z => fun c => sc c x) := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · apply hsep
      funext c
      exact congrFun hxy (some c)
    · exact congrFun hxy none
  have hEc (c : Option Γ) : ∀ᶠ n in l, ∀ x y : splitCarrier Y Z,
      p x.1.1 ∈ V n → p y.1.1 ∈ V n → p x.1.1 = p y.1.1 → sc c x = sc c y := by
    cases c with
    | none => exact hside
    | some c =>
      filter_upwards [hE c] with n hn
      exact fun x y hx hy hxy => hn x.1.1 y.1.1 hx hy hxy
  intro f
  have hpieces : ∀ a ∈ f.range_finite.toFinset,
      ∀ᶠ n in l, ∀ x y : splitCarrier Y Z,
        p x.1.1 ∈ V n → p y.1.1 ∈ V n → p x.1.1 = p y.1.1 →
          (f x = a ↔ f y = a) := by
    intro a _
    exact eventually_clopen_fibre l sc hsc (p ∘ projection) V hEc
      (f.isLocallyConstant.isClopen_fiber a)
  filter_upwards [(Filter.eventually_all_finset f.range_finite.toFinset).mpr hpieces] with n hn
  intro x y hx hy hxy
  exact ((hn (f x) (f.range_finite.mem_toFinset.mpr ⟨x, rfl⟩) x y hx hy hxy).mp rfl).symm

/-- The source reference is selected once from a genuine lift class. All other
choices inherit it on the same final source set. -/
theorem common_source_on_split
    [T2Space K] [TopologicalSpace.MetrizableSpace K] [TotallyDisconnectedSpace K]
    {Γ : Type*} (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (p : K → L) (hp : Continuous p) (hponto : Function.Surjective p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (P Q : Set L) (hP : IsClopen P) (hPQ : Disjoint P Q)
    (nu : ℕ → SignedMeasure L)
    (hbound : ∀ n, (nu n).totalVariation.real univ ≤ 1)
    (hnull : ∀ n, (nu n).totalVariation Pᶜ = 0)
    (hsupport : ∀ n, (nu n).totalVariation (V n)ᶜ = 0)
    (J M : Set ℕ) (hM : M.Infinite) (hMJ : M ⊆ J)
    (oldF : ∀ s : ℕ → SignedMeasure K,
      (∀ n, (s n).map p = nu n) →
      (∀ n, (s n).totalVariation univ = (nu n).totalVariation univ) →
      ∃ mu : SignedMeasure K, Tendsto
        (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
        (atTop ⊓ 𝓟 J) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual))
    (Y Z : Set K) (hY : IsClosed Y) (hZ : IsClosed Z)
    (hclosed : IsClosed (splitCarrier Y Z))
    (honto : Function.Surjective (fun x : splitCarrier Y Z => x.1.1))
    (hZQ : Z ⊆ p ⁻¹' Q)
    (hE : ∀ c, ∀ᶠ n in atTop ⊓ 𝓟 M, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y)
    (hside : ∀ᶠ n in atTop ⊓ 𝓟 M, ∀ x y : splitCarrier Y Z,
      p x.1.1 ∈ V n → p y.1.1 ∈ V n → p x.1.1 = p y.1.1 → x.1.2 = y.1.2) :
    letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
    ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
      Measure.Regular mu.toJordanDecomposition.posPart ∧
      Measure.Regular mu.toJordanDecomposition.negPart ∧
      ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
        (∀ n, (sigma n).map (fun x => p x.1.1) = nu n) →
        (∀ n, (sigma n).totalVariation univ = (nu n).totalVariation univ) →
        Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
          (atTop ⊓ 𝓟 M) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
  classical
  letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
  letI : MetricSpace (splitCarrier Y Z) := TopologicalSpace.metrizableSpaceMetric _
  let projection : splitCarrier Y Z → K := fun x => x.1.1
  have hpj : Continuous projection := continuous_fst.comp continuous_subtype_val
  choose ref hrmap hrmass using fun n =>
    NormPreservingLiftExistence.exists_norm_preserving_lift (p ∘ projection)
      (hp.comp hpj) (hponto.comp honto) (nu n)
  obtain ⟨mu, hmu, hpos, hneg, href⟩ := source_limit_on_split p hp P Q hP hPQ
    nu hbound hnull J M hM hMJ oldF Y Z hY hZ hclosed hZQ ref hrmap hrmass
  refine ⟨mu, hmu, hpos, hneg, ?_⟩
  intro sigma hmap hmass
  exact NormPreservingLifts.arbitrary_lifts_tendsto (atTop ⊓ 𝓟 M)
    (p ∘ projection) (hp.comp hpj) V hV nu ref sigma hrmap hmap hrmass hmass
    hsupport 1 (by norm_num) hbound
    (split_locallyConstant_eventually coord hsep p V _ Y Z hclosed hE hside)
    (NormPreservingLifts.signedFunctional mu).toWeakDual href

/-- A norm-preserving lift of a Dirac measure assigns mass one to any
measurable set containing its entire fibre. No positivity premise on the lift
is used. -/
private lemma dirac_lift_apply_of_fibre
    (p : K → L) (hp : Continuous p) (y : L) (t : SignedMeasure K)
    (ht : t.map p = (Measure.dirac y).toSignedMeasure)
    (hm : t.totalVariation univ = 1) (A : Set K) (hA : MeasurableSet A)
    (hf : p ⁻¹' {y} ⊆ A) : t A = 1 := by
  have htv : t.totalVariation.map p = Measure.dirac y := by
    have h := NormPreservingLifts.totalVariation_map_of_mass t p hp.measurable (by
      rw [ht, SignedMeasure.totalVariation_eq_variation, Measure.variation_toSignedMeasure,
        Measure.dirac_apply_of_mem (mem_univ _), hm])
    simpa only [ht, SignedMeasure.totalVariation_eq_variation,
      Measure.variation_toSignedMeasure] using h.symm
  have hnull : t.totalVariation Aᶜ = 0 := by
    apply measure_mono_null (compl_subset_compl.mpr hf)
    rw [← preimage_compl, ← Measure.map_apply hp.measurable (measurableSet_singleton y).compl,
      htv, Measure.dirac_apply' _ (measurableSet_singleton y).compl]
    simp
  have hcut := apply_eq_inter_of_null_compl t MeasurableSet.univ hA hnull
  have hone := congrArg (fun s : SignedMeasure L => s univ) ht
  rw [VectorMeasure.map_apply _ hp.measurable MeasurableSet.univ, preimage_univ,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ, Measure.real,
    Measure.dirac_apply_of_mem (mem_univ _), ENNReal.toReal_one] at hone
  simpa only [univ_inter] using hcut.symm.trans hone

/-- Direct delayed refinement: the exclusion is fixed first, then the target,
the literal Q-slice, its finite tests, and finally all auxiliary indices. -/
theorem exists_literal_delayed_column
    {Rows : Type w} {Γ : Type*} {q : ℕ}
    (code : Rows → ℕ) (hcode : Function.Injective code)
    (h : OrderedHistory Rows K q)
    (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (B : ℕ → TopologicalSpace.Clopens K)
    (S : Set ℕ) (hS : S.Infinite) (p : K → L) (hp : Continuous p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (Q : Set L) (hQ : IsClopen Q) (y : ℕ → L)
    (hyV : ∀ n, y n ∈ V n) (hyQ : ∀ n, y n ∈ Q)
    (nu : ℕ → SignedMeasure L)
    (hdirac : ∀ n, nu n = (Measure.dirac (y n)).toSignedMeasure)
    (z : K)
    (hfull : ∀ A : Set K, IsClopen A → z ∈ A →
      ∀ᶠ n in atTop ⊓ 𝓟 S, p ⁻¹' {y n} ⊆ A)
    (hE : ∀ c, ∀ᶠ n in atTop ⊓ 𝓟 S, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y)
    (Base : Rows → Type v)
    [∀ r, TopologicalSpace (Base r)] [∀ r, T2Space (Base r)]
    [∀ r, MeasurableSpace (Base r)] [∀ r, BorelSpace (Base r)]
    (pR : ∀ r, K → Base r) (hpR : ∀ r, Continuous (pR r))
    (VR : ∀ r, ℕ → Set (Base r)) (hVR : ∀ r n, IsClopen (VR r n))
    (nuR : ∀ r, ℕ → SignedMeasure (Base r))
    (sR : Rows → ℕ → SignedMeasure K) (muR : Rows → SignedMeasure K)
    (hsRmap : ∀ r n, (sR r n).map (pR r) = nuR r n)
    (hsRmass : ∀ r n, (sR r n).totalVariation univ = (nuR r n).totalVariation univ)
    (hRnull : ∀ r n, (nuR r n).totalVariation (VR r n)ᶜ = 0)
    (pool : Rows → Set ℕ) (hpool : ∀ r, (pool r).Infinite)
    (hRE : ∀ r c, ∀ᶠ n in atTop ⊓ 𝓟 (pool r), ∀ x y,
      pR r x ∈ VR r n → pR r y ∈ VR r n → pR r x = pR r y → coord c x = coord c y)
    (hRref : ∀ r, Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR r n)).toWeakDual)
      (atTop ⊓ 𝓟 (pool r)) (𝓝 (NormPreservingLifts.signedFunctional (muR r)).toWeakDual))
    (hRdis : ∀ r, Pairwise (fun n m => Disjoint (pR r ⁻¹' VR r n) (pR r ⁻¹' VR r m)))
    (havoid : ∀ r (j : Fin q), z ∉ pR r ⁻¹' VR r (h.m r j)) :
    ∃ c : OrderedColumn Rows K,
      c.Spec code h B S p (fun n => V n ∩ Q) nu (Measure.dirac z)
        Base pR VR nuR muR pool ∧
      (∀ r, z ∉ pR r ⁻¹' VR r (c.m r)) ∧
      (p ⁻¹' {y c.n} ⊆ (c.H : Set K)) ∧
      ∃ R : Set K, (c.H : Set K) = p ⁻¹' (V c.n ∩ Q) \ R ∧
        R = ⋃ r : {r // code r < q}, ⋃ j : Fin q, pR r.val ⁻¹' VR r.val (h.m r.val j) := by
  classical
  let A : Finset Rows := ((Set.finite_Iio q).preimage hcode.injOn).toFinset
  have hA (r : Rows) : r ∈ A ↔ code r < q := by simp [A]
  let R : TopologicalSpace.Clopens K :=
    ⟨⋃ r ∈ A, ⋃ j : Fin q, pR r ⁻¹' VR r (h.m r j),
      isClopen_biUnion_finset (fun r _ => isClopen_iUnion_of_finite
        (fun j => (hVR r _).preimage (hpR r)))⟩
  have hzR : z ∉ (R : Set K) := by
    simp only [R, TopologicalSpace.Clopens.coe_mk, mem_iUnion]
    rintro ⟨r, _, j, hz⟩
    exact havoid r j hz
  have hER := eventually_clopen_fibre (atTop ⊓ 𝓟 S) coord hsep p V hE R.isClopen
  have hFR := hfull (R : Set K)ᶜ R.isClopen.compl hzR
  have hev : ∀ᶠ n in atTop, n ∈ S →
      (p ⁻¹' {y n} ⊆ (R : Set K)ᶜ) ∧
      ∀ x y, p x ∈ V n → p y ∈ V n → p x = p y → (x ∈ R ↔ y ∈ R) :=
    eventually_inf_principal.mp (hFR.and hER)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨n, hnS, hnN⟩ := (hS.sdiff (Set.finite_Iic (max N (Finset.univ.sup h.n)))).nonempty
  have hnBig : max N (Finset.univ.sup h.n) < n := lt_of_not_ge hnN
  have hnM : Finset.univ.sup h.n < n := (le_max_right _ _).trans_lt hnBig
  have hn := hN n ((le_max_left _ _).trans hnBig.le) hnS
  let H : TopologicalSpace.Clopens K :=
    ⟨p ⁻¹' (V n ∩ Q) \ R, (((hV n).inter hQ).preimage hp).inter R.isClopen.compl⟩
  have hFH : p ⁻¹' {y n} ⊆ (H : Set K) := by
    intro x hx
    have hx' : p x = y n := hx
    exact ⟨⟨hx'.symm ▸ hyV n, hx'.symm ▸ hyQ n⟩, hn.1 hx⟩
  let F : Finset (TopologicalSpace.Clopens K) :=
    (Finset.univ.biUnion h.F) ∪ {B q, H, R}
  let test : {A // A ∈ F} → C(K, Bool) := fun A =>
    ⟨(A.val : Set K).boolIndicator,
      (continuous_boolIndicator_iff_isClopen _).mpr A.val.isClopen⟩
  have hex (r : Rows) := exists_auxiliary_index (pool r) (hpool r) (pR r) (hpR r)
    (VR r) (hVR r) (nuR r) (sR r) (muR r) (hsRmap r) (hsRmass r) (hRnull r) test
    (fun A => by
      filter_upwards [eventually_clopen_fibre (atTop ⊓ 𝓟 (pool r)) coord hsep
        (pR r) (VR r) (hRE r) A.val.isClopen] with k hk
      intro x y hx hy hxy
      have heq := hk x y hx hy hxy
      change (A.val : Set K).boolIndicator x = (A.val : Set K).boolIndicator y
      simp only [Set.boolIndicator, heq])
    (hRref r) (Measure.dirac z) (hRdis r) (Finset.univ.sup (h.m r))
    ((1 / 2 : ℝ) ^ q) ((1 : ℝ) / 128 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ q)
    (by positivity) (by positivity)
  choose m hmPool hmM hmSmall hmE hmMarginal using hex
  let c : OrderedColumn Rows K := ⟨n, H, F, m⟩
  have hmAvoid (r : Rows) : z ∉ pR r ⁻¹' VR r (m r) := by
    intro hz
    have hval : (Measure.dirac z).real (pR r ⁻¹' VR r (m r)) = 1 := by
      simp only [Measure.real, Measure.dirac_apply_of_mem hz, ENNReal.toReal_one]
    have hp1 : (1 / 2 : ℝ) ^ code r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp2 : (1 / 2 : ℝ) ^ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp0 : 0 ≤ (1 / 2 : ℝ) ^ q := by positivity
    have hprod := mul_le_mul_of_nonneg_right hp1 hp0
    have hs := hmSmall r
    rw [hval] at hs
    nlinarith
  refine ⟨c, ?_, hmAvoid, hFH, (R : Set K), rfl, ?_⟩
  · refine ⟨?_, hnS, ?_, ⟨A, hA, R, rfl, subset_rfl, ?_, ?_, rfl⟩, ?_, ?_⟩
    · cases h
      simp only [OrderedHistory.append, OrderedHistory.restrict, Fin.snoc_castSucc]
    · intro j
      exact (Finset.le_sup (s := Finset.univ) (f := h.n) (Finset.mem_univ j)).trans_lt hnM
    · exact ⟨V n ∩ Q, (hV n).inter hQ, subset_rfl, rfl⟩
    · intro x y hx hy heq
      exact and_congr (iff_of_eq (congrArg (fun w => w ∈ V n ∩ Q) heq))
        (not_congr (hn.2 x y hx.1 hy.1 heq))
    · intro t htmap htmass
      have ht : t.map p = (Measure.dirac (y n)).toSignedMeasure := (htmap.trans (hdirac n))
      have hm : t.totalVariation univ = 1 := by
        rw [htmass, hdirac, SignedMeasure.totalVariation_eq_variation,
          Measure.variation_toSignedMeasure, Measure.dirac_apply_of_mem (mem_univ _)]
      have hone := dirac_lift_apply_of_fibre p hp (y n) t ht hm (H : Set K)
        H.isClopen.isClosed.measurableSet hFH
      rw [hone]
      constructor <;> norm_num
    · intro r
      refine ⟨hmPool r, ?_, hmSmall r, ?_, ?_⟩
      · intro j
        exact (Finset.le_sup (s := Finset.univ) (f := h.m r)
          (Finset.mem_univ j)).trans_lt (hmM r)
      · intro A hAF x y hx hy hxy
        have hb := hmE r ⟨A, hAF⟩ x y hx hy hxy
        change (A : Set K).boolIndicator x = (A : Set K).boolIndicator y at hb
        change x ∈ (A : Set K) ↔ y ∈ (A : Set K)
        rw [(A : Set K).mem_iff_boolIndicator x, (A : Set K).mem_iff_boolIndicator y, hb]
      · intro t htmap htmass
        refine ⟨(hmMarginal r t htmap htmass).1, ?_⟩
        intro A hgen
        -- The finite marginal controls every union of its atoms.
        let f : K → ({A // A ∈ F} → Bool) := fun x C => test C x
        have hf : Continuous f := continuous_pi (fun C => (test C).continuous)
        have heval := (show SignedMeasure _ from t.map f - (muR r).map f).norm_le_totalVariation (f '' A)
        have hpre : f ⁻¹' (f '' A) = A := by
          ext x
          constructor
          · rintro ⟨y, hy, hxy⟩
            exact (hgen y x (fun C hC => by
              have hb := congrFun hxy ⟨C, hC⟩
              change (C : Set K).boolIndicator y = (C : Set K).boolIndicator x at hb
              change y ∈ (C : Set K) ↔ x ∈ (C : Set K)
              rw [(C : Set K).mem_iff_boolIndicator y,
                (C : Set K).mem_iff_boolIndicator x, hb])).mp hy
          · exact fun hx => ⟨x, hx, rfl⟩
        have hmA : MeasurableSet (f '' A) := (isClopen_discrete _).isClosed.measurableSet
        rw [_root_.sub_apply, VectorMeasure.map_apply _ hf.measurable hmA,
          VectorMeasure.map_apply _ hf.measurable hmA, hpre, Real.norm_eq_abs] at heval
        exact (heval.trans (measureReal_mono (subset_univ _) (measure_ne_top _ _))).trans_lt
          (hmMarginal r t htmap htmass).1
  · ext x
    simp only [R, TopologicalSpace.Clopens.coe_mk, mem_iUnion]
    constructor
    · rintro ⟨r, hr, j, hx⟩
      exact ⟨⟨r, (hA r).mp hr⟩, j, hx⟩
    · rintro ⟨r, j, hx⟩
      exact ⟨r.val, (hA r.val).mpr r.property, j, hx⟩

end D5.S3.Topology.Measures.SignedDelayedSplit
