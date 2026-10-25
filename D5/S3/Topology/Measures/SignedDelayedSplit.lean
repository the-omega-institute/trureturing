/- GID: D5/S3/Topology/Measures/SignedDelayedSplit
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedDelayedSplit
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Original parity pools and delayed whole-fibre ordered splitting -/

import D5.S3.Topology.Measures.SignedSplitSuccessor

/-! Delayed pools are chosen from born data and used by one ordered split. -/

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

/-- The two subsequences are selected inside the original source reservoirs.
Convergence concerns every point of the actual fibre, rather than a chosen lift. -/
theorem exists_delayed_fibre_pools [FirstCountableTopology K]
    {Γ : Type*} (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (p : K → L) (hp : Continuous p) (honto : Function.Surjective p)
    (V : ℕ → Set L) (y : ℕ → L) (hy : ∀ n, y n ∈ V n)
    (Q : Set L) (hQ : IsClopen Q) (hyQ : ∀ n, y n ∈ Q)
    (I J : Set ℕ) (N : Fin 2 → Set ℕ) (hJI : J ⊆ I)
    (hJN : ∀ e, (J ∩ N e).Infinite)
    (hE : ∀ c, ∀ᶠ n in atTop ⊓ 𝓟 I, ∀ x z,
      p x ∈ V n → p z ∈ V n → p x = p z → coord c x = coord c z) :
    ∃ (f : ℕ → K) (S : Fin 2 → Set ℕ) (z : Fin 2 → K),
      (∀ n, p (f n) = y n) ∧
      (∀ e, S e ⊆ J ∩ N e) ∧ (∀ e, (S e).Infinite) ∧
      (∀ e, p (z e) ∈ Q) ∧
      (∀ e, Tendsto f (atTop ⊓ 𝓟 (S e)) (𝓝 (z e))) ∧
      ∀ e (A : Set K), IsClopen A → z e ∈ A →
        ∀ᶠ n in atTop ⊓ 𝓟 (S e), p ⁻¹' {y n} ⊆ A := by
  classical
  choose f hf using fun n => honto (y n)
  have hex (e : Fin 2) : ∃ (S : Set ℕ) (z : K), S ⊆ J ∩ N e ∧ S.Infinite ∧
      p z ∈ Q ∧ Tendsto f (atTop ⊓ 𝓟 S) (𝓝 z) ∧
      ∀ A : Set K, IsClopen A → z ∈ A →
        ∀ᶠ n in atTop ⊓ 𝓟 S, p ⁻¹' {y n} ⊆ A := by
    letI : Infinite ↥(J ∩ N e) := Set.infinite_coe_iff.mpr (hJN e)
    let enum := Nat.orderEmbeddingOfSet (J ∩ N e)
    have henum : ∀ k, enum k ∈ J ∩ N e := fun k =>
      Nat.orderEmbeddingOfSet_range (J ∩ N e) ▸ Set.mem_range_self k
    obtain ⟨z, phi, hphi, hconv⟩ := CompactSpace.tendsto_subseq (fun k => f (enum k))
    let seq : ℕ → ℕ := fun k => enum (phi k)
    have hseq : StrictMono seq := enum.strictMono.comp hphi
    let S : Set ℕ := Set.range seq
    have hsub : S ⊆ J ∩ N e := by rintro _ ⟨k, rfl⟩; exact henum (phi k)
    have hzQ : p z ∈ Q := by
      apply (hQ.isClosed.preimage hp).mem_of_tendsto hconv
      exact Eventually.of_forall fun k => by
        change p (f (enum (phi k))) ∈ Q
        rw [hf]
        exact hyQ _
    have hfconv : Tendsto f (atTop ⊓ 𝓟 S) (𝓝 z) := by
      apply tendsto_def.mpr
      intro A hA
      obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hconv hA)
      apply eventually_inf_principal.mpr
      filter_upwards [eventually_ge_atTop (seq k₀)] with n hn hnS
      obtain ⟨k, rfl⟩ := hnS
      exact hk₀ k (hseq.le_iff_le.mp hn)
    refine ⟨S, z, hsub, Set.infinite_range_of_injective hseq.injective, hzQ, hfconv, ?_⟩
    intro A hA hzA
    have hfA : ∀ᶠ n in atTop ⊓ 𝓟 S, f n ∈ A := hfconv (hA.isOpen.mem_nhds hzA)
    have hEA := (eventually_clopen_fibre (atTop ⊓ 𝓟 I) coord hsep p V hE hA).filter_mono
      (inf_le_inf le_rfl (Filter.principal_mono.mpr (hsub.trans (inter_subset_left.trans hJI))))
    filter_upwards [hfA, hEA] with n hn hEn
    intro x hx
    have hpx : p x = y n := hx
    exact (hEn x (f n) (hpx.symm ▸ hy n) (hf n ▸ hy n)
      (hpx.trans (hf n).symm)).mpr hn
  choose S z hsub hinf hz hconv hfull using hex
  exact ⟨f, S, z, hf, hsub, hinf, hz, hconv, hfull⟩

/-- Internal equal/distinct alternative. Column parity is independent of the
original reservoir parity in the distinct-point branch. -/
theorem exists_delayed_pool_plan [FirstCountableTopology K]
    [T2Space K] [TotallyDisconnectedSpace K]
    {Γ : Type*} (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (p : K → L) (hp : Continuous p) (honto : Function.Surjective p)
    (V : ℕ → Set L) (y : ℕ → L) (hy : ∀ n, y n ∈ V n)
    (Q : Set L) (hQ : IsClopen Q) (hyQ : ∀ n, y n ∈ Q)
    (I J : Set ℕ) (N : Fin 2 → Set ℕ) (hJI : J ⊆ I)
    (hJN : ∀ e, (J ∩ N e).Infinite) (hN : Disjoint (N 0) (N 1))
    (hE : ∀ c, ∀ᶠ n in atTop ⊓ 𝓟 I, ∀ x z,
      p x ∈ V n → p z ∈ V n → p x = p z → coord c x = coord c z) :
    ∃ (T : Fin 2 → Set ℕ) (z : K),
      (∀ e, (T e).Infinite) ∧ (∀ e, T e ⊆ I) ∧ p z ∈ Q ∧
      (∀ e (A : Set K), IsClopen A → z ∈ A →
        ∀ᶠ n in atTop ⊓ 𝓟 (T e), p ⁻¹' {y n} ⊆ A) ∧
      ((∀ e, T e ⊆ J ∩ N e) ∨
        ∃ (M : Fin 2 → Set ℕ) (C : TopologicalSpace.Clopens K),
          (∀ e, (M e).Infinite) ∧ (∀ e, M e ⊆ J ∩ N e) ∧
          Disjoint (T 0 ∪ T 1) (M 0 ∪ M 1) ∧
          (∀ n ∈ M 0, p ⁻¹' {y n} ⊆ (C : Set K)) ∧
          (∀ n ∈ M 1, p ⁻¹' {y n} ⊆ (C : Set K)ᶜ)) := by
  classical
  obtain ⟨f, S, z, _, hsub, hinf, hzQ, _, hfull⟩ :=
    exists_delayed_fibre_pools coord hsep p hp honto V y hy Q hQ hyQ I J N hJI hJN hE
  by_cases heq : z 0 = z 1
  · refine ⟨S, z 0, hinf, (fun e => (hsub e).trans (inter_subset_left.trans hJI)), hzQ 0,
      ?_, Or.inl hsub⟩
    intro e A hA hzA
    have hze : z e = z 0 := by
      fin_cases e
      · rfl
      · exact heq.symm
    exact hfull e A hA (hze.symm ▸ hzA)
  · obtain ⟨C, hC, hz0, hz1⟩ := exists_isClopen_of_totally_separated heq
    have ht0 := eventually_inf_principal.mp (hfull 0 C hC hz0)
    have ht1 := eventually_inf_principal.mp (hfull 1 Cᶜ hC.compl hz1)
    obtain ⟨b0, hb0⟩ := eventually_atTop.mp ht0
    obtain ⟨b1, hb1⟩ := eventually_atTop.mp ht1
    let S0 := S 0 \ Iio b0
    let S1 := S 1 \ Iio b1
    have hS0 : S0.Infinite := (hinf 0).sdiff (Set.finite_Iio b0)
    have hS1 : S1.Infinite := (hinf 1).sdiff (Set.finite_Iio b1)
    letI : Infinite ↥S0 := Set.infinite_coe_iff.mpr hS0
    let enum : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet S0
    have hrange : Set.range enum = S0 := Nat.orderEmbeddingOfSet_range S0
    let R : Set ℕ := Set.range (fun k => enum (2 * k + 1))
    let M0 : Set ℕ := Set.range (fun k => enum (2 * k))
    have hRsub : R ⊆ S0 := by
      rintro _ ⟨k, rfl⟩
      exact hrange ▸ Set.mem_range_self _
    have hMsub : M0 ⊆ S0 := by
      rintro _ ⟨k, rfl⟩
      exact hrange ▸ Set.mem_range_self _
    have hRinf : R.Infinite := Set.infinite_range_of_injective
      (enum.injective.comp (fun a b h => by omega))
    have hMinf : M0.Infinite := Set.infinite_range_of_injective
      (enum.injective.comp (fun a b h => by omega))
    let M : Fin 2 → Set ℕ := ![M0, S1]
    have hMsource : ∀ e, M e ⊆ J ∩ N e := by
      intro e
      fin_cases e
      · exact hMsub.trans (sdiff_subset.trans (hsub 0))
      · exact sdiff_subset.trans (hsub 1)
    have hdisR : Disjoint R (M0 ∪ S1) := by
      rw [Set.disjoint_left]
      intro n hnR hnM
      rcases hnM with hn0 | hn1
      · obtain ⟨k, hk⟩ := hnR
        obtain ⟨j, hj⟩ := hn0
        have := enum.injective (hk.trans hj.symm)
        omega
      · exact Set.disjoint_left.mp hN
          ((hsub 0 (hRsub hnR).1).2) ((hsub 1 hn1.1).2)
    refine ⟨fun _ => R, z 0, (fun _ => hRinf),
      (fun _ => hRsub.trans (sdiff_subset.trans ((hsub 0).trans
        (inter_subset_left.trans hJI)))), hzQ 0, ?_, Or.inr ?_⟩
    · intro _ A hA hzA
      exact (hfull 0 A hA hzA).filter_mono
        (inf_le_inf le_rfl (Filter.principal_mono.mpr (hRsub.trans sdiff_subset)))
    · refine ⟨M, ⟨C, hC⟩, ?_, hMsource, ?_, ?_, ?_⟩
      · intro e
        fin_cases e
        · exact hMinf
        · exact hS1
      · simpa only [union_self, M, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one] using hdisR
      · intro n hn
        have hn0 : n ∈ S0 := hMsub hn
        exact hb0 n (le_of_not_gt hn0.2) hn0.1
      · intro n hn
        have hn1 : n ∈ S1 := hn
        exact hb1 n (le_of_not_gt hn1.2) hn1.1

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
private theorem common_source_on_split
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
private theorem exists_literal_delayed_column
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

set_option maxHeartbeats 800000 in
/-- A delayed finite construction uses the original two parity pools. Each
column fixes its target and clopen before choosing all auxiliary signed
indices. The very same closed split separates the full target fibres,
retains every auxiliary finite signed estimate and satisfies signed G. -/
theorem exists_parity_ordered_split [CompactSpace L] [ZeroDimensionalSpace L]
    [T2Space K] [SecondCountableTopology K]
    [TopologicalSpace.MetrizableSpace K] [TotallyDisconnectedSpace K]
    {Rows : Type w} {Γ : Type*}
    (code : Rows → ℕ) (hcode : Function.Injective code)
    (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (B : ℕ → TopologicalSpace.Clopens K) (hB : Function.Surjective B) (rho : ℕ → Γ)
    (S : Fin 2 → Set ℕ) (hS : ∀ e, (S e).Infinite)
    (p : K → L) (hp : Continuous p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (Q : Set L) (hQ : IsClopen Q)
    (y : ℕ → L) (hyV : ∀ n, y n ∈ V n) (hyQ : ∀ n, y n ∈ Q)
    (nu : ℕ → SignedMeasure L)
    (hdirac : ∀ n, nu n = (Measure.dirac (y n)).toSignedMeasure)
    (hE : ∀ e c, ∀ᶠ n in atTop ⊓ 𝓟 (S e), ∀ x z,
      p x ∈ V n → p z ∈ V n → p x = p z → coord c x = coord c z)
    (z : K)
    (hWhole : ∀ e (A : Set K), IsClopen A → z ∈ A →
      ∀ᶠ n in atTop ⊓ 𝓟 (S e), p ⁻¹' {y n} ⊆ A)
    (Base : Rows → Type v)
    [∀ r, TopologicalSpace (Base r)] [∀ r, T2Space (Base r)]
    [∀ r, MeasurableSpace (Base r)] [∀ r, BorelSpace (Base r)]
    (pR : ∀ r, K → Base r) (hpR : ∀ r, Continuous (pR r))
    (hpRsurj : ∀ r, Function.Surjective (pR r))
    (VR : ∀ r, ℕ → Set (Base r)) (hVR : ∀ r n, IsClopen (VR r n))
    (nuR : ∀ r, Γ → ℕ → SignedMeasure (Base r))
    (hRbound : ∀ r d n, (nuR r d n).totalVariation.real univ ≤ 1)
    (sR : Rows → Γ → ℕ → SignedMeasure K) (muR : Rows → Γ → SignedMeasure K)
    (hsRmap : ∀ r d n, (sR r d n).map (pR r) = nuR r d n)
    (hsRmass : ∀ r d n, (sR r d n).totalVariation univ = (nuR r d n).totalVariation univ)
    (hRnull : ∀ r d n, (nuR r d n).totalVariation (VR r n)ᶜ = 0)
    (pool : Rows → ℕ → Set ℕ) (hpool : ∀ r q, (pool r q).Infinite)
    (hRE : ∀ r q c, ∀ᶠ n in atTop ⊓ 𝓟 (pool r q), ∀ x z,
      pR r x ∈ VR r n → pR r z ∈ VR r n → pR r x = pR r z →
        coord c x = coord c z)
    (hRref : ∀ r q, Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR r (rho q) n)).toWeakDual)
      (atTop ⊓ 𝓟 (pool r q)) (𝓝 (NormPreservingLifts.signedFunctional (muR r (rho q))).toWeakDual))
    (hRdis : ∀ r, Pairwise (fun n m => Disjoint (pR r ⁻¹' VR r n) (pR r ⁻¹' VR r m)))
    (hTdis : Pairwise (fun n m => Disjoint (p ⁻¹' V n) (p ⁻¹' V m))) :
    ∃ (history : ∀ q, OrderedHistory Rows K q) (c : ℕ → OrderedColumn Rows K),
      (∀ q, history (q + 1) = (history q).append (c q)) ∧
      (∀ q, (c q).Spec code (history q) B (S ⟨q % 2, Nat.mod_lt q (by decide)⟩)
        p (fun n => V n ∩ Q) nu (Measure.dirac z) Base pR VR
        (fun r => nuR r (rho q)) (fun r => muR r (rho q)) (fun r => pool r q)) ∧
      StrictMono (fun q => (c q).n) ∧ (∀ r, StrictMono (fun q => (c q).m r)) ∧
      (∀ j q, j ≤ q → (c j).H ∈ (c q).F ∧ B j ∈ (c q).F) ∧
      (∀ q, ∃ R : Set K, ((c q).H : Set K) = p ⁻¹' (V (c q).n ∩ Q) \ R ∧
        R = ⋃ r : {r // code r < q}, ⋃ j : Fin q,
          pR r.val ⁻¹' VR r.val ((history q).m r.val j)) ∧
      ∃ (Y Z : Set K) (hclosed : IsClosed (splitCarrier Y Z)),
        letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
        IsClosed Y ∧ IsClosed Z ∧ Y ∪ Z = univ ∧
        Function.Surjective (fun x : splitCarrier Y Z => x.1.1) ∧
        Z ⊆ p ⁻¹' Q ∧
        Z = closure (⋃ q : ℕ, if q % 2 = 0 then ((c q).H : Set K) else ∅) ∧
        (∀ r q, code r < q →
          Z ∩ (pR r ⁻¹' VR r ((c q).m r)) =
            evenPrefix (fun j => ((c j).H : Set K)) q ∩ (pR r ⁻¹' VR r ((c q).m r)) ∧
          Disjoint (Y ∩ Z) (pR r ⁻¹' VR r ((c q).m r)) ∧
          ∀ x : splitCarrier Y Z, x.1.1 ∈ pR r ⁻¹' VR r ((c q).m r) →
            (x.1.2 = true ↔ x.1.1 ∈ evenPrefix (fun j => ((c j).H : Set K)) q)) ∧
        (∀ r q, code r < q → ∀ x y : splitCarrier Y Z,
          pR r x.1.1 ∈ VR r ((c q).m r) → pR r y.1.1 ∈ VR r ((c q).m r) →
          pR r x.1.1 = pR r y.1.1 → x.1.2 = y.1.2) ∧
        (∀ q, ∀ x z : splitCarrier Y Z,
          p x.1.1 ∈ V (c q).n → p z.1.1 ∈ V (c q).n →
          p x.1.1 = p z.1.1 → x.1.2 = z.1.2) ∧
        (∀ q (x : splitCarrier Y Z), p x.1.1 = y (c q).n →
          (x.1.2 = true ↔ q % 2 = 0)) ∧
        (∀ q (t : SignedMeasure (splitCarrier Y Z)),
          t.map (fun x => p x.1.1) = nu (c q).n →
          t.totalVariation univ = (nu (c q).n).totalVariation univ →
          (q % 2 = 0 → (13 : ℝ) / 48 < t {x | x.1.2 = true} ∧
            (1 : ℝ) / 6 < t {x | x.1.2 = true}) ∧
          (q % 2 ≠ 0 → t {x | x.1.2 = true} = 0)) ∧
        ∀ (r : Rows) (d : Γ) (phi : ℕ → ℕ), StrictMono phi →
          (∀ k, rho (phi k) = d) →
          ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
            Measure.Regular mu.toJordanDecomposition.posPart ∧
            Measure.Regular mu.toJordanDecomposition.negPart ∧
            ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
              (∀ k, (sigma k).map (fun x => pR r x.1.1) = nuR r d ((c (phi k)).m r)) →
              (∀ k, (sigma k).totalVariation univ =
                (nuR r d ((c (phi k)).m r)).totalVariation univ) →
              Tendsto (fun k => (NormPreservingLifts.signedFunctional (sigma k)).toWeakDual)
                atTop (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
  classical
  let VQ : ℕ → Set L := fun n => V n ∩ Q
  have hVQ (n : ℕ) : IsClopen (VQ n) := (hV n).inter hQ
  have hnull (n : ℕ) : (nu n).totalVariation (VQ n)ᶜ = 0 := by
    rw [hdirac, SignedMeasure.totalVariation_eq_variation, Measure.variation_toSignedMeasure,
      Measure.dirac_apply' _ (hVQ n).isClosed.measurableSet.compl,
      Set.indicator_of_notMem (show y n ∉ (VQ n)ᶜ from not_not.mpr ⟨hyV n, hyQ n⟩)]
  have hnullV (n : ℕ) : (nu n).totalVariation (V n)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr inter_subset_left) (hnull n)
  have hEQ (e : Fin 2) (a : Γ) : ∀ᶠ n in atTop ⊓ 𝓟 (S e), ∀ x z,
      p x ∈ VQ n → p z ∈ VQ n → p x = p z → coord a x = coord a z := by
    filter_upwards [hE e a] with n hn
    exact fun x z hx hz hpxz => hn x z hx.1 hz.1 hpxz
  let v : Measure K := Measure.dirac z
  let State (q : ℕ) := {h : OrderedHistory Rows K q //
    ∀ r (j : Fin q), z ∉ pR r ⁻¹' VR r (h.m r j)}
  have hex (q : ℕ) (x : State q) := exists_literal_delayed_column code hcode x.val
    coord hsep B (S ⟨q % 2, Nat.mod_lt q (by decide)⟩) (hS _) p hp V hV Q hQ y hyV hyQ
    nu hdirac z (hWhole _) (hE _) Base pR hpR VR hVR
    (fun r => nuR r (rho q)) (fun r => sR r (rho q))
    (fun r => muR r (rho q)) (fun r => hsRmap r (rho q)) (fun r => hsRmass r (rho q))
    (fun r => hRnull r (rho q)) (fun r => pool r q) (fun r => hpool r q)
    (fun r => hRE r q) (fun r => hRref r q) hRdis x.property
  choose column hcolumn using hex
  let next (q : ℕ) (x : State q) : State (q + 1) :=
    ⟨x.val.append (column q x), by
      intro r j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [OrderedHistory.append, Fin.snoc_last, Fin.val_last] using
          (hcolumn q x).2.1 r
      · simpa only [OrderedHistory.append, Fin.snoc_castSucc, Fin.val_castSucc] using
          x.property r j⟩
  let empty : State 0 := ⟨⟨Fin.elim0, Fin.elim0, Fin.elim0, fun _ => Fin.elim0⟩,
    fun _ j => Fin.elim0 j⟩
  let hist : ∀ q, State q := fun q => Nat.rec empty next q
  let c : ℕ → OrderedColumn Rows K := fun q => column q (hist q)
  have hsuc (q : ℕ) : (hist (q + 1)).val = (hist q).val.append (c q) := rfl
  have hstep (q : ℕ) : (c q).Spec code (hist q).val B (S ⟨q % 2, Nat.mod_lt q (by decide)⟩) p VQ nu v Base pR VR
      (fun r => nuR r (rho q)) (fun r => muR r (rho q)) (fun r => pool r q) := (hcolumn q (hist q)).1
  let get : ∀ {q}, OrderedHistory Rows K q → Fin q → OrderedColumn Rows K :=
    fun {_} h j => ⟨h.n j, h.H j, h.F j, fun r => h.m r j⟩
  have hstable : ∀ q (j : Fin q), get (hist q).val j = c (j : ℕ) := by
    intro q
    induction q with
    | zero => intro j; exact Fin.elim0 j
    | succ q ih =>
      intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [hsuc]
        change OrderedColumn.mk _ _ _ _ = c q
        simp only [OrderedHistory.append, Fin.snoc_last]
      · rw [hsuc]
        simpa only [get, OrderedHistory.append, Fin.snoc_castSucc, Fin.val_castSucc] using ih j
  have hn : StrictMono (fun q => (c q).n) := by
    intro q s hqs
    have hs := (hstep s).2.2.1 ⟨q, hqs⟩
    have heq := congrArg OrderedColumn.n (hstable s ⟨q, hqs⟩)
    change (hist s).val.n ⟨q, hqs⟩ = (c q).n at heq
    rw [heq] at hs
    exact hs
  have hm : ∀ r, StrictMono (fun q => (c q).m r) := by
    intro r q s hqs
    have hs := ((hstep s).2.2.2.2.2 r).2.1 ⟨q, hqs⟩
    have heq := congrArg (fun t => t.m r) (hstable s ⟨q, hqs⟩)
    change (hist s).val.m r ⟨q, hqs⟩ = (c q).m r at heq
    rw [heq] at hs
    exact hs
  have htests (j q : ℕ) (hjq : j ≤ q) : (c j).H ∈ (c q).F ∧ B j ∈ (c q).F := by
    have hself (k : ℕ) : (c k).H ∈ (c k).F ∧ B k ∈ (c k).F := by
      obtain ⟨_, _, _, _, _, _, _, hF⟩ := (hstep k).2.2.2.1
      rw [hF]
      simp
    rcases eq_or_lt_of_le hjq with rfl | hjq
    · exact hself j
    · obtain ⟨_, _, _, _, _, _, _, hF⟩ := (hstep q).2.2.2.1
      have hsubF : (c j).F ⊆ (c q).F := by
        intro A hAF
        rw [hF]
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        have heq := congrArg OrderedColumn.F (hstable q ⟨j, hjq⟩)
        change (hist q).val.F ⟨j, hjq⟩ = (c j).F at heq
        exact ⟨⟨j, hjq⟩, Finset.mem_univ _, heq.symm ▸ hAF⟩
      exact ⟨hsubF (hself j).1, hsubF (hself j).2⟩
  have havoid : ∀ r q s, code r < q → q < s →
      Disjoint ((c s).H : Set K) (pR r ⁻¹' VR r ((c q).m r)) := by
    intro r q s hr hqs
    obtain ⟨A, hA, R, hR, hsub, _, _, _⟩ := (hstep s).2.2.2.1
    rw [Set.disjoint_left]
    intro x hxH hxW
    apply (hsub hxH).2
    rw [hR]
    have heq := congrArg (fun t => t.m r) (hstable s ⟨q, hqs⟩)
    refine mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨(hA r).mpr (hr.trans hqs),
      mem_iUnion.mpr ⟨⟨q, hqs⟩, ?_⟩⟩⟩
    change pR r x ∈ VR r ((hist s).val.m r ⟨q, hqs⟩)
    change (hist s).val.m r ⟨q, hqs⟩ = (c q).m r at heq
    rwa [heq]
  have hHT (q : ℕ) : ((c q).H : Set K) ⊆ p ⁻¹' V (c q).n := by
    obtain ⟨_, _, _, _, hsub, _, _, _⟩ := (hstep q).2.2.2.1
    exact fun x hx => (hsub hx).1.1
  have hdis : Pairwise (fun q s => Disjoint (p ⁻¹' V (c q).n) (p ⁻¹' V (c s).n)) := by
    intro q s hqs
    exact hTdis (fun h => hqs (hn.injective h))
  obtain ⟨Y, Z, hY, hZ, hcov, hZdef, hYdef, hclosed, hsurj, haux, htarget⟩ :=
    exists_closed_split_of_ordered_exclusion code (fun q => ((c q).H : Set K))
      (fun q => (c q).H.isClopen) (fun r q => pR r ⁻¹' VR r ((c q).m r))
      (fun r q => (hVR r _).preimage (hpR r)) havoid
      (fun q => p ⁻¹' V (c q).n) (fun q => (hV _).preimage hp) hdis hHT

  have hQH (q : ℕ) : ((c q).H : Set K) ⊆ p ⁻¹' Q := by
    obtain ⟨_, _, _, _, hsub, _, _, _⟩ := (hstep q).2.2.2.1
    exact fun x hx => (hsub hx).1.2
  have hZQ : Z ⊆ p ⁻¹' Q := by
    rw [hZdef]
    apply closure_minimal _ (hQ.isClosed.preimage hp)
    rintro x hx
    obtain ⟨q, hx⟩ := mem_iUnion.mp hx
    obtain ⟨_, hx⟩ := mem_iUnion.mp hx
    exact hQH q hx
  have hHE (q : ℕ) : ∀ x z, p x ∈ V (c q).n → p z ∈ V (c q).n →
      p x = p z → (x ∈ (c q).H ↔ z ∈ (c q).H) := by
    intro x z hx hz heq
    by_cases hxQ : p x ∈ Q
    · have hzQ : p z ∈ Q := heq ▸ hxQ
      obtain ⟨_, _, _, _, _, _, hconst, _⟩ := (hstep q).2.2.2.1
      exact hconst x z ⟨hx, hxQ⟩ ⟨hz, hzQ⟩ heq
    · have hzQ : p z ∉ Q := heq ▸ hxQ
      exact iff_of_false (fun h => hxQ (hQH q h)) (fun h => hzQ (hQH q h))
  have hnewTarget : ∀ q, ∀ x z : splitCarrier Y Z,
      p x.1.1 ∈ V (c q).n → p z.1.1 ∈ V (c q).n →
      p x.1.1 = p z.1.1 → x.1.2 = z.1.2 := by
    intro q x z hx hz heq
    apply bool_eq_of_true_iff
    rw [(htarget q).2.2 x hx, (htarget q).2.2 z hz]
    exact and_congr Iff.rfl (hHE q x.1.1 z.1.1 hx hz heq)
  have hfull (q : ℕ) : p ⁻¹' {y (c q).n} ⊆ ((c q).H : Set K) :=
    (hcolumn q (hist q)).2.2.1
  have hfibre (q : ℕ) (x : splitCarrier Y Z) (hx : p x.1.1 = y (c q).n) :
      x.1.2 = true ↔ q % 2 = 0 := by
    have hxV : x.1.1 ∈ p ⁻¹' V (c q).n := by
      change p x.1.1 ∈ V (c q).n
      rw [hx]
      exact hyV _
    rw [(htarget q).2.2 x hxV]
    exact and_iff_left (hfull q hx)
  letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
  let projection : splitCarrier Y Z → K := fun x => x.1.1
  have hprojection : Continuous projection := continuous_fst.comp continuous_subtype_val
  let side : Set (splitCarrier Y Z) := {x | x.1.2 = true}
  have hside : IsClopen side := (isClopen_discrete ({true} : Set Bool)).preimage
    (continuous_snd.comp continuous_subtype_val)
  have hG : ∀ q (t : SignedMeasure (splitCarrier Y Z)),
      t.map (p ∘ projection) = nu (c q).n →
      t.totalVariation univ = (nu (c q).n).totalVariation univ →
      (q % 2 = 0 → (13 : ℝ) / 48 < t side ∧ (1 : ℝ) / 6 < t side) ∧ (q % 2 ≠ 0 → t side = 0) := by
    intro q t htmap htmass
    let W : Set (splitCarrier Y Z) := (p ∘ projection) ⁻¹' V (c q).n
    have hW : IsClopen W := (hV _).preimage (hp.comp hprojection)
    have htNull : t.totalVariation Wᶜ = 0 := support_null (p ∘ projection)
      (hp.comp hprojection) t (nu (c q).n) htmap htmass (hV _) (hnullV _)
    have htcut := apply_eq_inter_of_null_compl t hside.isClosed.measurableSet
      hW.isClosed.measurableSet htNull
    constructor
    · intro heven
      have htrace : side ∩ W = projection ⁻¹' ((c q).H : Set K) := by
        ext x
        constructor
        · rintro ⟨hx, hxW⟩
          exact ((htarget q).2.2 x hxW).mp hx |>.2
        · intro hxH
          have hxW : x ∈ W := hHT q hxH
          exact ⟨((htarget q).2.2 x hxW).mpr ⟨heven, hxH⟩, hxW⟩
      have hmid := map_mass_through_factor projection hprojection.measurable p hp.measurable
        t (nu (c q).n) htmap htmass
      have hlarge := (hstep q).2.2.2.2.1 (t.map projection) hmid.1 hmid.2
      rw [htcut, htrace, ← VectorMeasure.map_apply t hprojection.measurable
        (c q).H.isClopen.isClosed.measurableSet]
      exact hlarge
    · intro hodd
      have htrace : side ∩ W = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxW⟩
        exact hodd (((htarget q).2.2 x hxW).mp hx).1
      rw [htcut, htrace, t.empty]

  let U : ℕ → Set K := evenPrefix (fun q => ((c q).H : Set K))
  have hUclopen (q : ℕ) : IsClopen (U q) :=
    evenPrefix_clopen _ (fun j => (c j).H.isClopen) q
  have hUmono : Monotone U := evenPrefix_mono _
  have hGenU (q : ℕ) (x y : K)
      (hxy : ∀ C ∈ (c q).F, x ∈ C ↔ y ∈ C) : x ∈ U q ↔ y ∈ U q := by
    simp only [U, evenPrefix, mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hxH⟩
      refine ⟨j, hj, ?_⟩
      by_cases heven : j % 2 = 0
      · simp only [ite_eq_left heven] at hxH ⊢
        exact (hxy (c j).H (htests j q (by omega)).1).mp hxH
      · simpa only [ite_eq_right heven, mem_empty_iff_false] using hxH
    · rintro ⟨j, hj, hyH⟩
      refine ⟨j, hj, ?_⟩
      by_cases heven : j % 2 = 0
      · simp only [ite_eq_left heven] at hyH ⊢
        exact (hxy (c j).H (htests j q (by omega)).1).mpr hyH
      · simpa only [ite_eq_right heven, mem_empty_iff_false] using hyH
  have hnewAux (r : Rows) (q : ℕ) (hq : code r < q)
      (x y : splitCarrier Y Z)
      (hx : pR r x.1.1 ∈ VR r ((c q).m r))
      (hy : pR r y.1.1 ∈ VR r ((c q).m r))
      (hxy : pR r x.1.1 = pR r y.1.1) : x.1.2 = y.1.2 := by
    apply bool_eq_of_true_iff
    rw [(haux r q hq).2.2.2 x hx, (haux r q hq).2.2.2 y hy]
    apply hGenU q
    intro A hA
    exact ((hstep q).2.2.2.2.2 r).2.2.2.1 A hA x.1.1 y.1.1 hx hy hxy
  have hSideRow (r : Rows) (q : ℕ) (hq : code r < q)
      (t : SignedMeasure (splitCarrier Y Z))
      (htmap : t.map (pR r ∘ projection) = nuR r (rho q) ((c q).m r))
      (htmass : t.totalVariation univ = (nuR r (rho q) ((c q).m r)).totalVariation univ)
      (A : Set K) (hA : IsClopen A) :
      t (side ∩ projection ⁻¹' A) = (t.map projection) (A ∩ U q) := by
    let W : Set (splitCarrier Y Z) := (pR r ∘ projection) ⁻¹' VR r ((c q).m r)
    have hW : IsClopen W := (hVR r _).preimage ((hpR r).comp hprojection)
    have htNull : t.totalVariation Wᶜ = 0 := support_null (pR r ∘ projection)
      ((hpR r).comp hprojection) t (nuR r (rho q) ((c q).m r)) htmap htmass
      (hVR r _) (hRnull r (rho q) _)
    have hLeft : MeasurableSet (side ∩ projection ⁻¹' A) :=
      (hside.inter (hA.preimage hprojection)).isClosed.measurableSet
    have hRight : MeasurableSet (projection ⁻¹' (A ∩ U q)) :=
      ((hA.inter (hUclopen q)).preimage hprojection).isClosed.measurableSet
    have heq : (side ∩ projection ⁻¹' A) ∩ W = projection ⁻¹' (A ∩ U q) ∩ W := by
      ext x
      constructor
      · rintro ⟨⟨hxSide, hxA⟩, hxW⟩
        exact ⟨⟨hxA, ((haux r q hq).2.2.2 x hxW).mp hxSide⟩, hxW⟩
      · rintro ⟨⟨hxA, hxU⟩, hxW⟩
        exact ⟨⟨((haux r q hq).2.2.2 x hxW).mpr hxU, hxA⟩, hxW⟩
    calc
      t (side ∩ projection ⁻¹' A) = t ((side ∩ projection ⁻¹' A) ∩ W) :=
        apply_eq_inter_of_null_compl t hLeft hW.isClosed.measurableSet htNull
      _ = t (projection ⁻¹' (A ∩ U q) ∩ W) := congrArg t heq
      _ = t (projection ⁻¹' (A ∩ U q)) :=
        (apply_eq_inter_of_null_compl t hRight hW.isClosed.measurableSet htNull).symm
      _ = (t.map projection) (A ∩ U q) :=
        (VectorMeasure.map_apply t hprojection.measurable
          (hA.inter (hUclopen q)).isClosed.measurableSet).symm
  have hF : ∀ (r : Rows) (d : Γ) (phi : ℕ → ℕ), StrictMono phi →
      (∀ k, rho (phi k) = d) → ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
      (∀ k, (sigma k).map (pR r ∘ projection) = nuR r d ((c (phi k)).m r)) →
      (∀ k, (sigma k).totalVariation univ = (nuR r d ((c (phi k)).m r)).totalVariation univ) →
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        Tendsto (fun k => (NormPreservingLifts.signedFunctional (sigma k)).toWeakDual)
          atTop (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    intro r d phi hphi hlabel sigma hmap hmass
    let mid : ℕ → SignedMeasure K := fun k => (sigma k).map projection
    have hmid (k : ℕ) := map_mass_through_factor projection hprojection.measurable
      (pR r) (hpR r).measurable (sigma k) (nuR r d ((c (phi k)).m r)) (hmap k) (hmass k)
    have hmap' (k : ℕ) : (sigma k).map (pR r ∘ projection) =
        nuR r (rho (phi k)) ((c (phi k)).m r) := by rw [hlabel k]; exact hmap k
    have hmass' (k : ℕ) : (sigma k).totalVariation univ =
        (nuR r (rho (phi k)) ((c (phi k)).m r)).totalVariation univ := by
      rw [hlabel k]; exact hmass k
    have herror (k : ℕ) (A : Set K)
        (hgen : ∀ x y, (∀ C ∈ (c (phi k)).F, x ∈ C ↔ y ∈ C) → (x ∈ A ↔ y ∈ A)) :
        |mid k A - muR r d A| < (1 / 2 : ℝ) ^ phi k := by
      have hm := hmid k
      have hmmap : (mid k).map (pR r) = nuR r (rho (phi k)) ((c (phi k)).m r) := by
        rw [hlabel k]; exact hm.1
      have hmmass : (mid k).totalVariation univ =
          (nuR r (rho (phi k)) ((c (phi k)).m r)).totalVariation univ := by
        rw [hlabel k]; exact hm.2
      have he := (((hstep (phi k)).2.2.2.2.2 r).2.2.2.2 (mid k) hmmap hmmass).2 A hgen
      simpa only [hlabel k] using he
    have heps : Tendsto (fun k => (1 / 2 : ℝ) ^ phi k) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).comp hphi.tendsto_atTop
    have hbound : ∀ k, (sigma k).totalVariation.real univ ≤ 1 := by
      intro k
      simpa only [Measure.real, hmass k] using hRbound r d ((c (phi k)).m r)
    letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
    apply SignedSplitReferenceConvergence.exists_signed_limit_of_reference Y Z hY hZ
      1 (by norm_num) sigma hbound (muR r d) (fun k => U (phi k))
      (fun k => (hUclopen _).isClosed.measurableSet) (hUmono.comp hphi.monotone)
      (fun k => (1 / 2 : ℝ) ^ phi k) heps
    · intro A hA
      obtain ⟨j, hj⟩ := hB ⟨A, hA⟩
      have herrorA : ∀ᶠ k in atTop, |mid k A - muR r d A| ≤ (1 / 2 : ℝ) ^ phi k := by
        filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop j)] with k hk
        have hAF : (⟨A, hA⟩ : TopologicalSpace.Clopens K) ∈ (c (phi k)).F := by
          simpa only [hj] using (htests j (phi k) hk).2
        apply (herror k A ?_).le
        intro x y hxy
        exact hxy ⟨A, hA⟩ hAF
      have hz : Tendsto (fun k => mid k A - muR r d A) atTop (𝓝 0) :=
        squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using herrorA) heps
      change Tendsto (fun k => mid k A) atTop (𝓝 (muR r d A))
      simpa only [sub_add_cancel, zero_add] using hz.add_const (muR r d A)
    · intro A hA
      obtain ⟨j, hj⟩ := hB ⟨A, hA⟩
      filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop j),
        hphi.tendsto_atTop.eventually (eventually_gt_atTop (code r))] with k hk hcodek
      have hAF : (⟨A, hA⟩ : TopologicalSpace.Clopens K) ∈ (c (phi k)).F := by
        simpa only [hj] using (htests j (phi k) hk).2
      change |sigma k (side ∩ projection ⁻¹' A) - muR r d (A ∩ U (phi k))| ≤ _
      rw [hSideRow r (phi k) hcodek (sigma k) (hmap' k) (hmass' k) A hA]
      apply (herror k (A ∩ U (phi k)) ?_).le
      intro x y hxy
      exact and_congr (hxy ⟨A, hA⟩ hAF) (hGenU (phi k) x y hxy)
  have hFuniform : ∀ (r : Rows) (d : Γ) (phi : ℕ → ℕ), StrictMono phi →
      (∀ k, rho (phi k) = d) →
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ k, (sigma k).map (pR r ∘ projection) = nuR r d ((c (phi k)).m r)) →
          (∀ k, (sigma k).totalVariation univ = (nuR r d ((c (phi k)).m r)).totalVariation univ) →
          Tendsto (fun k => (NormPreservingLifts.signedFunctional (sigma k)).toWeakDual)
            atTop (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    intro r d phi hphi hlabel
    letI : MetricSpace (splitCarrier Y Z) := TopologicalSpace.metrizableSpaceMetric _
    choose ref hrefmap hrefmass using fun k =>
      NormPreservingLiftExistence.exists_norm_preserving_lift (pR r ∘ projection)
        ((hpR r).comp hprojection) ((hpRsurj r).comp hsurj)
        (nuR r d ((c (phi k)).m r))
    obtain ⟨mu, hbound, hpos, hneg, hrefconv⟩ := hF r d phi hphi hlabel ref hrefmap hrefmass
    refine ⟨mu, hbound, hpos, hneg, ?_⟩
    intro sigma hmap hmass
    obtain ⟨mu', _, _, _, hconv⟩ := hF r d phi hphi hlabel sigma hmap hmass
    let mix : ℕ → SignedMeasure (splitCarrier Y Z) :=
      fun k => if k % 2 = 0 then ref k else sigma k
    have hmixmap (k : ℕ) : (mix k).map (pR r ∘ projection) = nuR r d ((c (phi k)).m r) := by
      dsimp only [mix]
      split_ifs
      · exact hrefmap k
      · exact hmap k
    have hmixmass (k : ℕ) : (mix k).totalVariation univ =
        (nuR r d ((c (phi k)).m r)).totalVariation univ := by
      dsimp only [mix]
      split_ifs
      · exact hrefmass k
      · exact hmass k
    obtain ⟨mixmu, _, _, _, hmixconv⟩ := hF r d phi hphi hlabel mix hmixmap hmixmass
    have heven : StrictMono (fun k : ℕ => 2 * k) := fun a b hab => by
      change 2 * a < 2 * b
      omega
    have hodd : StrictMono (fun k : ℕ => 2 * k + 1) := fun a b hab => by
      change 2 * a + 1 < 2 * b + 1
      omega
    have heq : (NormPreservingLifts.signedFunctional mu).toWeakDual =
        (NormPreservingLifts.signedFunctional mixmu).toWeakDual := by
      apply tendsto_nhds_unique (hrefconv.comp heven.tendsto_atTop)
      simpa only [Function.comp_def, mix, Nat.mul_mod_right, ite_true] using
        hmixconv.comp heven.tendsto_atTop
    have heq' : (NormPreservingLifts.signedFunctional mu').toWeakDual =
        (NormPreservingLifts.signedFunctional mixmu).toWeakDual := by
      apply tendsto_nhds_unique (hconv.comp hodd.tendsto_atTop)
      simpa [Function.comp_def, mix] using hmixconv.comp hodd.tendsto_atTop
    rwa [heq'.trans heq.symm] at hconv
  refine ⟨fun q => (hist q).val, c, hsuc, hstep, hn, hm, htests,
    (fun q => (hcolumn q (hist q)).2.2.2),
    Y, Z, hclosed, hY, hZ, hcov, hsurj, hZQ, ?_, ?_, hnewAux, hnewTarget, hfibre, hG, hFuniform⟩
  · rw [hZdef]
    congr 1
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨q, hq, hx⟩
      exact ⟨q, by simpa only [if_pos hq] using hx⟩
    · rintro ⟨q, hx⟩
      by_cases hq : q % 2 = 0
      · exact ⟨q, hq, by simpa only [if_pos hq] using hx⟩
      · simpa only [if_neg hq, mem_empty_iff_false] using hx
  · intro r q hq
    exact ⟨(haux r q hq).1, (haux r q hq).2.2.1, (haux r q hq).2.2.2⟩

set_option maxHeartbeats 1200000 in
-- Internal pool selection and the two geometric branches are combined here.
/-- Both cluster cases on one actual split. The target reference, target
pools, source replacement and common source limit are selected internally.
No common-reference or successor-limit premise is supplied by the caller. -/
theorem exists_internal_delayed_split [CompactSpace L] [ZeroDimensionalSpace L]
    [T2Space K] [SecondCountableTopology K]
    [TopologicalSpace.MetrizableSpace K] [TotallyDisconnectedSpace K]
    {Rows : Type w} {Γ : Type*}
    (code : Rows → ℕ) (hcode : Function.Injective code)
    (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (B : ℕ → TopologicalSpace.Clopens K) (hB : Function.Surjective B) (rho : ℕ → Γ)
    (I J : Set ℕ) (N : Fin 2 → Set ℕ)
    (hJI : J ⊆ I) (hJN : ∀ e, (J ∩ N e).Infinite)
    (hN : Disjoint (N 0) (N 1))
    (p : K → L) (hp : Continuous p) (hponto : Function.Surjective p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (Q : Set L) (hQ : IsClopen Q)
    (y : ℕ → L) (hyV : ∀ n, y n ∈ V n) (hyQ : ∀ n, y n ∈ Q)
    (nu : ℕ → SignedMeasure L)
    (hdirac : ∀ n, nu n = (Measure.dirac (y n)).toSignedMeasure)
    (hE : ∀ c, ∀ᶠ n in atTop ⊓ 𝓟 I, ∀ x z,
      p x ∈ V n → p z ∈ V n → p x = p z → coord c x = coord c z)
    (P : Set L) (hP : IsClopen P) (hPQ : Disjoint P Q)
    (sourceNu : ℕ → SignedMeasure L)
    (hSourceBound : ∀ n, (sourceNu n).totalVariation.real univ ≤ 1)
    (hSourceNull : ∀ n, (sourceNu n).totalVariation Pᶜ = 0)
    (hSourceSupport : ∀ n, (sourceNu n).totalVariation (V n)ᶜ = 0)
    (oldSourceF : ∀ t : ℕ → SignedMeasure K,
      (∀ n, (t n).map p = sourceNu n) →
      (∀ n, (t n).totalVariation univ = (sourceNu n).totalVariation univ) →
      ∃ mu : SignedMeasure K, Tendsto
        (fun n => (NormPreservingLifts.signedFunctional (t n)).toWeakDual)
        (atTop ⊓ 𝓟 J) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual))
    (Base : Rows → Type v)
    [∀ r, TopologicalSpace (Base r)] [∀ r, T2Space (Base r)]
    [∀ r, MeasurableSpace (Base r)] [∀ r, BorelSpace (Base r)]
    (pR : ∀ r, K → Base r) (hpR : ∀ r, Continuous (pR r))
    (hpRsurj : ∀ r, Function.Surjective (pR r))
    (VR : ∀ r, ℕ → Set (Base r)) (hVR : ∀ r n, IsClopen (VR r n))
    (nuR : ∀ r, Γ → ℕ → SignedMeasure (Base r))
    (hRbound : ∀ r d n, (nuR r d n).totalVariation.real univ ≤ 1)
    (sR : Rows → Γ → ℕ → SignedMeasure K) (muR : Rows → Γ → SignedMeasure K)
    (hsRmap : ∀ r d n, (sR r d n).map (pR r) = nuR r d n)
    (hsRmass : ∀ r d n, (sR r d n).totalVariation univ = (nuR r d n).totalVariation univ)
    (hRnull : ∀ r d n, (nuR r d n).totalVariation (VR r n)ᶜ = 0)
    (pool : Rows → ℕ → Set ℕ) (hpool : ∀ r q, (pool r q).Infinite)
    (hRE : ∀ r q c, ∀ᶠ n in atTop ⊓ 𝓟 (pool r q), ∀ x z,
      pR r x ∈ VR r n → pR r z ∈ VR r n → pR r x = pR r z →
        coord c x = coord c z)
    (hRref : ∀ r q, Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR r (rho q) n)).toWeakDual)
      (atTop ⊓ 𝓟 (pool r q)) (𝓝 (NormPreservingLifts.signedFunctional (muR r (rho q))).toWeakDual))
    (hRdis : ∀ r, Pairwise (fun n m => Disjoint (pR r ⁻¹' VR r n) (pR r ⁻¹' VR r m)))
    (hTdis : Pairwise (fun n m => Disjoint (p ⁻¹' V n) (p ⁻¹' V m))) :
    ∃ (z : K) (T : Fin 2 → Set ℕ)
      (history : ∀ q, OrderedHistory Rows K q) (c : ℕ → OrderedColumn Rows K)
      (M : Fin 2 → Set ℕ) (Y Z : Set K) (hclosed : IsClosed (splitCarrier Y Z)),
      letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
      (∀ q, history (q + 1) = (history q).append (c q)) ∧
      (∀ q, (c q).Spec code (history q) B (T ⟨q % 2, Nat.mod_lt q (by decide)⟩)
        p (fun n => V n ∩ Q) nu (Measure.dirac z) Base pR VR
        (fun r => nuR r (rho q)) (fun r => muR r (rho q)) (fun r => pool r q)) ∧
      StrictMono (fun q => (c q).n) ∧ (∀ r, StrictMono (fun q => (c q).m r)) ∧
      (∀ j q, j ≤ q → (c j).H ∈ (c q).F ∧ B j ∈ (c q).F) ∧
      (∀ q, ∃ R : Set K, ((c q).H : Set K) = p ⁻¹' (V (c q).n ∩ Q) \ R ∧
        R = ⋃ r : {r // code r < q}, ⋃ j : Fin q,
          pR r.val ⁻¹' VR r.val ((history q).m r.val j)) ∧
      (∀ e, (M e).Infinite) ∧ (∀ e, M e ⊆ J ∩ N e) ∧
      IsClosed Y ∧ IsClosed Z ∧ Y ∪ Z = univ ∧
      Function.Surjective (fun x : splitCarrier Y Z => x.1.1) ∧
      Z ⊆ p ⁻¹' Q ∧
      (∀ r q, code r < q → ∀ x y : splitCarrier Y Z,
        pR r x.1.1 ∈ VR r ((c q).m r) → pR r y.1.1 ∈ VR r ((c q).m r) →
        pR r x.1.1 = pR r y.1.1 → x.1.2 = y.1.2) ∧
      (∀ n ∈ M 0 ∪ M 1, ∀ x y : splitCarrier Y Z,
        p x.1.1 ∈ V n → p y.1.1 ∈ V n → p x.1.1 = p y.1.1 → x.1.2 = y.1.2) ∧
      (∃ C : TopologicalSpace.Clopens (splitCarrier Y Z),
        (∀ n ∈ M 0, ∀ x : splitCarrier Y Z, p x.1.1 = y n → x ∈ C) ∧
        (∀ n ∈ M 1, ∀ x : splitCarrier Y Z, p x.1.1 = y n → x ∉ C)) ∧
      (∀ q (t : SignedMeasure (splitCarrier Y Z)),
        t.map (fun x => p x.1.1) = nu (c q).n →
        t.totalVariation univ = (nu (c q).n).totalVariation univ →
        (q % 2 = 0 → (13 : ℝ) / 48 < t {x | x.1.2 = true} ∧
            (1 : ℝ) / 6 < t {x | x.1.2 = true}) ∧
        (q % 2 ≠ 0 → t {x | x.1.2 = true} = 0)) ∧
      (∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (fun x => p x.1.1) = sourceNu n) →
          (∀ n, (sigma n).totalVariation univ = (sourceNu n).totalVariation univ) →
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
            (atTop ⊓ 𝓟 (M 0 ∪ M 1))
            (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual)) ∧
      ∀ (r : Rows) (d : Γ) (phi : ℕ → ℕ), StrictMono phi →
        (∀ k, rho (phi k) = d) →
        ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
          Measure.Regular mu.toJordanDecomposition.posPart ∧
          Measure.Regular mu.toJordanDecomposition.negPart ∧
          ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
            (∀ k, (sigma k).map (fun x => pR r x.1.1) = nuR r d ((c (phi k)).m r)) →
            (∀ k, (sigma k).totalVariation univ =
              (nuR r d ((c (phi k)).m r)).totalVariation univ) →
            Tendsto (fun k => (NormPreservingLifts.signedFunctional (sigma k)).toWeakDual)
              atTop (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
  classical
  obtain ⟨T, z, hTinf, hTI, _, hWhole, hcase⟩ :=
    exists_delayed_pool_plan coord hsep p hp hponto V y hyV Q hQ hyQ I J N hJI hJN hN hE
  have hTE (e : Fin 2) (a : Γ) : ∀ᶠ n in atTop ⊓ 𝓟 (T e), ∀ x z,
      p x ∈ V n → p z ∈ V n → p x = p z → coord a x = coord a z :=
    (hE a).filter_mono (inf_le_inf le_rfl (Filter.principal_mono.mpr (hTI e)))
  obtain ⟨history, c, hsuc, hstep, hn, hm, htests, hliteral,
    Y, Z, hclosed, hY, hZ, hcov, hsurj, hZQ, hZdef, haux, hnewAux,
    hnewTarget, hfibre, hG, hFuniform⟩ :=
    exists_parity_ordered_split code hcode coord hsep B hB rho T hTinf p hp V hV Q hQ
      y hyV hyQ nu hdirac hTE z hWhole Base pR hpR hpRsurj VR hVR nuR hRbound
      sR muR hsRmap hsRmass hRnull pool hpool hRE hRref hRdis hTdis
  letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
  let projection : splitCarrier Y Z → K := fun x => x.1.1
  have hpj : Continuous projection := continuous_fst.comp continuous_subtype_val
  have hex : ∃ M : Fin 2 → Set ℕ,
      (∀ e, (M e).Infinite) ∧ (∀ e, M e ⊆ J ∩ N e) ∧
      (∀ n ∈ M 0 ∪ M 1, ∀ x y : splitCarrier Y Z,
        p x.1.1 ∈ V n → p y.1.1 ∈ V n → p x.1.1 = p y.1.1 → x.1.2 = y.1.2) ∧
      ∃ C : TopologicalSpace.Clopens (splitCarrier Y Z),
        (∀ n ∈ M 0, ∀ x : splitCarrier Y Z, p x.1.1 = y n → x ∈ C) ∧
        (∀ n ∈ M 1, ∀ x : splitCarrier Y Z, p x.1.1 = y n → x ∉ C) := by
    rcases hcase with hequal | ⟨M, C, hMinf, hMsub, hdis, hC0, hC1⟩
    · let M : Fin 2 → Set ℕ := fun e => Set.range (fun k : ℕ => (c (2 * k + (e : ℕ))).n)
      have hMinf (e : Fin 2) : (M e).Infinite := Set.infinite_range_of_injective
        (hn.injective.comp (fun a b h => by omega))
      have hMsub (e : Fin 2) : M e ⊆ J ∩ N e := by
        rintro _ ⟨k, rfl⟩
        have he : (⟨(2 * k + (e : ℕ)) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = e :=
          Fin.ext (by simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
            Nat.mod_eq_of_lt e.isLt])
        have hmem := (hstep (2 * k + (e : ℕ))).2.1
        rw [he] at hmem
        exact hequal e hmem
      refine ⟨M, hMinf, hMsub, ?_,
        ⟨{x | x.1.2 = true}, (isClopen_discrete ({true} : Set Bool)).preimage
          (continuous_snd.comp continuous_subtype_val)⟩, ?_, ?_⟩
      · intro n hnM
        rcases hnM with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exact hnewTarget _
        · exact hnewTarget _
      · rintro n ⟨k, rfl⟩ x hx
        exact (hfibre _ x hx).mpr (by omega)
      · rintro n ⟨k, rfl⟩ x hx hxC
        have := (hfibre _ x hx).mp hxC
        omega
    · have hUnused (n : ℕ) (hnM : n ∈ M 0 ∪ M 1) :
          Disjoint Z (p ⁻¹' V n) := by
        have hUnselected (q : ℕ) : (c q).n ≠ n := by
          intro hqn
          have ht := (hstep q).2.1
          have htarget : (c q).n ∈ T 0 ∪ T 1 := by
            have he : (⟨q % 2, Nat.mod_lt q (by decide)⟩ : Fin 2) = 0 ∨
                (⟨q % 2, Nat.mod_lt q (by decide)⟩ : Fin 2) = 1 := by omega
            rcases he with he | he
            · exact Or.inl (he ▸ ht)
            · exact Or.inr (he ▸ ht)
          exact Set.disjoint_left.mp hdis (hqn ▸ htarget) hnM
        rw [Set.disjoint_left]
        intro x hxZ hxV
        have hZsub : Z ⊆ (p ⁻¹' V n)ᶜ := by
          rw [hZdef]
          apply closure_minimal _ ((hV n).preimage hp).isOpen.isClosed_compl
          rintro x hx
          obtain ⟨q, hxq⟩ := mem_iUnion.mp hx
          by_cases heven : q % 2 = 0
          · simp only [if_pos heven] at hxq
            have hsub : x ∈ p ⁻¹' V (c q).n := by
              obtain ⟨_, _, _, _, hsub, _, _, _⟩ := (hstep q).2.2.2.1
              exact (hsub hxq).1.1
            exact fun hx => Set.disjoint_left.mp (hTdis (hUnselected q)) hsub hx
          · simpa only [if_neg heven, mem_empty_iff_false] using hxq
        exact hZsub hxZ hxV
      have hZero (n : ℕ) (hnM : n ∈ M 0 ∪ M 1)
          (x : splitCarrier Y Z) (hx : p x.1.1 ∈ V n) : x.1.2 = false := by
        rcases x.2 with hxY | hxZ
        · exact hxY.2
        · exact (Set.disjoint_left.mp (hUnused n hnM) hxZ.1 hx).elim
      refine ⟨M, hMinf, hMsub, ?_, ⟨projection ⁻¹' (C : Set K), C.isClopen.preimage hpj⟩, ?_, ?_⟩
      · intro n hnM x y hx hy _
        exact (hZero n hnM x hx).trans (hZero n hnM y hy).symm
      · intro n hn x hx
        exact hC0 n hn hx
      · intro n hn x hx
        exact hC1 n hn hx
  obtain ⟨M, hMinf, hMsub, hMside, hWitness⟩ := hex
  have hMJ : M 0 ∪ M 1 ⊆ J := union_subset
    ((hMsub 0).trans inter_subset_left) ((hMsub 1).trans inter_subset_left)
  have hME (a : Γ) : ∀ᶠ n in atTop ⊓ 𝓟 (M 0 ∪ M 1), ∀ x z,
      p x ∈ V n → p z ∈ V n → p x = p z → coord a x = coord a z :=
    (hE a).filter_mono (inf_le_inf le_rfl (Filter.principal_mono.mpr (hMJ.trans hJI)))
  have hSourceF := common_source_on_split coord hsep p hp hponto V hV P Q hP hPQ
    sourceNu hSourceBound hSourceNull hSourceSupport J (M 0 ∪ M 1)
    ((hMinf 0).mono subset_union_left) hMJ oldSourceF Y Z hY hZ hclosed hsurj hZQ
    hME (eventually_inf_principal.mpr (Eventually.of_forall hMside))
  exact ⟨z, T, history, c, M, Y, Z, hclosed, hsuc, hstep, hn, hm, htests, hliteral,
    hMinf, hMsub, hY, hZ, hcov, hsurj, hZQ, hnewAux, hMside, hWitness, hG,
    hSourceF, hFuniform⟩

end D5.S3.Topology.Measures.SignedDelayedSplit
