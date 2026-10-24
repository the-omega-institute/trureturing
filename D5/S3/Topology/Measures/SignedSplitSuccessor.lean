import D5.S3.Topology.Measures.SignedSplitSuccessorOrdered

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Topology.Measures.SignedSplitSuccessor

universe u v w

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
variable {L : Type v} [TopologicalSpace L] [T2Space L]
  [MeasurableSpace L] [BorelSpace L]

set_option maxHeartbeats 800000 in
/-- Dynamic measured choices and their same-object closed split.
The actual I and J, inherited and birth reservoirs, whole-support E, common
represented every-choice signed F and scheduled signed G are constructed.
The birth signed clusters and the independent target positive-variation
cluster are selected internally. Residual reference selection follows final I. -/
theorem exists_measured_dynamic_split [CompactSpace L] [ZeroDimensionalSpace L]
    [T2Space K] [SecondCountableTopology K]
    [TopologicalSpace.MetrizableSpace K] [TotallyDisconnectedSpace K]
    {Rows : Type w} {Γ : Type*}
    (code : Rows → ℕ) (hcode : Function.Injective code)
    (newRow : Rows) (hNewCode : code newRow = 0)
    (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (B : ℕ → TopologicalSpace.Clopens K) (hB : Function.Surjective B) (rho : ℕ → Γ)
    (hRho : ∀ d (e : Fin 2), {q | rho q = d ∧ q % 2 = (e : ℕ)}.Infinite)
    (targetPool : Set ℕ) (hTargetPoolInf : targetPool.Infinite) (p : K → L) (hp : Continuous p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (nu : ℕ → SignedMeasure L) (s : ℕ → SignedMeasure K)
    (hsmap : ∀ n, (s n).map p = nu n)
    (hsmass : ∀ n, (s n).totalVariation univ = (nu n).totalVariation univ)
    (hTargetMass : ∀ n, (nu n).totalVariation univ = 1)
    (hnull : ∀ n, (nu n).totalVariation (V n)ᶜ = 0)
    (hposreg : ∀ n, Measure.Regular (nu n).toJordanDecomposition.posPart)
    (hnegreg : ∀ n, Measure.Regular (nu n).toJordanDecomposition.negPart)
    (hpos : ∀ n, (1 : ℝ) / 2 ≤ (nu n).toJordanDecomposition.posPart.real univ)
    (hTargetE : ∀ c, ∀ᶠ n in atTop ⊓ 𝓟 targetPool, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y)
    (Base : Rows → Type v)
    [∀ r, TopologicalSpace (Base r)] [∀ r, T2Space (Base r)]
    [∀ r, MeasurableSpace (Base r)] [∀ r, BorelSpace (Base r)]
    (pR : ∀ r, K → Base r) (hpR : ∀ r, Continuous (pR r))
    (hpRsurj : ∀ r, Function.Surjective (pR r))
    (VR : ∀ r, ℕ → Set (Base r)) (hVR : ∀ r n, IsClopen (VR r n))
    (targetRow : Rows)
    (hTargetSupport : ∀ n, pR targetRow ⁻¹' VR targetRow n = p ⁻¹' V n)
    (hTargetFibre : ∀ x y, pR targetRow x = pR targetRow y → p x = p y)
    (nuR : ∀ r, Γ → ℕ → SignedMeasure (Base r))
    (hRbound : ∀ r d n, (nuR r d n).totalVariation.real univ ≤ 1)
    (sR : Rows → Γ → ℕ → SignedMeasure K)
    (oldMuR : ∀ r, r ≠ newRow → Γ → SignedMeasure K)
    (hsRmap : ∀ r d n, (sR r d n).map (pR r) = nuR r d n)
    (hsRmass : ∀ r d n, (sR r d n).totalVariation univ = (nuR r d n).totalVariation univ)
    (hRnull : ∀ r d n, (nuR r d n).totalVariation (VR r n)ᶜ = 0)
    (nuA : ∀ r, ℕ → SignedMeasure (Base r))
    (hAbound : ∀ r n, (nuA r n).totalVariation.real univ ≤ 1)
    (hAnull : ∀ r n, (nuA r n).totalVariation (VR r n)ᶜ = 0)
    (oldI : ∀ r, r ≠ newRow → Set ℕ)
    (hTargetPool : ∀ hr : targetRow ≠ newRow, targetPool ⊆ oldI targetRow hr)
    (oldJ : ∀ r, r ≠ newRow → Γ → Set ℕ)
    (oldN : ∀ r, r ≠ newRow → Γ → Fin 2 → Set ℕ)
    (hOldA : ∀ r hr d, oldJ r hr d ⊆ oldI r hr)
    (hOldB : ∀ r hr d, Disjoint (oldN r hr d 0) (oldN r hr d 1))
    (hOldC : ∀ r hr d e, (oldJ r hr d ∩ oldN r hr d e).Infinite)
    (hOldE : ∀ r hr c, ∀ᶠ n in atTop ⊓ 𝓟 (oldI r hr), ∀ x y,
      pR r x ∈ VR r n → pR r y ∈ VR r n → pR r x = pR r y → coord c x = coord c y)
    (hOldRef : ∀ r hr d, Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR r d n)).toWeakDual)
      (atTop ⊓ 𝓟 (oldJ r hr d)) (𝓝 (NormPreservingLifts.signedFunctional (oldMuR r hr d)).toWeakDual))
    (hNewProjection : Function.Injective (pR newRow))
    (hRdis : ∀ r, Pairwise (fun n m => Disjoint (pR r ⁻¹' VR r n) (pR r ⁻¹' VR r m)))
    (hTdis : Pairwise (fun n m => Disjoint (p ⁻¹' V n) (p ⁻¹' V m))) :
    ∃ (S : Set ℕ) (vP : ProbabilityMeasure K),
      S ⊆ targetPool ∧ S.Infinite ∧
      (∀ A : Set K, IsClopen A → Tendsto (fun n => (s n).totalVariation.real A)
        (atTop ⊓ 𝓟 S) (𝓝 ((vP : Measure K).real A))) ∧
      ∃ (birthS : Γ → Set ℕ) (birthMu : Γ → SignedMeasure K),
        (∀ d, (birthS d).Infinite) ∧
        (∀ d, (birthMu d).totalVariation.real univ ≤ 1 ∧
          Measure.Regular (birthMu d).toJordanDecomposition.posPart ∧
          Measure.Regular (birthMu d).toJordanDecomposition.negPart ∧
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sR newRow d n)).toWeakDual)
            (atTop ⊓ 𝓟 (birthS d))
            (𝓝 (NormPreservingLifts.signedFunctional (birthMu d)).toWeakDual)) ∧
    let v : Measure K := vP
    let muR := ordinaryReference newRow oldMuR birthMu
    let pool := ordinaryPool newRow oldJ oldN birthS rho
    ∃ (history : ∀ q, OrderedHistory Rows K q) (c : ℕ → OrderedColumn Rows K),
      (∀ q, history (q + 1) = (history q).append (c q)) ∧
      (∀ q, (c q).Spec code (history q) B S p V nu v Base pR VR
        (fun r => nuR r (rho q)) (fun r => muR r (rho q)) (fun r => pool r q)) ∧
      StrictMono (fun q => (c q).n) ∧ (∀ r, StrictMono (fun q => (c q).m r)) ∧
      (∀ j q, j ≤ q → (c j).H ∈ (c q).F ∧ B j ∈ (c q).F) ∧
      (∀ r q s, code r < q → q < s →
        Disjoint ((c s).H : Set K) (pR r ⁻¹' VR r ((c q).m r))) ∧
      ∃ (Y Z : Set K) (hclosed : IsClosed (splitCarrier Y Z)),
        letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
        IsClosed Y ∧ IsClosed Z ∧ Y ∪ Z = univ ∧
        Z = closure (⋃ s : ℕ, ⋃ (_ : s % 2 = 0), ((c s).H : Set K)) ∧ Y = closure Zᶜ ∧
        IsClosed (splitCarrier Y Z) ∧
        Function.Surjective (fun x : splitCarrier Y Z => x.1.1) ∧
        (∀ r q, code r < q →
          Z ∩ (pR r ⁻¹' VR r ((c q).m r)) =
            evenPrefix (fun s => ((c s).H : Set K)) q ∩ (pR r ⁻¹' VR r ((c q).m r)) ∧
          Y ∩ (pR r ⁻¹' VR r ((c q).m r)) =
            (evenPrefix (fun s => ((c s).H : Set K)) q)ᶜ ∩ (pR r ⁻¹' VR r ((c q).m r)) ∧
          Disjoint (Y ∩ Z) (pR r ⁻¹' VR r ((c q).m r)) ∧
          ∀ x : splitCarrier Y Z, x.1.1 ∈ pR r ⁻¹' VR r ((c q).m r) →
            (x.1.2 = true ↔ x.1.1 ∈ evenPrefix (fun s => ((c s).H : Set K)) q)) ∧
        (∀ q, Z ∩ (p ⁻¹' V (c q).n) = (if q % 2 = 0 then ((c q).H : Set K) else ∅) ∧
          Disjoint (Y ∩ Z) (p ⁻¹' V (c q).n) ∧
          ∀ x : splitCarrier Y Z, x.1.1 ∈ p ⁻¹' V (c q).n →
            (x.1.2 = true ↔ q % 2 = 0 ∧ x.1.1 ∈ (c q).H)) ∧
        (∀ r q, code r < q → ∀ x y : splitCarrier Y Z,
          pR r x.1.1 ∈ VR r ((c q).m r) → pR r y.1.1 ∈ VR r ((c q).m r) →
          pR r x.1.1 = pR r y.1.1 → x.1.2 = y.1.2) ∧
        (∀ q, ∀ x y : splitCarrier Y Z,
          p x.1.1 ∈ V (c q).n → p y.1.1 ∈ V (c q).n →
          p x.1.1 = p y.1.1 → x.1.2 = y.1.2) ∧
        (∀ q (t : SignedMeasure (splitCarrier Y Z)),
          t.map (fun x => p x.1.1) = nu (c q).n →
          t.totalVariation univ = (nu (c q).n).totalVariation univ →
          (q % 2 = 0 → (1 : ℝ) / 6 < t {x | x.1.2 = true}) ∧
          (q % 2 ≠ 0 → t {x | x.1.2 = true} = 0)) ∧
        (∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (fun x => p x.1.1) = nu n) →
          (∀ n, (sigma n).totalVariation univ = (nu n).totalVariation univ) →
          {n | (1 : ℝ) / 6 ≤ sigma n {x | x.1.2 = true}}.Infinite ∧
            {n | sigma n {x | x.1.2 = true} = 0}.Infinite) ∧
        (∀ (r : Rows) (d : Γ) (phi : ℕ → ℕ), StrictMono phi →
          (∀ k, rho (phi k) = d) →
          ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
            Measure.Regular mu.toJordanDecomposition.posPart ∧
            Measure.Regular mu.toJordanDecomposition.negPart ∧
            ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
              (∀ k, (sigma k).map (fun x => pR r x.1.1) = nuR r d ((c (phi k)).m r)) →
              (∀ k, (sigma k).totalVariation univ =
                (nuR r d ((c (phi k)).m r)).totalVariation univ) →
              Tendsto (fun k => (NormPreservingLifts.signedFunctional (sigma k)).toWeakDual)
                atTop (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual)) ∧
        ∃ (I : Rows → Set ℕ) (J : Rows → Γ → Set ℕ) (N : Rows → Γ → Fin 2 → Set ℕ),
          (∀ r, I r = {n | (∃ q, code r < q ∧ (c q).m r = n) ∨
            (r = targetRow ∧ ∃ q, (c q).n = n)}) ∧
          (∀ r d, J r d = {n | ∃ q, code r < q ∧ rho q = d ∧ (c q).m r = n}) ∧
          (∀ r hr d e, N r d e = oldN r hr d e) ∧
          (∀ d e, N newRow d e =
            {n | ∃ q, code newRow < q ∧ rho q = d ∧ q % 2 = (e : ℕ) ∧ (c q).m newRow = n}) ∧
          (∀ r d, J r d ⊆ I r) ∧
          (∀ r d, Disjoint (N r d 0) (N r d 1)) ∧
          (∀ r d e, (J r d ∩ N r d e).Infinite) ∧
          (∀ r, (I r).Infinite) ∧
          (∀ r hr, I r ⊆ oldI r hr) ∧
          (∀ r hr d, J r d ⊆ oldJ r hr d) ∧
          (∀ r (A : Set K), IsClopen A → ∀ᶠ n in atTop ⊓ 𝓟 (I r),
            ∀ x y : splitCarrier Y Z,
              pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
              pR r x.1.1 = pR r y.1.1 →
              (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2) ∧
          (∀ r d, ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
            Measure.Regular mu.toJordanDecomposition.posPart ∧
            Measure.Regular mu.toJordanDecomposition.negPart ∧
            ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
              (∀ n, (sigma n).map (fun x => pR r x.1.1) = nuR r d n) →
              (∀ n, (sigma n).totalVariation univ = (nuR r d n).totalVariation univ) →
              Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
                (atTop ⊓ 𝓟 (J r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual)) ∧
          (∃ (JA : Rows → Set ℕ) (NA : Rows → Fin 2 → Set ℕ)
              (muA : Rows → SignedMeasure (splitCarrier Y Z)),
            ∀ r, JA r ⊆ I r ∧ Disjoint (NA r 0) (NA r 1) ∧
              (∀ e, NA r e ⊆ JA r) ∧ (∀ e, (JA r ∩ NA r e).Infinite) ∧
              (muA r).totalVariation.real univ ≤ 1 ∧
              Measure.Regular (muA r).toJordanDecomposition.posPart ∧
              Measure.Regular (muA r).toJordanDecomposition.negPart ∧
              ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
                (∀ n, (sigma n).map (fun x => pR r x.1.1) = nuA r n) →
                (∀ n, (sigma n).totalVariation univ = (nuA r n).totalVariation univ) →
                Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
                  (atTop ⊓ 𝓟 (JA r))
                  (𝓝 (NormPreservingLifts.signedFunctional (muA r)).toWeakDual)) := by
  classical
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  letI : Infinite targetPool := Set.infinite_coe_iff.mpr hTargetPoolInf
  let tauV : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet targetPool
  have htauVRange : Set.range tauV = targetPool := Nat.orderEmbeddingOfSet_range targetPool
  have htauVMem (k : ℕ) : tauV k ∈ targetPool := htauVRange ▸ Set.mem_range_self k
  let tvProb : ℕ → ProbabilityMeasure K := fun n =>
    ⟨(s n).totalVariation, ⟨by rw [hsmass n, hTargetMass n]⟩⟩
  obtain ⟨vP, phiV, hphiV, hVconv⟩ := CompactSpace.tendsto_subseq (fun k => tvProb (tauV k))
  let psiV : ℕ → ℕ := fun k => tauV (phiV k)
  have hpsiV : StrictMono psiV := tauV.strictMono.comp hphiV
  let S : Set ℕ := Set.range psiV
  have hS : S.Infinite := Set.infinite_range_of_injective hpsiV.injective
  have hSsub : S ⊆ targetPool := by
    rintro _ ⟨k, rfl⟩
    exact htauVMem (phiV k)
  let v : Measure K := vP
  have href (A : Set K) (hA : IsClopen A) :
      Tendsto (fun n => (s n).totalVariation.real A) (atTop ⊓ 𝓟 S) (𝓝 (v.real A)) := by
    have hprob := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hVconv hA
    have hreal := (NNReal.continuous_coe.tendsto (vP A)).comp hprob
    have hconv : Tendsto (fun k => (s (psiV k)).totalVariation.real A) atTop (𝓝 (v.real A)) := by
      exact hreal
    apply Filter.tendsto_def.mpr
    intro T hT
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hconv.eventually hT)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (psiV M)] with n hn hnS
    obtain ⟨k, rfl⟩ := hnS
    have hMk : M ≤ k := by
      by_contra hk
      exact (not_lt_of_ge hn) (hpsiV (lt_of_not_ge hk))
    exact hM k hMk
  have hE (c : Γ) : ∀ᶠ n in atTop ⊓ 𝓟 S, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y :=
    (hTargetE c).filter_mono (inf_le_inf le_rfl (Filter.principal_mono.mpr hSsub))
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  have hBirthBound (d : Γ) (n : ℕ) : (sR newRow d n).totalVariation.real univ ≤ 1 := by
    simpa only [Measure.real, hsRmass] using hRbound newRow d n
  have hBirthCluster (d : Γ) := SignedWeakStarCompactness.exists_subsequence_tendsto_signedFunctional
    1 (by norm_num) (sR newRow d) (hBirthBound d)
  choose phiBirth birthMu hPhiBirth hMuBirth hConvBirth using hBirthCluster
  let birthS : Γ → Set ℕ := fun d => Set.range (phiBirth d)
  have hBirthS (d : Γ) : (birthS d).Infinite := Set.infinite_range_of_injective (hPhiBirth d).injective
  have hBirthRef (d : Γ) : Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR newRow d n)).toWeakDual)
      (atTop ⊓ 𝓟 (birthS d)) (𝓝 (NormPreservingLifts.signedFunctional (birthMu d)).toWeakDual) := by
    apply Filter.tendsto_def.mpr
    intro A hA
    obtain ⟨M, hM⟩ := eventually_atTop.mp ((hConvBirth d).eventually hA)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (phiBirth d M)] with n hn hnS
    obtain ⟨k, rfl⟩ := hnS
    have hMk : M ≤ k := by
      by_contra hk
      exact (not_lt_of_ge hn) (hPhiBirth d (lt_of_not_ge hk))
    exact hM k hMk
  have hBirthData (d : Γ) : (birthMu d).totalVariation.real univ ≤ 1 ∧
      Measure.Regular (birthMu d).toJordanDecomposition.posPart ∧
      Measure.Regular (birthMu d).toJordanDecomposition.negPart ∧
      Tendsto (fun n => (NormPreservingLifts.signedFunctional (sR newRow d n)).toWeakDual)
        (atTop ⊓ 𝓟 (birthS d)) (𝓝 (NormPreservingLifts.signedFunctional (birthMu d)).toWeakDual) :=
    ⟨hMuBirth d, inferInstance, inferInstance, hBirthRef d⟩
  let muR : Rows → Γ → SignedMeasure K := ordinaryReference newRow oldMuR birthMu
  let pool : Rows → ℕ → Set ℕ := ordinaryPool newRow oldJ oldN birthS rho
  have hpool : ∀ r q, (pool r q).Infinite := by
    intro r q
    by_cases hr : r = newRow
    · subst r
      simpa [pool, ordinaryPool] using hBirthS (rho q)
    · simpa only [pool, ordinaryPool, dite_eq_right hr] using
        hOldC r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩
  have hRE : ∀ r q c, ∀ᶠ n in atTop ⊓ 𝓟 (pool r q), ∀ x y,
      pR r x ∈ VR r n → pR r y ∈ VR r n → pR r x = pR r y → coord c x = coord c y := by
    intro r q c
    by_cases hr : r = newRow
    · subst r
      exact Filter.Eventually.of_forall (fun _ x y _ _ hxy => congrArg (coord c) (hNewProjection hxy))
    · have hsub : pool r q ⊆ oldI r hr := by
        intro n hn
        have hn' : n ∈ oldJ r hr (rho q) ∩
            oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩ := by
          simpa only [pool, ordinaryPool, dite_eq_right hr] using hn
        exact hOldA r hr (rho q) hn'.1
      exact (hOldE r hr c).filter_mono (inf_le_inf le_rfl (Filter.principal_mono.mpr hsub))
  have hRref : ∀ r q, Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR r (rho q) n)).toWeakDual)
      (atTop ⊓ 𝓟 (pool r q)) (𝓝 (NormPreservingLifts.signedFunctional (muR r (rho q))).toWeakDual) := by
    intro r q
    by_cases hr : r = newRow
    · subst r
      simpa [pool, ordinaryPool, muR, ordinaryReference] using hBirthRef (rho q)
    · have hsub : pool r q ⊆ oldJ r hr (rho q) := by
        intro n hn
        have hn' : n ∈ oldJ r hr (rho q) ∩
            oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩ := by
          simpa only [pool, ordinaryPool, dite_eq_right hr] using hn
        exact hn'.1
      simpa only [muR, ordinaryReference, dif_neg hr] using
        (hOldRef r hr (rho q)).mono_left (inf_le_inf le_rfl (Filter.principal_mono.mpr hsub))
  let State (q : ℕ) := {h : OrderedHistory Rows K q //
    ∀ r (j : Fin q), v.real (pR r ⁻¹' VR r (h.m r j)) ≤
      (1 : ℝ) / 128 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ (j : ℕ)}
  have hex (q : ℕ) (x : State q) := exists_ordered_signed_column code hcode x.val
    coord hsep B S hS p hp V hV nu s hsmap hsmass hnull hposreg hnegreg hpos hE v href
    Base pR hpR VR hVR (fun r => nuR r (rho q)) (fun r => sR r (rho q)) (fun r => muR r (rho q))
    (fun r => hsRmap r (rho q)) (fun r => hsRmass r (rho q)) (fun r => hRnull r (rho q))
    (fun r => pool r q) (fun r => hpool r q) (fun r => hRE r q) (fun r => hRref r q)
    hRdis x.property
  choose column hcolumn using hex
  let next (q : ℕ) (x : State q) : State (q + 1) :=
    ⟨x.val.append (column q x), by
      intro r j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [OrderedHistory.append, Fin.snoc_last, Fin.val_last] using
          ((hcolumn q x).2.2.2.2.2 r).2.2.1.le
      · simpa only [OrderedHistory.append, Fin.snoc_castSucc, Fin.val_castSucc] using
          x.property r j⟩
  let empty : State 0 := ⟨⟨Fin.elim0, Fin.elim0, Fin.elim0, fun _ => Fin.elim0⟩,
    fun _ j => Fin.elim0 j⟩
  let hist : ∀ q, State q := fun q => Nat.rec empty next q
  let c : ℕ → OrderedColumn Rows K := fun q => column q (hist q)
  have hsuc (q : ℕ) : (hist (q + 1)).val = (hist q).val.append (c q) := rfl
  have hstep (q : ℕ) : (c q).Spec code (hist q).val B S p V nu v Base pR VR
      (fun r => nuR r (rho q)) (fun r => muR r (rho q)) (fun r => pool r q) := hcolumn q (hist q)
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
    exact hsub.trans sdiff_subset
  have hdis : Pairwise (fun q s => Disjoint (p ⁻¹' V (c q).n) (p ⁻¹' V (c s).n)) := by
    intro q s hqs
    exact hTdis (fun h => hqs (hn.injective h))
  obtain ⟨Y, Z, hY, hZ, hcov, hZdef, hYdef, hclosed, hsurj, haux, htarget⟩ :=
    exists_closed_split_of_ordered_exclusion code (fun q => ((c q).H : Set K))
      (fun q => (c q).H.isClopen) (fun r q => pR r ⁻¹' VR r ((c q).m r))
      (fun r q => (hVR r _).preimage (hpR r)) havoid
      (fun q => p ⁻¹' V (c q).n) (fun q => (hV _).preimage hp) hdis hHT
  have hnewAux : ∀ r q, code r < q → ∀ x y : splitCarrier Y Z,
      pR r x.1.1 ∈ VR r ((c q).m r) → pR r y.1.1 ∈ VR r ((c q).m r) →
      pR r x.1.1 = pR r y.1.1 → x.1.2 = y.1.2 := by
    intro r q hr x y hx hy hxy
    have hfinite (j : ℕ) (hj : j ≤ q) :
        (x.1.1 ∈ (c j).H ↔ y.1.1 ∈ (c j).H) :=
      ((hstep q).2.2.2.2.2 r).2.2.2.1 (c j).H (htests j q hj).1 x.1.1 y.1.1 hx hy hxy
    have hU : x.1.1 ∈ evenPrefix (fun s => ((c s).H : Set K)) q ↔
        y.1.1 ∈ evenPrefix (fun s => ((c s).H : Set K)) q := by
      simp only [evenPrefix, mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨j, hj, hxH⟩
        refine ⟨j, hj, ?_⟩
        by_cases heven : j % 2 = 0
        · simp only [ite_eq_left heven] at hxH ⊢
          exact (hfinite j (by omega)).mp hxH
        · simpa only [ite_eq_right heven, mem_empty_iff_false] using hxH
      · rintro ⟨j, hj, hyH⟩
        refine ⟨j, hj, ?_⟩
        by_cases heven : j % 2 = 0
        · simp only [ite_eq_left heven] at hyH ⊢
          exact (hfinite j (by omega)).mpr hyH
        · simpa only [ite_eq_right heven, mem_empty_iff_false] using hyH
    have hb := ((haux r q hr).2.2.2 x hx).trans (hU.trans ((haux r q hr).2.2.2 y hy).symm)
    exact bool_eq_of_true_iff x.1.2 y.1.2 hb
  have hnewTarget : ∀ q, ∀ x y : splitCarrier Y Z,
      p x.1.1 ∈ V (c q).n → p y.1.1 ∈ V (c q).n →
      p x.1.1 = p y.1.1 → x.1.2 = y.1.2 := by
    intro q x y hx hy hxy
    obtain ⟨_, _, _, _, _, _, hHE, _⟩ := (hstep q).2.2.2.1
    have hHxy := hHE x.1.1 y.1.1 hx hy hxy
    change x.1.1 ∈ ((c q).H : Set K) ↔ y.1.1 ∈ ((c q).H : Set K) at hHxy
    have htagX := (htarget q).2.2 x hx
    have htagY := (htarget q).2.2 y hy
    have hb : (x.1.2 = true ↔ y.1.2 = true) := by
      rw [htagX, htagY, hHxy]
    exact bool_eq_of_true_iff x.1.2 y.1.2 hb
  letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
  let projection : splitCarrier Y Z → K := fun x => x.1.1
  have hprojection : Continuous projection := continuous_fst.comp continuous_subtype_val
  let side : Set (splitCarrier Y Z) := {x | x.1.2 = true}
  have hside : IsClopen side := (isClopen_discrete ({true} : Set Bool)).preimage
    (continuous_snd.comp continuous_subtype_val)
  have hG : ∀ q (t : SignedMeasure (splitCarrier Y Z)),
      t.map (p ∘ projection) = nu (c q).n →
      t.totalVariation univ = (nu (c q).n).totalVariation univ →
      (q % 2 = 0 → (1 : ℝ) / 6 < t side) ∧ (q % 2 ≠ 0 → t side = 0) := by
    intro q t htmap htmass
    let W : Set (splitCarrier Y Z) := (p ∘ projection) ⁻¹' V (c q).n
    have hW : IsClopen W := (hV _).preimage (hp.comp hprojection)
    have htNull : t.totalVariation Wᶜ = 0 := support_null (p ∘ projection)
      (hp.comp hprojection) t (nu (c q).n) htmap htmass (hV _) (hnull _)
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
      have hlarge := ((hstep q).2.2.2.2.1 (t.map projection) hmid.1 hmid.2).2
      rw [htcut, htrace, ← VectorMeasure.map_apply t hprojection.measurable
        (c q).H.isClopen.isClosed.measurableSet]
      exact hlarge
    · intro hodd
      have htrace : side ∩ W = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxW⟩
        exact hodd (((htarget q).2.2 x hxW).mp hx).1
      rw [htcut, htrace, t.empty]
  have hGinf : ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
      (∀ n, (sigma n).map (p ∘ projection) = nu n) →
      (∀ n, (sigma n).totalVariation univ = (nu n).totalVariation univ) →
      {n | (1 : ℝ) / 6 ≤ sigma n side}.Infinite ∧ {n | sigma n side = 0}.Infinite := by
    intro sigma hmap hmass
    have heven : Function.Injective (fun k => (c (2 * k)).n) :=
      hn.injective.comp (fun a b hab => by omega)
    have hodd : Function.Injective (fun k => (c (2 * k + 1)).n) :=
      hn.injective.comp (fun a b hab => by omega)
    constructor
    · apply (Set.infinite_range_of_injective heven).mono
      rintro _ ⟨k, rfl⟩
      exact ((hG (2 * k) (sigma _) (hmap _) (hmass _)).1 (by omega)).le
    · apply (Set.infinite_range_of_injective hodd).mono
      rintro _ ⟨k, rfl⟩
      exact (hG (2 * k + 1) (sigma _) (hmap _) (hmass _)).2 (by omega)
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
    by_cases hex : ∃ ref : ℕ → SignedMeasure (splitCarrier Y Z),
        (∀ k, (ref k).map (pR r ∘ projection) = nuR r d ((c (phi k)).m r)) ∧
        (∀ k, (ref k).totalVariation univ = (nuR r d ((c (phi k)).m r)).totalVariation univ)
    · obtain ⟨ref, hrefmap, hrefmass⟩ := hex
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
    · refine ⟨0, ?_, ?_, ?_, ?_⟩
      · norm_num [SignedMeasure.totalVariation_zero, Measure.real]
      · simpa only [SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_posPart]
          using (inferInstance : Measure.Regular (0 : Measure (splitCarrier Y Z)))
      · simpa only [SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_negPart]
          using (inferInstance : Measure.Regular (0 : Measure (splitCarrier Y Z)))
      · intro sigma hmap hmass
        exact (hex ⟨sigma, hmap, hmass⟩).elim
  let I : Rows → Set ℕ := fun r => {n | (∃ q, code r < q ∧ (c q).m r = n) ∨
    (r = targetRow ∧ ∃ q, (c q).n = n)}
  let J : Rows → Γ → Set ℕ := fun r d =>
    {n | ∃ q, code r < q ∧ rho q = d ∧ (c q).m r = n}
  let N : Rows → Γ → Fin 2 → Set ℕ := fun r d e =>
    if hr : r = newRow then {n | ∃ q, code r < q ∧ rho q = d ∧
      q % 2 = (e : ℕ) ∧ (c q).m r = n}
    else oldN r hr d e
  have hJsub (r : Rows) (d : Γ) : J r d ⊆ I r := by
    rintro n ⟨q, hq, _, rfl⟩
    exact Or.inl ⟨q, hq, rfl⟩
  have hOldPool (r : Rows) (hr : r ≠ newRow) (q : ℕ) :
      (c q).m r ∈ oldJ r hr (rho q) ∩
        oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩ := by
    have hmem := ((hstep q).2.2.2.2.2 r).1
    simpa only [pool, ordinaryPool, dif_neg hr] using hmem
  have hNold (r : Rows) (hr : r ≠ newRow) (d : Γ) (e : Fin 2) :
      N r d e = oldN r hr d e := by simp only [N, dif_neg hr]
  have hNnew (d : Γ) (e : Fin 2) : N newRow d e =
      {n | ∃ q, code newRow < q ∧ rho q = d ∧ q % 2 = (e : ℕ) ∧ (c q).m newRow = n} := by
    simp only [N, dif_pos rfl]
  have hNdis (r : Rows) (d : Γ) : Disjoint (N r d 0) (N r d 1) := by
    by_cases hr : r = newRow
    · simp only [N, dif_pos hr]
      rw [Set.disjoint_left]
      rintro n ⟨q, _, _, hq, heq⟩ ⟨s, _, _, hs, hes⟩
      have hqs : q = s := (hm r).injective (heq.trans hes.symm)
      subst s
      change q % 2 = 0 at hq
      change q % 2 = 1 at hs
      omega
    · rw [hNold r hr, hNold r hr]
      exact hOldB r hr d
  have hC (r : Rows) (d : Γ) (e : Fin 2) : (J r d ∩ N r d e).Infinite := by
    have hinf : {q | code r < q ∧ rho q = d ∧ q % 2 = (e : ℕ)}.Infinite := by
      have h := (hRho d e).diff (Set.finite_Iic (code r))
      exact h.mono (fun q hq => ⟨by simpa only [Set.mem_Iic, not_le] using hq.2,
        hq.1.1, hq.1.2⟩)
    apply (hinf.image (hm r).injective.injOn).mono
    rintro n ⟨q, ⟨hq, hlabel, hparity⟩, rfl⟩
    refine ⟨⟨q, hq, hlabel, rfl⟩, ?_⟩
    by_cases hr : r = newRow
    · simp only [N, dif_pos hr]
      exact ⟨q, hq, hlabel, hparity, rfl⟩
    · rw [hNold r hr]
      have he : (⟨q % 2, Nat.mod_lt q (by decide)⟩ : Fin 2) = e := Fin.ext hparity
      have hmem := (hOldPool r hr q).2
      simpa only [hlabel, he] using hmem
  have hIinf (r : Rows) : (I r).Infinite :=
    (hC r (rho 0) 0).mono (fun _ hn => hJsub r (rho 0) hn.1)
  have hIold (r : Rows) (hr : r ≠ newRow) : I r ⊆ oldI r hr := by
    rintro n (⟨q, _, rfl⟩ | ⟨rfl, q, rfl⟩)
    · exact hOldA r hr (rho q) (hOldPool r hr q).1
    · exact hTargetPool hr (hSsub (hstep q).2.1)
  have hJold (r : Rows) (hr : r ≠ newRow) (d : Γ) : J r d ⊆ oldJ r hr d := by
    rintro n ⟨q, _, hlabel, rfl⟩
    simpa only [hlabel] using (hOldPool r hr q).1
  have hFullE (r : Rows) (A : Set K) (hA : IsClopen A) :
      ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
        pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
        pR r x.1.1 = pR r y.1.1 →
        (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2 := by
    obtain ⟨j, hj⟩ := hB ⟨A, hA⟩
    let Q := max j (code r + 1)
    have htargetE := eventually_clopen_fibre (atTop ⊓ 𝓟 S) coord hsep p V hE hA
    obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_inf_principal.mp htargetE)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (max M ((c Q).m r))] with n hn hnI
    intro x y hx hy hxy
    rcases hnI with ⟨q, hq, rfl⟩ | ⟨rfl, q, rfl⟩
    · have hQq : Q ≤ q := by
        by_contra hnq
        have hlt := hm r (lt_of_not_ge hnq)
        exact (not_lt_of_ge (le_trans (le_max_right M _) hn)) hlt
      have hAF : (⟨A, hA⟩ : TopologicalSpace.Clopens K) ∈ (c q).F := by
        simpa only [hj] using (htests j q ((le_max_left j _).trans hQq)).2
      refine ⟨?_, hnewAux r q hq x y hx hy hxy⟩
      exact ((hstep q).2.2.2.2.2 r).2.2.2.1 ⟨A, hA⟩ hAF x.1.1 y.1.1 hx hy hxy
    · have hx' : p x.1.1 ∈ V (c q).n := by
        change x.1.1 ∈ p ⁻¹' V (c q).n
        rw [← hTargetSupport]
        exact hx
      have hy' : p y.1.1 ∈ V (c q).n := by
        change y.1.1 ∈ p ⁻¹' V (c q).n
        rw [← hTargetSupport]
        exact hy
      have hxy' := hTargetFibre x.1.1 y.1.1 hxy
      exact ⟨hM _ ((le_max_left M _).trans hn) (hstep q).2.1 x.1.1 y.1.1 hx' hy' hxy',
        hnewTarget q x y hx' hy' hxy'⟩
  have hFJ (r : Rows) (d : Γ) :
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (pR r ∘ projection) = nuR r d n) →
          (∀ n, (sigma n).totalVariation univ = (nuR r d n).totalVariation univ) →
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
            (atTop ⊓ 𝓟 (J r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    let P : Set ℕ := {q | code r < q ∧ rho q = d}
    have hP : P.Infinite := by
      apply ((hRho d 0).diff (Set.finite_Iic (code r))).mono
      intro q hq
      exact ⟨by simpa only [Set.mem_Iic, not_le] using hq.2, hq.1.1⟩
    letI : Infinite P := Set.infinite_coe_iff.mpr hP
    let phi : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet P
    have hphiRange : Set.range phi = P := Nat.orderEmbeddingOfSet_range P
    have hphiMem (k : ℕ) : phi k ∈ P := hphiRange ▸ Set.mem_range_self k
    have hlabel (k : ℕ) : rho (phi k) = d := (hphiMem k).2
    let psi : ℕ → ℕ := fun k => (c (phi k)).m r
    have hpsi : StrictMono psi := (hm r).comp phi.strictMono
    have hpsiRange : Set.range psi = J r d := by
      ext n
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨phi k, (hphiMem k).1, hlabel k, rfl⟩
      · rintro ⟨q, hq, hlabelq, hqn⟩
        obtain ⟨k, rfl⟩ : q ∈ Set.range phi := hphiRange.symm ▸ ⟨hq, hlabelq⟩
        exact ⟨k, hqn⟩
    obtain ⟨mu, hmu, hpos, hneg, hall⟩ := hFuniform r d phi phi.strictMono hlabel
    refine ⟨mu, hmu, hpos, hneg, ?_⟩
    intro sigma hmap hmass
    have hconv := hall (fun k => sigma (psi k)) (fun k => hmap (psi k))
      (fun k => hmass (psi k))
    apply Filter.tendsto_def.mpr
    intro A hA
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hconv.eventually hA)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (psi M)] with n hn hnJ
    obtain ⟨k, rfl⟩ : n ∈ Set.range psi := hpsiRange.symm ▸ hnJ
    have hMk : M ≤ k := by
      by_contra hk
      exact (not_lt_of_ge hn) (hpsi (lt_of_not_ge hk))
    exact hM k hMk
  let splitCoord : Option Γ → C(splitCarrier Y Z, Bool) := fun c =>
    match c with
    | none => ⟨fun x => x.1.2, continuous_snd.comp continuous_subtype_val⟩
    | some c => ⟨fun x => coord c x.1.1, (coord c).continuous.comp hprojection⟩
  have hSplitSep : Function.Injective
      (fun x : splitCarrier Y Z => fun c => splitCoord c x) := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · apply hsep
      funext c
      exact congrFun hxy (some c)
    · exact congrFun hxy none
  have hSplitE (r : Rows) (c : Option Γ) :
      ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
        pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
        pR r x.1.1 = pR r y.1.1 → splitCoord c x = splitCoord c y := by
    cases c with
    | none =>
      filter_upwards [hFullE r ∅ isClopen_empty] with n hn
      intro x y hx hy hxy
      exact (hn x y hx hy hxy).2
    | some c =>
      let A : Set K := coord c ⁻¹' {true}
      have hA : IsClopen A := (isClopen_discrete ({true} : Set Bool)).preimage (coord c).continuous
      filter_upwards [hFullE r A hA] with n hn
      intro x y hx hy hxy
      apply bool_eq_of_true_iff
      change (coord c x.1.1 = true ↔ coord c y.1.1 = true)
      simpa only [A, mem_preimage, mem_singleton_iff] using (hn x y hx hy hxy).1
  have hLocE (r : Rows) (f : LocallyConstant (splitCarrier Y Z) ℝ) :
      ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
        pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
        pR r x.1.1 = pR r y.1.1 → f x = f y := by
    have hpieces : ∀ a ∈ f.range_finite.toFinset,
        ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
          pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
          pR r x.1.1 = pR r y.1.1 → (f x = a ↔ f y = a) := by
      intro a _
      exact eventually_clopen_fibre (atTop ⊓ 𝓟 (I r)) splitCoord hSplitSep
        (pR r ∘ projection) (VR r) (hSplitE r) (f.isLocallyConstant.isClopen_fiber a)
    filter_upwards [(Filter.eventually_all_finset f.range_finite.toFinset).mpr hpieces] with n hn
    intro x y hx hy hxy
    exact ((hn (f x) (f.range_finite.mem_toFinset.mpr ⟨x, rfl⟩) x y hx hy hxy).mp rfl).symm
  letI : MetricSpace (splitCarrier Y Z) := TopologicalSpace.metrizableSpaceMetric _
  have hResidualLifts (r : Rows) (n : ℕ) :=
    NormPreservingLiftExistence.exists_norm_preserving_lift (pR r ∘ projection)
      ((hpR r).comp hprojection) ((hpRsurj r).comp hsurj) (nuA r n)
  choose sA hsAmap hsAmass using hResidualLifts
  have hResidual (r : Rows) :
      ∃ (JA : Set ℕ) (NA : Fin 2 → Set ℕ) (mu : SignedMeasure (splitCarrier Y Z)),
        JA ⊆ I r ∧ Disjoint (NA 0) (NA 1) ∧
        (∀ e, NA e ⊆ JA) ∧ (∀ e, (JA ∩ NA e).Infinite) ∧
        mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (pR r ∘ projection) = nuA r n) →
          (∀ n, (sigma n).totalVariation univ = (nuA r n).totalVariation univ) →
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
            (atTop ⊓ 𝓟 JA) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    letI : Infinite (I r) := Set.infinite_coe_iff.mpr (hIinf r)
    let tau : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet (I r)
    have htauRange : Set.range tau = I r := Nat.orderEmbeddingOfSet_range (I r)
    have htauMem (k : ℕ) : tau k ∈ I r := htauRange ▸ Set.mem_range_self k
    have hbound (k : ℕ) : (sA r (tau k)).totalVariation.real univ ≤ 1 := by
      simpa only [Measure.real, hsAmass] using hAbound r (tau k)
    obtain ⟨phi, mu, hphi, hmu, hrefconv⟩ :=
      SignedWeakStarCompactness.exists_subsequence_tendsto_signedFunctional
        1 (by norm_num) (fun k => sA r (tau k)) hbound
    let psi : ℕ → ℕ := fun k => tau (phi k)
    have hpsi : StrictMono psi := tau.strictMono.comp hphi
    let JA : Set ℕ := Set.range psi
    let NA : Fin 2 → Set ℕ := fun e => Set.range (fun k => psi (2 * k + (e : ℕ)))
    have hJAsub : JA ⊆ I r := by
      rintro _ ⟨k, rfl⟩
      exact htauMem (phi k)
    have hNAsub (e : Fin 2) : NA e ⊆ JA := by
      rintro _ ⟨k, rfl⟩
      exact Set.mem_range_self (2 * k + (e : ℕ))
    have hNAinf (e : Fin 2) : (JA ∩ NA e).Infinite := by
      have hinj : Function.Injective (fun k => psi (2 * k + (e : ℕ))) :=
        hpsi.injective.comp (fun a b hab => by omega)
      apply (Set.infinite_range_of_injective hinj).mono
      rintro _ ⟨k, rfl⟩
      exact ⟨Set.mem_range_self (2 * k + (e : ℕ)), Set.mem_range_self k⟩
    have hNAdis : Disjoint (NA 0) (NA 1) := by
      rw [Set.disjoint_left]
      rintro n ⟨k, hk⟩ ⟨j, hj⟩
      have heq := hpsi.injective (hk.trans hj.symm)
      change 2 * k + 0 = 2 * j + 1 at heq
      omega
    refine ⟨JA, NA, mu, hJAsub, hNAdis, hNAsub, hNAinf, hmu, inferInstance, inferInstance, ?_⟩
    intro sigma hmap hmass
    have hfibre (f : LocallyConstant (splitCarrier Y Z) ℝ) :
        ∀ᶠ k in atTop, ∀ x y : splitCarrier Y Z,
          pR r x.1.1 ∈ VR r (psi k) → pR r y.1.1 ∈ VR r (psi k) →
          pR r x.1.1 = pR r y.1.1 → f x = f y := by
      filter_upwards [hpsi.tendsto_atTop.eventually (eventually_inf_principal.mp (hLocE r f))]
        with k hk
      exact hk (hJAsub (Set.mem_range_self k))
    have hconv := NormPreservingLifts.arbitrary_lifts_tendsto atTop
      (pR r ∘ projection) ((hpR r).comp hprojection) (fun k => VR r (psi k))
      (fun k => hVR r (psi k)) (fun k => nuA r (psi k))
      (fun k => sA r (psi k)) (fun k => sigma (psi k))
      (fun k => hsAmap r (psi k)) (fun k => hmap (psi k))
      (fun k => hsAmass r (psi k)) (fun k => hmass (psi k))
      (fun k => hAnull r (psi k)) 1 (by norm_num) (fun k => hAbound r (psi k))
      hfibre (NormPreservingLifts.signedFunctional mu).toWeakDual hrefconv
    apply Filter.tendsto_def.mpr
    intro A hA
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hconv.eventually hA)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (psi M)] with n hn hnJ
    obtain ⟨k, rfl⟩ := hnJ
    have hMk : M ≤ k := by
      by_contra hk
      exact (not_lt_of_ge hn) (hpsi (lt_of_not_ge hk))
    exact hM k hMk
  choose JA NA muA hJAsub hNAdis hNAsub hNAinf hmuA hmuApos hmuAneg hmuAF using hResidual
  have hBook : ∃ (I : Rows → Set ℕ) (J : Rows → Γ → Set ℕ) (N : Rows → Γ → Fin 2 → Set ℕ),
      (∀ r, I r = {n | (∃ q, code r < q ∧ (c q).m r = n) ∨
        (r = targetRow ∧ ∃ q, (c q).n = n)}) ∧
      (∀ r d, J r d = {n | ∃ q, code r < q ∧ rho q = d ∧ (c q).m r = n}) ∧
      (∀ r hr d e, N r d e = oldN r hr d e) ∧
      (∀ d e, N newRow d e =
        {n | ∃ q, code newRow < q ∧ rho q = d ∧ q % 2 = (e : ℕ) ∧ (c q).m newRow = n}) ∧
      (∀ r d, J r d ⊆ I r) ∧
      (∀ r d, Disjoint (N r d 0) (N r d 1)) ∧
      (∀ r d e, (J r d ∩ N r d e).Infinite) ∧
      (∀ r, (I r).Infinite) ∧
      (∀ r hr, I r ⊆ oldI r hr) ∧
      (∀ r hr d, J r d ⊆ oldJ r hr d) ∧
      (∀ r (A : Set K), IsClopen A → ∀ᶠ n in atTop ⊓ 𝓟 (I r),
        ∀ x y : splitCarrier Y Z,
          pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
          pR r x.1.1 = pR r y.1.1 → (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2) ∧
      (∀ r d, ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
            Measure.Regular mu.toJordanDecomposition.posPart ∧
            Measure.Regular mu.toJordanDecomposition.negPart ∧
            ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
              (∀ n, (sigma n).map (fun x => pR r x.1.1) = nuR r d n) →
              (∀ n, (sigma n).totalVariation univ = (nuR r d n).totalVariation univ) →
              Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
                (atTop ⊓ 𝓟 (J r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual)) ∧
          (∃ (JA : Rows → Set ℕ) (NA : Rows → Fin 2 → Set ℕ)
              (muA : Rows → SignedMeasure (splitCarrier Y Z)),
            ∀ r, JA r ⊆ I r ∧ Disjoint (NA r 0) (NA r 1) ∧
              (∀ e, NA r e ⊆ JA r) ∧ (∀ e, (JA r ∩ NA r e).Infinite) ∧
              (muA r).totalVariation.real univ ≤ 1 ∧
              Measure.Regular (muA r).toJordanDecomposition.posPart ∧
              Measure.Regular (muA r).toJordanDecomposition.negPart ∧
              ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
                (∀ n, (sigma n).map (fun x => pR r x.1.1) = nuA r n) →
                (∀ n, (sigma n).totalVariation univ = (nuA r n).totalVariation univ) →
                Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
                  (atTop ⊓ 𝓟 (JA r))
                  (𝓝 (NormPreservingLifts.signedFunctional (muA r)).toWeakDual)) :=
    ⟨I, J, N, fun _ => rfl, fun _ _ => rfl, hNold, hNnew, hJsub, hNdis, hC, hIinf, hIold, hJold, hFullE, hFJ,
      JA, NA, muA, fun r => ⟨hJAsub r, hNAdis r, hNAsub r, hNAinf r,
        hmuA r, hmuApos r, hmuAneg r, hmuAF r⟩⟩
  exact ⟨S, vP, hSsub, hS, href, birthS, birthMu, hBirthS, hBirthData,
    fun q => (hist q).val, c, hsuc, hstep, hn, hm, htests, havoid,
    Y, Z, hclosed, hY, hZ, hcov, hZdef, hYdef, hclosed, hsurj, haux, htarget, hnewAux,
    hnewTarget, hG, hGinf, hFuniform, hBook⟩


end D5.S3.Topology.Measures.SignedSplitSuccessor
