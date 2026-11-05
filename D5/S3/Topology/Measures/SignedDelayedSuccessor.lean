/- GID: D5/S3/Topology/Measures/SignedDelayedSuccessor
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedDelayedSuccessor
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Same-object delayed signed successor with final source and residual reservoirs -/

import D5.S3.Topology.Measures.SignedDelayedSplit

/-! One delayed split supplies final row sets and all signed residual births. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Topology.Measures.SignedDelayedSuccessor

open SignedSplitSuccessor SignedDelayedSplit

universe u v w

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

private lemma tendsto_on_strict_range {X : Type*} [TopologicalSpace X]
    (f : ℕ → X) (phi : ℕ → ℕ) (hphi : StrictMono phi) (x : X)
    (h : Tendsto (fun k => f (phi k)) atTop (𝓝 x)) :
    Tendsto f (atTop ⊓ 𝓟 (Set.range phi)) (𝓝 x) := by
  apply tendsto_def.mpr
  intro A hA
  obtain ⟨k, hk⟩ := eventually_atTop.mp (h hA)
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_ge_atTop (phi k)] with n hn hnS
  obtain ⟨j, rfl⟩ := hnS
  exact hk j (hphi.le_iff_le.mp hn)

set_option maxHeartbeats 1600000 in
-- One local construction assembles all row and residual cases before returning.
/-- Born signed input and the original strict old laws construct one delayed
successor, with a final enlarged I, the actual source-J replacement, unchanged
old N, and common regular signed references for all old and residual labels. -/
theorem exists_delayed_successor
    [T2Space K] [SecondCountableTopology K]
    [TopologicalSpace.MetrizableSpace K] [TotallyDisconnectedSpace K]
    {Rows : Type w} {Γ : Type*}
    (code : Rows → ℕ) (hcode : Function.Injective code)
    (newRow : Rows) (hNewCode : code newRow = 0)
    (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (B : ℕ → TopologicalSpace.Clopens K) (hB : Function.Surjective B)
    (rho : ℕ → Γ)
    (hRho : ∀ d (e : Fin 2), {q | rho q = d ∧ q % 2 = (e : ℕ)}.Infinite)
    (Base : Rows → Type v)
    [∀ r, TopologicalSpace (Base r)] [∀ r, CompactSpace (Base r)]
    [∀ r, T2Space (Base r)] [∀ r, ZeroDimensionalSpace (Base r)]
    [∀ r, MeasurableSpace (Base r)] [∀ r, BorelSpace (Base r)]
    (pR : ∀ r, K → Base r) (hpR : ∀ r, Continuous (pR r))
    (hpRsurj : ∀ r, Function.Surjective (pR r))
    (hNewProjection : Function.Injective (pR newRow))
    (VR : ∀ r, ℕ → Set (Base r)) (hVR : ∀ r n, IsClopen (VR r n))
    (hRdis : ∀ r, Pairwise (fun n m => Disjoint (pR r ⁻¹' VR r n) (pR r ⁻¹' VR r m)))
    (nuR : ∀ r, Γ → ℕ → SignedMeasure (Base r))
    (hRmass : ∀ r d n, (nuR r d n).totalVariation univ = 1)
    (hRnull : ∀ r d n, (nuR r d n).totalVariation (VR r n)ᶜ = 0)
    (_hRposreg : ∀ r d n, Measure.Regular (nuR r d n).toJordanDecomposition.posPart)
    (_hRnegreg : ∀ r d n, Measure.Regular (nuR r d n).toJordanDecomposition.negPart)
    (_hRpositive : ∀ r d n, (1 : ℝ) / 2 ≤ (nuR r d n).toJordanDecomposition.posPart.real univ)
    (nuA : ∀ r, ℕ → SignedMeasure (Base r))
    (hAmass : ∀ r n, (nuA r n).totalVariation univ = 1)
    (hAnull : ∀ r n, (nuA r n).totalVariation (VR r n)ᶜ = 0)
    (_hAposreg : ∀ r n, Measure.Regular (nuA r n).toJordanDecomposition.posPart)
    (_hAnegreg : ∀ r n, Measure.Regular (nuA r n).toJordanDecomposition.negPart)
    (_hApositive : ∀ r n, (1 : ℝ) / 2 ≤ (nuA r n).toJordanDecomposition.posPart.real univ)
    (oldI : ∀ r, r ≠ newRow → Set ℕ)
    (oldJ : ∀ r, r ≠ newRow → Γ → Set ℕ)
    (oldN : ∀ r, r ≠ newRow → Γ → Fin 2 → Set ℕ)
    (hOldA : ∀ r hr d, oldJ r hr d ⊆ oldI r hr)
    (hOldB : ∀ r hr d, Disjoint (oldN r hr d 0) (oldN r hr d 1))
    (hOldC : ∀ r hr d e, (oldJ r hr d ∩ oldN r hr d e).Infinite)
    (hOldE : ∀ r hr c, ∀ᶠ n in atTop ⊓ 𝓟 (oldI r hr), ∀ x y,
      pR r x ∈ VR r n → pR r y ∈ VR r n → pR r x = pR r y → coord c x = coord c y)
    (hOldF : ∀ r hr d (s : ℕ → SignedMeasure K),
      (∀ n, (s n).map (pR r) = nuR r d n) →
      (∀ n, (s n).totalVariation univ = (nuR r d n).totalVariation univ) →
      ∃ mu : SignedMeasure K, Tendsto
        (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
        (atTop ⊓ 𝓟 (oldJ r hr d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual))
    (targetRow : Rows) (hTargetOld : targetRow ≠ newRow)
    (sourceD targetD : Γ)
    (P Q : Set (Base targetRow)) (hP : IsClopen P) (hQ : IsClopen Q)
    (hPQ : Disjoint P Q)
    (y : ℕ → Base targetRow)
    (hyV : ∀ n, y n ∈ VR targetRow n) (hyQ : ∀ n, y n ∈ Q)
    (hdirac : ∀ n, nuR targetRow targetD n = (Measure.dirac (y n)).toSignedMeasure)
    (hSourceNull : ∀ n, (nuR targetRow sourceD n).totalVariation Pᶜ = 0) :
    ∃ (Y Z : Set K) (hclosed : IsClosed (splitCarrier Y Z)),
      letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
      IsClosed Y ∧ IsClosed Z ∧ Y ∪ Z = univ ∧
      Function.Surjective (fun x : splitCarrier Y Z => x.1.1) ∧
      Z ⊆ pR targetRow ⁻¹' Q ∧
      ∃ (M : Fin 2 → Set ℕ) (I : Rows → Set ℕ) (J : Rows → Γ → Set ℕ)
        (N : Rows → Γ → Fin 2 → Set ℕ)
        (c : ℕ → OrderedColumn Rows K),
        (∀ e, (M e).Infinite) ∧
        (∀ e, M e ⊆ oldJ targetRow hTargetOld sourceD ∩ oldN targetRow hTargetOld sourceD e) ∧
        (∀ r, I r = {n | (∃ q, code r < q ∧ (c q).m r = n) ∨
          (r = targetRow ∧ n ∈ M 0 ∪ M 1)}) ∧
        (∀ r d, J r d = (by
          classical
          exact if r = targetRow ∧ d = sourceD then M 0 ∪ M 1
            else (fun n => ∃ q, code r < q ∧ rho q = d ∧ (c q).m r = n))) ∧
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
                (atTop ⊓ 𝓟 (JA r)) (𝓝 (NormPreservingLifts.signedFunctional (muA r)).toWeakDual)) ∧
        (∃ C : TopologicalSpace.Clopens (splitCarrier Y Z),
          (∀ n ∈ M 0, ∀ x : splitCarrier Y Z, pR targetRow x.1.1 = y n → x ∈ C) ∧
          (∀ n ∈ M 1, ∀ x : splitCarrier Y Z, pR targetRow x.1.1 = y n → x ∉ C)) ∧
        (∀ q (t : SignedMeasure (splitCarrier Y Z)),
          t.map (fun x => pR targetRow x.1.1) = nuR targetRow targetD (c q).n →
          t.totalVariation univ = (nuR targetRow targetD (c q).n).totalVariation univ →
          (q % 2 = 0 → (13 : ℝ) / 48 < t {x | x.1.2 = true} ∧
            (1 : ℝ) / 6 < t {x | x.1.2 = true}) ∧
          (q % 2 ≠ 0 → t {x | x.1.2 = true} = 0)) ∧
        (∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (fun x => pR targetRow x.1.1) = nuR targetRow targetD n) →
          (∀ n, (sigma n).totalVariation univ = (nuR targetRow targetD n).totalVariation univ) →
          {n | (1 : ℝ) / 6 ≤ sigma n {x | x.1.2 = true}}.Infinite ∧
          {n | sigma n {x | x.1.2 = true} = 0}.Infinite) ∧
        (∀ r d n, ∃ t : SignedMeasure (splitCarrier Y Z),
          t.map (fun x => pR r x.1.1) = nuR r d n ∧
          t.totalVariation univ = (nuR r d n).totalVariation univ) ∧
        (∀ r n, ∃ t : SignedMeasure (splitCarrier Y Z),
          t.map (fun x => pR r x.1.1) = nuA r n ∧
          t.totalVariation univ = (nuA r n).totalVariation univ) := by
  classical
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  have hRbound (r : Rows) (d : Γ) (n : ℕ) : (nuR r d n).totalVariation.real univ ≤ 1 := by
    simp only [Measure.real, hRmass, ENNReal.toReal_one, le_refl]
  have hAbound (r : Rows) (n : ℕ) : (nuA r n).totalVariation.real univ ≤ 1 := by
    simp only [Measure.real, hAmass, ENNReal.toReal_one, le_refl]
  choose sR hsRmap hsRmass using fun r d n =>
    NormPreservingLiftExistence.exists_norm_preserving_lift (pR r) (hpR r) (hpRsurj r) (nuR r d n)
  choose oldMuR hOldRef using fun r hr d => hOldF r hr d (sR r d) (hsRmap r d) (hsRmass r d)
  have hBirth (d : Γ) := SignedWeakStarCompactness.exists_subsequence_tendsto_signedFunctional
    1 (by norm_num) (sR newRow d) (fun n => by
      simpa only [Measure.real, hsRmass] using hRbound newRow d n)
  choose phiBirth birthMu hPhiBirth hMuBirth hConvBirth using hBirth
  let birthS : Γ → Set ℕ := fun d => Set.range (phiBirth d)
  have hBirthS (d : Γ) : (birthS d).Infinite :=
    Set.infinite_range_of_injective (hPhiBirth d).injective
  have hBirthRef (d : Γ) : Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR newRow d n)).toWeakDual)
      (atTop ⊓ 𝓟 (birthS d)) (𝓝 (NormPreservingLifts.signedFunctional (birthMu d)).toWeakDual) :=
    tendsto_on_strict_range _ _ (hPhiBirth d) _ (hConvBirth d)
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
  obtain ⟨z, T, history, c, M, Y, Z, hclosed, hsuc, hstep, hn, hm, htests, hliteral,
    hMinf, hMsub, hY, hZ, hcov, hsurj, hZQ, hnewAux, hMside, hWitness,
    hG, hSourceF, hFuniform⟩ :=
    exists_internal_delayed_split code hcode coord hsep B hB rho
      (oldI targetRow hTargetOld) (oldJ targetRow hTargetOld sourceD)
      (oldN targetRow hTargetOld sourceD) (hOldA targetRow hTargetOld sourceD)
      (hOldC targetRow hTargetOld sourceD) (hOldB targetRow hTargetOld sourceD)
      (pR targetRow) (hpR targetRow) (hpRsurj targetRow)
      (VR targetRow) (hVR targetRow) Q hQ y hyV hyQ (nuR targetRow targetD) hdirac
      (hOldE targetRow hTargetOld) P hP hPQ (nuR targetRow sourceD)
      (hRbound targetRow sourceD) hSourceNull (hRnull targetRow sourceD)
      (hOldF targetRow hTargetOld sourceD)
      Base pR hpR hpRsurj VR hVR nuR hRbound sR muR hsRmap hsRmass hRnull
      pool hpool hRE hRref hRdis (hRdis targetRow)
  letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
  let projection : splitCarrier Y Z → K := fun x => x.1.1
  have hprojection : Continuous projection := continuous_fst.comp continuous_subtype_val
  let I : Rows → Set ℕ := fun r => {n | (∃ q, code r < q ∧ (c q).m r = n) ∨
    (r = targetRow ∧ n ∈ M 0 ∪ M 1)}
  let J0 : Rows → Γ → Set ℕ := fun r d =>
    {n | ∃ q, code r < q ∧ rho q = d ∧ (c q).m r = n}
  let J : Rows → Γ → Set ℕ := fun r d =>
    if r = targetRow ∧ d = sourceD then M 0 ∪ M 1 else J0 r d
  let N : Rows → Γ → Fin 2 → Set ℕ := fun r d e =>
    if hr : r = newRow then {n | ∃ q, code r < q ∧ rho q = d ∧
      q % 2 = (e : ℕ) ∧ (c q).m r = n}
    else oldN r hr d e
  have hMold : M 0 ∪ M 1 ⊆ oldJ targetRow hTargetOld sourceD :=
    union_subset ((hMsub 0).trans inter_subset_left) ((hMsub 1).trans inter_subset_left)
  have hJsub (r : Rows) (d : Γ) : J r d ⊆ I r := by
    by_cases he : r = targetRow ∧ d = sourceD
    · obtain ⟨heR, heD⟩ := he
      subst r
      subst d
      intro n hn
      exact Or.inr ⟨rfl, by simpa [J] using hn⟩
    · simp only [J, if_neg he]
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
  have hC0 (r : Rows) (d : Γ) (e : Fin 2) : (J0 r d ∩ N r d e).Infinite := by
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
  have hC (r : Rows) (d : Γ) (e : Fin 2) : (J r d ∩ N r d e).Infinite := by
    by_cases he : r = targetRow ∧ d = sourceD
    · obtain ⟨heR, heD⟩ := he
      subst r
      subst d
      apply (hMinf e).mono
      intro n hnM
      refine ⟨?_, ?_⟩
      · simp only [J, ite_eq_left (show targetRow = targetRow ∧ sourceD = sourceD from ⟨rfl, rfl⟩)]
        fin_cases e
        · exact Or.inl hnM
        · exact Or.inr hnM
      · rw [hNold targetRow hTargetOld]
        exact (hMsub e hnM).2
    · simpa only [J, if_neg he] using hC0 r d e
  have hIinf (r : Rows) : (I r).Infinite := by
    apply (hC0 r (rho 0) 0).mono
    rintro n ⟨⟨q, hq, _, hqn⟩, _⟩
    exact Or.inl ⟨q, hq, hqn⟩
  have hIold (r : Rows) (hr : r ≠ newRow) : I r ⊆ oldI r hr := by
    rintro n (⟨q, _, rfl⟩ | ⟨heR, hnM⟩)
    · exact hOldA r hr (rho q) (hOldPool r hr q).1
    · subst r
      exact hOldA targetRow hr sourceD (hMold hnM)
  have hJold (r : Rows) (hr : r ≠ newRow) (d : Γ) : J r d ⊆ oldJ r hr d := by
    by_cases he : r = targetRow ∧ d = sourceD
    · obtain ⟨heR, heD⟩ := he
      subst r
      subst d
      simpa [J] using hMold
    · simp only [J, if_neg he]
      rintro n ⟨q, _, hlabel, rfl⟩
      simpa only [hlabel] using (hOldPool r hr q).1
  have hFullE (r : Rows) (A : Set K) (hA : IsClopen A) :
      ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
        pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
        pR r x.1.1 = pR r y.1.1 →
        (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2 := by
    have hOldPart : ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : K,
        pR r x ∈ VR r n → pR r y ∈ VR r n → pR r x = pR r y → (x ∈ A ↔ y ∈ A) := by
      by_cases hr : r = newRow
      · subst r
        exact Eventually.of_forall fun _ x y _ _ hxy => iff_of_eq (congrArg (fun x => x ∈ A)
          (hNewProjection hxy))
      · exact (eventually_clopen_fibre (atTop ⊓ 𝓟 (oldI r hr)) coord hsep
          (pR r) (VR r) (hOldE r hr) hA).filter_mono
          (inf_le_inf le_rfl (Filter.principal_mono.mpr (hIold r hr)))
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_inf_principal.mp hOldPart,
      eventually_ge_atTop ((c (code r + 1)).m r)] with n hold hn hnI
    intro x w hx hw hxw
    refine ⟨hold hnI x.1.1 w.1.1 hx hw hxw, ?_⟩
    rcases hnI with ⟨q, hq, rfl⟩ | ⟨heR, hnM⟩
    · exact hnewAux r q hq x w hx hw hxw
    · subst r
      exact hMside n hnM x w hx hw hxw
  have hFJ0 (r : Rows) (d : Γ) :
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (pR r ∘ projection) = nuR r d n) →
          (∀ n, (sigma n).totalVariation univ = (nuR r d n).totalVariation univ) →
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
            (atTop ⊓ 𝓟 (J0 r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
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
    have hpsiRange : Set.range psi = J0 r d := by
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
  have hFJ (r : Rows) (d : Γ) :
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (pR r ∘ projection) = nuR r d n) →
          (∀ n, (sigma n).totalVariation univ = (nuR r d n).totalVariation univ) →
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
            (atTop ⊓ 𝓟 (J r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    by_cases he : r = targetRow ∧ d = sourceD
    · obtain ⟨heR, heD⟩ := he
      subst r
      subst d
      simpa [J, projection, Function.comp_def] using hSourceF
    · simpa only [J, if_neg he] using hFJ0 r d
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
  have hGinf (sigma : ℕ → SignedMeasure (splitCarrier Y Z))
      (hmap : ∀ n, (sigma n).map (pR targetRow ∘ projection) = nuR targetRow targetD n)
      (hmass : ∀ n, (sigma n).totalVariation univ = (nuR targetRow targetD n).totalVariation univ) :
      {n | (1 : ℝ) / 6 ≤ sigma n {x | x.1.2 = true}}.Infinite ∧
        {n | sigma n {x | x.1.2 = true} = 0}.Infinite := by
    have heven : Function.Injective (fun k : ℕ => 2 * k) := by
      intro a b h
      change 2 * a = 2 * b at h
      omega
    have hodd : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b h
      change 2 * a + 1 = 2 * b + 1 at h
      omega
    have hi0 : (Set.range (fun k : ℕ => (c (2 * k)).n)).Infinite :=
      Set.infinite_range_of_injective (hn.injective.comp heven)
    have hi1 : (Set.range (fun k : ℕ => (c (2 * k + 1)).n)).Infinite :=
      Set.infinite_range_of_injective (hn.injective.comp hodd)
    constructor
    · apply hi0.mono
      rintro n ⟨k, rfl⟩
      exact ((hG (2 * k) (sigma _) (hmap _) (hmass _)).1 (by omega)).2.le
    · apply hi1.mono
      rintro n ⟨k, rfl⟩
      exact (hG (2 * k + 1) (sigma _) (hmap _) (hmass _)).2 (by omega)
  have hRealLifts (r : Rows) (d : Γ) (n : ℕ) :=
    NormPreservingLiftExistence.exists_norm_preserving_lift (pR r ∘ projection)
      ((hpR r).comp hprojection) ((hpRsurj r).comp hsurj) (nuR r d n)
  refine ⟨Y, Z, hclosed, hY, hZ, hcov, hsurj, hZQ, M, I, J, N, c,
    hMinf, hMsub, (fun _ => rfl), (fun _ _ => rfl), hNold, hNnew,
    hJsub, hNdis, hC, hIinf, hIold, hJold, hFullE, hFJ, ?_, hWitness,
    hG, hGinf, hRealLifts, (fun r n => ⟨sA r n, hsAmap r n, hsAmass r n⟩)⟩
  exact ⟨JA, NA, muA, fun r => ⟨hJAsub r, hNAdis r, hNAsub r, hNAinf r,
    hmuA r, hmuApos r, hmuAneg r, hmuAF r⟩⟩

end D5.S3.Topology.Measures.SignedDelayedSuccessor
