/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalDelayed
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalDelayed
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Same-preparation delayed ordinal successor with permanent reservoirs and whole fibres. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor
import D5.S3.Topology.Measures.SignedDelayedSplit

/-! One actual delayed split fills the existing ordinal successor interface. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor

open SignedProperLimit SignedBirthEnumeration
open D5.S3.Topology.Measures SignedSplitSuccessor

variable {a : Ordinal.{0}} {H : Prefix (Order.succ a)} {ha : ω ≤ a}
  {P : Predecessor H ha} {launch : Launch a} (Q : Prepared H ha P launch)

/-- Eligibility reads two distinct original whole sequences of one already born
row. Only clopens, points and support proofs are supplied, never successor F. -/
structure DelayedTask where
  row : Rows a
  old : row ≠ newRow a ha
  source : Coord a
  target : Coord a
  distinct : source ≠ target
  sourceSupport : Clopens (Base H row)
  targetSupport : Clopens (Base H row)
  disjoint : Disjoint (sourceSupport : Set (Base H row)) targetSupport
  y : ℕ → Base H row
  inSupport : ∀ n, y n ∈ (Q.V row).clopen n
  inTarget : ∀ n, y n ∈ targetSupport
  dirac : ∀ n, Q.measure row (oldCol target) n = (Measure.dirac (y n)).toSignedMeasure
  sourceNull : ∀ n, (Q.measure row (oldCol source) n).totalVariation
    (sourceSupport : Set (Base H row))ᶜ = 0

/-- Extra certificates refer to the identical executed Result. Its A-F and G
remain the common interface; original birth reservoirs are never replaced. -/
def DelayedCertificate (D : DelayedTask Q)
    (R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩) : Prop :=
  ∃ M : Fin 2 → Set ℕ,
    R.J D.row (oldCol D.source) = M 0 ∪ M 1 ∧
    (∀ e, (M e).Infinite) ∧
    (∀ e, M e ⊆ P.J D.row D.old D.source ∩ P.oldN D.row D.old D.source e) ∧
    (∃ C : Clopens R.coordinates.carrier,
      (∀ n ∈ M 0, ∀ x : R.coordinates.carrier,
        restrict (D.row.2.2.trans (Order.le_succ a)) x.1 = (D.y n).1 → x ∈ C) ∧
      (∀ n ∈ M 1, ∀ x : R.coordinates.carrier,
        restrict (D.row.2.2.trans (Order.le_succ a)) x.1 = (D.y n).1 → x ∉ C)) ∧
    (∀ q (s : SignedMeasure R.coordinates.carrier),
      s.map (R.literalProjection D.row) = Q.measure D.row (oldCol D.target) (R.column q).n →
      s.totalVariation univ = 1 →
      (q % 2 = 0 → (13 : ℝ) / 48 < s R.quantitativeClopen) ∧
      (q % 2 ≠ 0 → s R.quantitativeClopen = 0))

set_option maxHeartbeats 2400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Execute the delayed supplier once, retain every old birth, and fill every
old, new and residual field of the same ordinal successor Result. -/
theorem exists_delayed_result (D : DelayedTask Q) :
    ∃ R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩, DelayedCertificate Q D R := by
  classical
  letI : Countable (Coord a) := (Cardinal.countable_Iio_of_lt_omega_one P.proper).to_subtype
  letI : MetricSpace (K H) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨code, rho, hcode, hzero, hrho⟩ := exists_codes ha P.proper
  let coord : Coord a → C(K H, Bool) := fun c =>
    ⟨fun x => x.1 c, (continuous_apply c).comp continuous_subtype_val⟩
  have hsep : Injective (fun x : K H => fun c => coord c x) := by
    intro x y h
    exact Subtype.ext (funext (congrFun h))
  let nuR := fun (r : Rows a) (d : Coord a) => Q.measure r (oldCol d)
  let nuA := fun r => Q.measure r (lastCol a)
  choose sR hsRmap hsRmass using fun r d n =>
    NormPreservingLiftExistence.exists_norm_preserving_lift (projection H r)
      (projection H r).continuous (projection_onto H r) (nuR r d n)
  choose oldMuR hOldRef using fun r hr d =>
    Q.old_f r hr d (sR r d) (hsRmap r d) (hsRmass r d)
  have hRbound (r : Rows a) (d : Coord a) (n : ℕ) :
      (nuR r d n).totalVariation.real univ ≤ 1 := by simp [nuR, Measure.real, Q.mass]
  have hAbound (r : Rows a) (n : ℕ) :
      (nuA r n).totalVariation.real univ ≤ 1 := by simp [nuA, Measure.real, Q.mass]
  have hAnull (r : Rows a) (n : ℕ) :
      (nuA r n).totalVariation ((Q.V r).clopen n : Set (Base H r))ᶜ = 0 := Q.null r _ n
  have hBirthBound (d : Coord a) (n : ℕ) : (sR (newRow a ha) d n).totalVariation.real univ ≤ 1 := by
    simpa only [Measure.real, hsRmass] using hRbound (newRow a ha) d n
  have hBirthCluster (d : Coord a) := SignedWeakStarCompactness.exists_subsequence_tendsto_signedFunctional
    1 (by norm_num) (sR (newRow a ha) d) (hBirthBound d)
  choose phiBirth birthMu hPhiBirth hMuBirth hConvBirth using hBirthCluster
  let birthS : Coord a → Set ℕ := fun d => Set.range (phiBirth d)
  have hBirthS (d : Coord a) : (birthS d).Infinite := Set.infinite_range_of_injective (hPhiBirth d).injective
  have hBirthRef (d : Coord a) : Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR (newRow a ha) d n)).toWeakDual)
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
  let muR : Rows a → Coord a → SignedMeasure (K H) := ordinaryReference (newRow a ha) oldMuR birthMu
  let pool : Rows a → ℕ → Set ℕ := ordinaryPool (newRow a ha) P.J P.oldN birthS rho
  have hpool : ∀ r q, (pool r q).Infinite := by
    intro r q
    by_cases hr : r = (newRow a ha)
    · subst r
      simpa [pool, ordinaryPool] using hBirthS (rho q)
    · simpa only [pool, ordinaryPool, dite_eq_right hr, Predecessor.oldN] using
        P.C r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩
  have hRE : ∀ r q c, ∀ᶠ n in atTop ⊓ 𝓟 (pool r q), ∀ x y,
      projection H r x ∈ ((Q.V r).clopen n : Set (Base H r)) → projection H r y ∈ ((Q.V r).clopen n : Set (Base H r)) → projection H r x = projection H r y → coord c x = coord c y := by
    intro r q c
    by_cases hr : r = (newRow a ha)
    · subst r
      exact Filter.Eventually.of_forall (fun _ x y _ _ hxy => congrArg (coord c) hxy)
    · have hsub : pool r q ⊆ P.I r hr := by
        intro n hn
        have hn' : n ∈ P.J r hr (rho q) ∩
            P.oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩ := by
          simpa only [pool, ordinaryPool, dite_eq_right hr] using hn
        exact P.A r hr (rho q) hn'.1
      exact (Q.old_e r hr c).filter_mono (inf_le_inf le_rfl (Filter.principal_mono.mpr hsub))
  have hRref : ∀ r q, Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR r (rho q) n)).toWeakDual)
      (atTop ⊓ 𝓟 (pool r q)) (𝓝 (NormPreservingLifts.signedFunctional (muR r (rho q))).toWeakDual) := by
    intro r q
    by_cases hr : r = (newRow a ha)
    · subst r
      simpa [pool, ordinaryPool, muR, ordinaryReference] using hBirthRef (rho q)
    · have hsub : pool r q ⊆ P.J r hr (rho q) := by
        intro n hn
        have hn' : n ∈ P.J r hr (rho q) ∩
            P.oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩ := by
          simpa only [pool, ordinaryPool, dite_eq_right hr] using hn
        exact hn'.1
      simpa only [muR, ordinaryReference, dite_eq_right hr] using
        (hOldRef r hr (rho q)).mono_left (inf_le_inf le_rfl (Filter.principal_mono.mpr hsub))
  obtain ⟨z, T, hist, c, M, Y, Z, hclosed, hsuc, hstep, hc, hm, htests, hliteral,
    hMinf, hMsub, hY, hZ, hcover, honto, hZQ, hnewAux, hMside, hWitness,
    hG, hSourceF, hFuniform⟩ :=
    SignedDelayedSplit.exists_internal_delayed_split code hcode coord hsep Q.B Q.Bonto rho
      (P.I D.row D.old) (P.J D.row D.old D.source) (P.oldN D.row D.old D.source)
      (P.A D.row D.old D.source) (P.C D.row D.old D.source) (P.B D.row D.old D.source)
      (projection H D.row) (projection H D.row).continuous (projection_onto H D.row)
      (fun n => ((Q.V D.row).clopen n : Set (Base H D.row)))
      (fun n => ((Q.V D.row).clopen n).isClopen)
      D.targetSupport D.targetSupport.isClopen D.y D.inSupport D.inTarget
      (Q.measure D.row (oldCol D.target)) D.dirac (Q.old_e D.row D.old)
      D.sourceSupport D.sourceSupport.isClopen D.disjoint
      (Q.measure D.row (oldCol D.source)) (hRbound D.row D.source)
      D.sourceNull (Q.null D.row (oldCol D.source))
      (fun s hmap hmass => Q.old_f D.row D.old D.source s hmap hmass)
      (Base H) (fun r => projection H r) (fun r => (projection H r).continuous)
      (fun r => projection_onto H r)
      (fun r n => ((Q.V r).clopen n : Set (Base H r)))
      (fun r n => ((Q.V r).clopen n).isClopen)
      nuR hRbound sR muR hsRmap hsRmass (fun r d => Q.null r (oldCol d))
      pool hpool hRE hRref
      (fun r _ _ h => ((Q.V r).disjoint h).preimage (projection H r))
      (fun _ _ h => ((Q.V D.row).disjoint h).preimage (projection H D.row))
  letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
  let pj : splitCarrier Y Z → K H := fun x => x.1.1
  have hpj : Continuous pj := continuous_fst.comp continuous_subtype_val
  let I0 : Rows a → Set ℕ := fun r => {n | ∃ q, code r < q ∧ (c q).m r = n}
  let J0 : Rows a → Coord a → Set ℕ := fun r d =>
    {n | ∃ q, code r < q ∧ rho q = d ∧ (c q).m r = n}
  let N0 : Rows a → Coord a → Fin 2 → Set ℕ := fun r d e =>
    if hr : r = newRow a ha then {n | ∃ q, code r < q ∧ rho q = d ∧
      q % 2 = (e : ℕ) ∧ (c q).m r = n}
    else P.oldN r hr d e
  have hOldPool (r : Rows a) (hr : r ≠ newRow a ha) (q : ℕ) :
      (c q).m r ∈ P.J r hr (rho q) ∩
        P.oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩ := by
    have hmem := ((hstep q).2.2.2.2.2 r).1
    simpa only [pool, ordinaryPool, dite_eq_right hr] using hmem
  have hNold (r : Rows a) (hr : r ≠ newRow a ha) (d : Coord a) (e : Fin 2) :
      N0 r d e = P.oldN r hr d e := by simp only [N0, dite_eq_right hr]
  have hNnew (d : Coord a) (e : Fin 2) : N0 (newRow a ha) d e =
      {n | ∃ q, 0 < q ∧ rho q = d ∧ q % 2 = (e : ℕ) ∧ (c q).m (newRow a ha) = n} := by
    simp only [N0, dite_eq_left rfl, hzero]
  have hNdis (r : Rows a) (d : Coord a) : Disjoint (N0 r d 0) (N0 r d 1) := by
    by_cases hr : r = newRow a ha
    · simp only [N0, dite_eq_left hr]
      rw [Set.disjoint_left]
      rintro n ⟨q, _, _, hq, heq⟩ ⟨s, _, _, hs, hes⟩
      have hqs : q = s := (hm r).injective (heq.trans hes.symm)
      subst s
      change q % 2 = 0 at hq
      change q % 2 = 1 at hs
      omega
    · rw [hNold r hr, hNold r hr]
      exact P.B r hr d
  have hC0 (r : Rows a) (d : Coord a) (e : Fin 2) : (J0 r d ∩ N0 r d e).Infinite := by
    have hinf : {q | code r < q ∧ rho q = d ∧ q % 2 = (e : ℕ)}.Infinite := by
      have h := (hrho d e).sdiff (Set.finite_Iic (code r))
      exact h.mono (fun q hq => ⟨by simpa only [Set.mem_Iic, not_le] using hq.2,
        hq.1.1, hq.1.2⟩)
    apply (hinf.image (hm r).injective.injOn).mono
    rintro n ⟨q, ⟨hq, hlabel, hparity⟩, rfl⟩
    refine ⟨⟨q, hq, hlabel, rfl⟩, ?_⟩
    by_cases hr : r = newRow a ha
    · simp only [N0, dite_eq_left hr]
      exact ⟨q, hq, hlabel, hparity, rfl⟩
    · rw [hNold r hr]
      have he : (⟨q % 2, Nat.mod_lt q (by decide)⟩ : Fin 2) = e := Fin.ext hparity
      have hmem := (hOldPool r hr q).2
      simpa only [hlabel, he] using hmem
  have hJ0sub (r : Rows a) (d : Coord a) : J0 r d ⊆ I0 r := by
    rintro n ⟨q, hq, _, rfl⟩
    exact ⟨q, hq, rfl⟩
  have hI0inf (r : Rows a) : (I0 r).Infinite :=
    (hC0 r (rho 0) 0).mono (fun _ hn => hJ0sub r (rho 0) hn.1)
  have hI0old (r : Rows a) (hr : r ≠ newRow a ha) : I0 r ⊆ P.I r hr := by
    rintro n ⟨q, _, rfl⟩
    exact P.A r hr (rho q) (hOldPool r hr q).1
  have hJ0old (r : Rows a) (hr : r ≠ newRow a ha) (d : Coord a) :
      J0 r d ⊆ P.J r hr d := by
    rintro n ⟨q, _, hlabel, rfl⟩
    simpa only [hlabel] using (hOldPool r hr q).1
  have hAuxE (r : Rows a) (A : Set (K H)) (hA : IsClopen A) :
      ∀ᶠ n in along (I0 r), ∀ x y : splitCarrier Y Z,
        projection H r x.1.1 ∈ (Q.V r).clopen n →
        projection H r y.1.1 ∈ (Q.V r).clopen n →
        projection H r x.1.1 = projection H r y.1.1 →
        (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2 := by
    obtain ⟨j, hj⟩ := Q.Bonto ⟨A, hA⟩
    let b := max j (code r + 1)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop ((c b).m r)] with n hn hnI
    intro x y hx hy hxy
    obtain ⟨q, hq, rfl⟩ := hnI
    have hbq : b ≤ q := by
      by_contra hnq
      exact (not_lt_of_ge hn) (hm r (lt_of_not_ge hnq))
    have hAF : (⟨A, hA⟩ : Clopens (K H)) ∈ (c q).F := by
      simpa only [hj] using (htests j q ((le_max_left j _).trans hbq)).2
    exact ⟨((hstep q).2.2.2.2.2 r).2.2.2.1 ⟨A, hA⟩ hAF x.1.1 y.1.1 hx hy hxy,
      hnewAux r q hq x y hx hy hxy⟩
  let S : Set ℕ := M 0 ∪ M 1
  have hSJ : S ⊆ P.J D.row D.old D.source := union_subset
    ((hMsub 0).trans inter_subset_left) ((hMsub 1).trans inter_subset_left)
  have hSI : S ⊆ P.I D.row D.old := hSJ.trans (P.A D.row D.old D.source)
  let I : Rows a → Set ℕ := fun r => if r = D.row then I0 r ∪ S else I0 r
  let JO : Rows a → Coord a → Set ℕ := fun r d =>
    if r = D.row ∧ d = D.source then S else J0 r d
  have hI0I (r : Rows a) : I0 r ⊆ I r := by
    by_cases hr : r = D.row <;> simp only [I, hr, ite_true, ite_false]
    · exact subset_union_left
    · exact subset_rfl
  have hJsub (r : Rows a) (d : Coord a) : JO r d ⊆ I r := by
    by_cases h : r = D.row ∧ d = D.source
    · rcases h with ⟨rfl, rfl⟩
      simpa only [JO, I, and_self, ite_true] using (subset_union_right : S ⊆ I0 D.row ∪ S)
    · simpa only [JO, ite_eq_right h] using (hJ0sub r d).trans (hI0I r)
  have hC (r : Rows a) (d : Coord a) (e : Fin 2) : (JO r d ∩ N0 r d e).Infinite := by
    by_cases h : r = D.row ∧ d = D.source
    · rcases h with ⟨rfl, rfl⟩
      apply (hMinf e).mono
      intro n hn
      refine ⟨?_, ?_⟩
      · simp only [JO, and_self, ite_true]
        rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
        · exact Or.inl hn
        · exact Or.inr hn
      · rw [hNold D.row D.old]
        exact (hMsub e hn).2
    · simpa only [JO, ite_eq_right h] using hC0 r d e
  have hIinf (r : Rows a) : (I r).Infinite := (hI0inf r).mono (hI0I r)
  have hIold (r : Rows a) (hr : r ≠ newRow a ha) : I r ⊆ P.I r hr := by
    by_cases he : r = D.row
    · subst r
      simpa only [I, ite_eq_left rfl] using union_subset (hI0old D.row hr) hSI
    · simpa only [I, ite_eq_right he] using hI0old r hr
  have hJold (r : Rows a) (hr : r ≠ newRow a ha) (d : Coord a) :
      JO r d ⊆ P.J r hr d := by
    by_cases he : r = D.row ∧ d = D.source
    · rcases he with ⟨rfl, rfl⟩
      simpa only [JO, and_self, ite_true] using hSJ
    · simpa only [JO, ite_eq_right he] using hJ0old r hr d
  have hFullE (r : Rows a) (A : Set (K H)) (hA : IsClopen A) :
      ∀ᶠ n in along (I r), ∀ x y : splitCarrier Y Z,
        projection H r x.1.1 ∈ (Q.V r).clopen n →
        projection H r y.1.1 ∈ (Q.V r).clopen n →
        projection H r x.1.1 = projection H r y.1.1 →
        (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2 := by
    by_cases hr : r = D.row
    · subst r
      have hOld := (eventually_clopen_fibre (along (P.I D.row D.old)) coord hsep
        (projection H D.row) (fun n => ((Q.V D.row).clopen n : Set (Base H D.row)))
        (Q.old_e D.row D.old) hA).filter_mono
          (inf_le_inf le_rfl (Filter.principal_mono.mpr hSI))
      have hBoth : ∀ᶠ n in along S, ∀ x y : splitCarrier Y Z,
          projection H D.row x.1.1 ∈ (Q.V D.row).clopen n →
          projection H D.row y.1.1 ∈ (Q.V D.row).clopen n →
          projection H D.row x.1.1 = projection H D.row y.1.1 →
          (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2 := by
        filter_upwards [hOld, (show ∀ᶠ n in along S, n ∈ S from
          eventually_inf_principal.mpr (Eventually.of_forall (fun _ hn => hn)))] with n hn hnS
        intro x y hx hy hxy
        exact ⟨hn x.1.1 y.1.1 hx hy hxy, hMside n hnS x y hx hy hxy⟩
      obtain ⟨b, hb⟩ := eventually_atTop.mp (eventually_inf_principal.mp (hAuxE D.row A hA))
      obtain ⟨d, hd⟩ := eventually_atTop.mp (eventually_inf_principal.mp hBoth)
      apply eventually_inf_principal.mpr
      filter_upwards [eventually_ge_atTop (max b d)] with n hn hnI
      have hnI' : n ∈ I0 D.row ∪ S := by simpa only [I, ite_eq_left rfl] using hnI
      rcases hnI' with hnI | hnI
      · exact hb n ((le_max_left b d).trans hn) hnI
      · exact hd n ((le_max_right b d).trans hn) hnI
    · simpa only [I, ite_eq_right hr] using hAuxE r A hA
  have hF0 (r : Rows a) (d : Coord a) :
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (fun x : splitCarrier Y Z => projection H r x.1.1) = nuR r d n) →
          (∀ n, (sigma n).totalVariation univ = (nuR r d n).totalVariation univ) →
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
            (atTop ⊓ 𝓟 (J0 r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    let P : Set ℕ := {q | code r < q ∧ rho q = d}
    have hP : P.Infinite := by
      apply ((hrho d 0).sdiff (Set.finite_Iic (code r))).mono
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
  have hFJ (r : Rows a) (d : Coord a) :
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (fun x : splitCarrier Y Z => projection H r x.1.1) = nuR r d n) →
          (∀ n, (sigma n).totalVariation univ = (nuR r d n).totalVariation univ) →
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
            (along (JO r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    by_cases he : r = D.row ∧ d = D.source
    · rcases he with ⟨rfl, rfl⟩
      simpa only [JO, and_self, ite_true, along] using hSourceF
    · simpa only [JO, ite_eq_right he, along] using hF0 r d
  let splitCoord : Option (Coord a) → C(splitCarrier Y Z, Bool) := fun c =>
    match c with
    | none => ⟨fun x => x.1.2, continuous_snd.comp continuous_subtype_val⟩
    | some c => ⟨fun x => coord c x.1.1, (coord c).continuous.comp hpj⟩
  have hSplitSep : Injective
      (fun x : splitCarrier Y Z => fun c => splitCoord c x) := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · apply hsep
      funext c
      exact congrFun hxy (some c)
    · exact congrFun hxy none
  have hSplitE (r : Rows a) (c : Option (Coord a)) :
      ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
        projection H r x.1.1 ∈ ((Q.V r).clopen n : Set (Base H r)) → projection H r y.1.1 ∈ ((Q.V r).clopen n : Set (Base H r)) →
        projection H r x.1.1 = projection H r y.1.1 → splitCoord c x = splitCoord c y := by
    cases c with
    | none =>
      filter_upwards [hFullE r ∅ isClopen_empty] with n hn
      intro x y hx hy hxy
      exact (hn x y hx hy hxy).2
    | some c =>
      let A : Set (K H) := coord c ⁻¹' {true}
      have hA : IsClopen A := (isClopen_discrete ({true} : Set Bool)).preimage (coord c).continuous
      filter_upwards [hFullE r A hA] with n hn
      intro x y hx hy hxy
      apply bool_eq_of_true_iff
      change (coord c x.1.1 = true ↔ coord c y.1.1 = true)
      simpa only [A, mem_preimage, mem_singleton_iff] using (hn x y hx hy hxy).1
  have hLocE (r : Rows a) (f : LocallyConstant (splitCarrier Y Z) ℝ) :
      ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
        projection H r x.1.1 ∈ ((Q.V r).clopen n : Set (Base H r)) → projection H r y.1.1 ∈ ((Q.V r).clopen n : Set (Base H r)) →
        projection H r x.1.1 = projection H r y.1.1 → f x = f y := by
    have hpieces : ∀ a ∈ f.range_finite.toFinset,
        ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
          projection H r x.1.1 ∈ ((Q.V r).clopen n : Set (Base H r)) → projection H r y.1.1 ∈ ((Q.V r).clopen n : Set (Base H r)) →
          projection H r x.1.1 = projection H r y.1.1 → (f x = a ↔ f y = a) := by
      intro a _
      exact eventually_clopen_fibre (atTop ⊓ 𝓟 (I r)) splitCoord hSplitSep
        (fun x : splitCarrier Y Z => projection H r x.1.1) (fun n => ((Q.V r).clopen n : Set (Base H r))) (hSplitE r) (f.isLocallyConstant.isClopen_fiber a)
    filter_upwards [(Filter.eventually_all_finset f.range_finite.toFinset).mpr hpieces] with n hn
    intro x y hx hy hxy
    exact ((hn (f x) (f.range_finite.mem_toFinset.mpr ⟨x, rfl⟩) x y hx hy hxy).mp rfl).symm
  letI : MetricSpace (splitCarrier Y Z) := TopologicalSpace.metrizableSpaceMetric _
  have hResidualLifts (r : Rows a) (n : ℕ) :=
    NormPreservingLiftExistence.exists_norm_preserving_lift (fun x : splitCarrier Y Z => projection H r x.1.1)
      ((projection H r).continuous.comp hpj) ((projection_onto H r).comp honto) (nuA r n)
  choose sA hsAmap hsAmass using hResidualLifts
  have hResidual (r : Rows a) :
      ∃ (JA : Set ℕ) (NA : Fin 2 → Set ℕ) (mu : SignedMeasure (splitCarrier Y Z)),
        JA ⊆ I r ∧ Disjoint (NA 0) (NA 1) ∧
        (∀ e, NA e ⊆ JA) ∧ (∀ e, (JA ∩ NA e).Infinite) ∧
        mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (fun x : splitCarrier Y Z => projection H r x.1.1) = nuA r n) →
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
      have hinj : Injective (fun k => psi (2 * k + (e : ℕ))) :=
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
          projection H r x.1.1 ∈ ((Q.V r).clopen (psi k) : Set (Base H r)) → projection H r y.1.1 ∈ ((Q.V r).clopen (psi k) : Set (Base H r)) →
          projection H r x.1.1 = projection H r y.1.1 → f x = f y := by
      filter_upwards [hpsi.tendsto_atTop.eventually (eventually_inf_principal.mp (hLocE r f))]
        with k hk
      exact hk (hJAsub (Set.mem_range_self k))
    have hconv := NormPreservingLifts.arbitrary_lifts_tendsto atTop
      (fun x : splitCarrier Y Z => projection H r x.1.1) ((projection H r).continuous.comp hpj) (fun k => ((Q.V r).clopen (psi k) : Set (Base H r)))
      (fun k => ((Q.V r).clopen (psi k)).isClopen) (fun k => nuA r (psi k))
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
  obtain ⟨geometry⟩ := SignedSuccessorCoordinates.exists_successor_coordinates H Y Z hY hZ hcover
  let J : Rows a → Cols a → Set ℕ := fun r d =>
    if hd : d.1 < a then JO r ⟨d.1, hd⟩ else JA r
  let N : Rows a → Cols a → Fin 2 → Set ℕ := fun r d =>
    if hd : d.1 < a then N0 r ⟨d.1, hd⟩ else NA r
  let R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩ := {
    Y := Y, Z := Z, closed := hclosed, closedY := hY, closedZ := hZ, cover := hcover
    coordinates := geometry, I := I, J := J, N := N, rho := rho, rho_cofinal := hrho
    column := c, k_mono := hc
    oldN := by
      intro r hr d e
      have hd : d.1 < a := d.2
      simpa [N, hd] using hNold r hr d e
    newN := by
      intro d e
      have hd : d.1 < a := d.2
      simpa [N, hd] using hNnew d e
    residualN := NA
    residual_eq := by intro r e; simp [N]
    residual_subset := by intro r e; simpa [J] using hNAsub r e
    A := by
      intro r d
      by_cases hd : d.1 < a
      · simpa [J, hd] using hJsub r ⟨d.1, hd⟩
      · simpa [J, hd] using hJAsub r
    B := by
      intro r d
      by_cases hd : d.1 < a
      · simpa [N, hd] using hNdis r ⟨d.1, hd⟩
      · simpa [N, hd] using hNAdis r
    C := by
      intro r d e
      by_cases hd : d.1 < a
      · simpa [J, N, hd] using hC r ⟨d.1, hd⟩ e
      · simpa [J, N, hd] using hNAinf r e
    I_infinite := hIinf
    oldI := hIold
    oldJ := by
      intro r hr d
      have hd : d.1 < a := d.2
      simpa [J, hd] using hJold r hr d
    E := hFullE
    F := by
      intro r d
      by_cases hd : d.1 < a
      · obtain ⟨mu, hb, hp, hn, hconv⟩ := hFJ r ⟨d.1, hd⟩
        refine ⟨mu, hb, hp, hn, ?_⟩
        intro sigma hmap hmass
        simpa [J, hd, along] using hconv sigma hmap
          (fun n => (hmass n).trans (Q.mass r d n).symm)
      · have he : d = lastCol a := Subtype.ext (le_antisymm d.2 (le_of_not_gt hd))
        subst d
        exact ⟨muA r, hmuA r, hmuApos r, hmuAneg r, fun sigma hmap hmass => by
          simpa [J, along] using hmuAF r sigma hmap
            (fun n => (hmass n).trans (Q.mass r _ n).symm)⟩
    G := by
      intro q s hmap hmass
      have hg := hG q s hmap (hmass.trans (Q.mass D.row (oldCol D.target) _).symm)
      exact ⟨fun hq => (hg.1 hq).2, hg.2⟩ }
  refine ⟨R, M, ?_, hMinf, hMsub, ?_, ?_⟩
  · change J D.row (oldCol D.source) = S
    have hd : D.source.1 < a := D.source.2
    simp [J, JO, hd]
  · obtain ⟨C, h0, h1⟩ := hWitness
    let C' : Clopens R.coordinates.carrier :=
      ⟨R.coordinates.equiv.symm ⁻¹' (C : Set (splitCarrier Y Z)),
        C.isClopen.preimage R.coordinates.equiv.symm.continuous⟩
    refine ⟨C', ?_, ?_⟩
    · intro n hn x hx
      apply h0 n hn (R.coordinates.equiv.symm x)
      apply Subtype.ext
      change restrict D.row.2.2 (R.coordinates.equiv.symm x).1.1.1 = (D.y n).1
      exact (R.coordinates.restrict_inverse D.row.1 D.row.2.2 x).symm.trans hx
    · intro n hn x hx
      apply h1 n hn (R.coordinates.equiv.symm x)
      apply Subtype.ext
      change restrict D.row.2.2 (R.coordinates.equiv.symm x).1.1.1 = (D.y n).1
      exact (R.coordinates.restrict_inverse D.row.1 D.row.2.2 x).symm.trans hx
  · intro q s hmap hmass
    apply R.quantitative_transport
      (fun value => (q % 2 = 0 → (13 : ℝ) / 48 < value) ∧ (q % 2 ≠ 0 → value = 0))
      q s hmap hmass
    intro sigma hm hn
    have hg := hG q sigma hm (hn.trans (Q.mass D.row (oldCol D.target) _).symm)
    exact ⟨fun hq => (hg.1 hq).1, hg.2⟩

/-- CH prepares Q once. Ordinary and locally eligible delayed treatments then
consume this same whole birth pack without selecting a second enumeration. -/
theorem exists_prepared_step (H : Prefix (Order.succ a)) (ha : ω ≤ a)
    (P : Predecessor H ha) (launch : Launch a) (hCH : Cardinal.continuum.{0} = ℵ₁) :
    ∃ Q : Prepared H ha P launch,
      (∀ t : Treatment a, Nonempty (Result H ha P launch Q t)) ∧
      (∀ D : DelayedTask Q,
        ∃ R : Result H ha P launch Q ⟨D.row, oldCol D.target⟩, DelayedCertificate Q D R) := by
  obtain ⟨Q⟩ := exists_prepared H ha P launch hCH
  exact ⟨Q, fun t => exists_ordinary H ha P launch Q t, exists_delayed_result Q⟩

end D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor
