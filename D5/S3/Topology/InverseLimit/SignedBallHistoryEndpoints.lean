/- GID: D5/S3/Topology/InverseLimit/SignedBallHistoryEndpoints
   generality: G
   mirror-B: none(waiver:private-internal-step)
   mirror-E: none(waiver:private-internal-step)
   anchors: []
   utility: none
   digest: Original whole-birth oscillation on actual generated successor carriers. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor
import D5.S3.Topology.InverseLimit.SignedOrdinalHistory
import D5.S3.Topology.InverseLimit.SignedOrdinalRealizationEvents
import D5.S3.Topology.Measures.SignedGrothendieckCriterion
import D5.S3.Topology.Measures.SignedBallReduction

/-! One actual selected successor transports the original whole birth sequence
and its quantitative clopen to the next state of the same constructed run. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology

namespace D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints

open SignedOrdinalSuccessor

/-- The even and odd columns of one literal successor give infinitely many
high and zero evaluations of every whole sequence of original norm-one lifts. -/
private theorem quantitative_g_infinite
    {a : Ordinal.{0}} {H : SignedProperLimit.Prefix (Order.succ a)}
    {ha : ω ≤ a} {P : Predecessor H ha} {launch : Launch a}
    {Q : Prepared H ha P launch} {t : Treatment a}
    (R : Result H ha P launch Q t)
    (s : ℕ → SignedMeasure R.coordinates.carrier)
    (hmap : ∀ n, (s n).map (R.literalProjection t.row) = Q.measure t.row t.label n)
    (hmass : ∀ n, (s n).totalVariation univ = 1) :
    {n | (1 : ℝ) / 6 ≤ s n R.quantitativeClopen}.Infinite ∧
      {n | s n R.quantitativeClopen = 0}.Infinite := by
  have heven : Injective (fun m : ℕ => (R.column (2 * m)).n) :=
    R.k_mono.injective.comp (fun i j hij => by omega)
  have hodd : Injective (fun m : ℕ => (R.column (2 * m + 1)).n) :=
    R.k_mono.injective.comp (fun i j hij => by omega)
  constructor
  · apply (Set.infinite_range_of_injective heven).mono
    rintro _ ⟨m, rfl⟩
    exact ((R.quantitative_g (2 * m) (s _) (hmap _) (hmass _)).1 (by omega)).le
  · apply (Set.infinite_range_of_injective hodd).mono
    rintro _ ⟨m, rfl⟩
    exact (R.quantitative_g (2 * m + 1) (s _) (hmap _) (hmass _)).2 (by omega)

open SignedProperLimit SignedOrdinalHistoryState SignedOrdinalHistoryEvent
open SignedOrdinalHistorySuccessor SignedOrdinalHistory
open SignedBirthEnumeration
open SignedOrdinalRealization SignedOrdinalRawHistory SignedOrdinalRealizationEvents
open SignedBallHistoryCapture
open D5.S3.Topology.Measures

set_option backward.isDefEq.respectTransparency false in
/-- An actual ordinary event supplies one clopen on its actual next run carrier.
Its literal old-row projection reads the whole original birth sequence, for
every original label and every norm-one signed lift on that generated carrier. -/
private theorem original_birth_oscillation
    (hCH : Cardinal.continuum.{0} = ℵ₁) (θ : Stage) (d base : Label) :
    ∃ (a : Stage) (hθ : θ < a), base < a.1 ∧ d.1 < ord a ∧
      ∃ (t : Treatment (ord a))
        (R : Result (run hCH a).H a.2 (run hCH a).P
          (scheduledLaunch (run hCH a).H a.2 (run hCH a).P)
          (run hCH a).event.Q t),
        (run hCH a).event.selected = .ordinary t R ∧
        t.row.1 = ord θ ∧ t.label.1 = d.1 ∧
        (SignedOrdinalRealization.finalPrefix hCH).carrier (nextStage a).1 =
          R.coordinates.carrier ∧
        (∀ n, HEq ((run hCH a).event.Q.measure t.row t.label n)
          ((SignedOrdinalRealization.wholeBirth hCH θ).measure d n)) ∧
        ∃ G : Clopens (K (run hCH (nextStage a)).H),
          ∀ s : ℕ → SignedMeasure (K (run hCH (nextStage a)).H),
            (∀ n, HEq ((s n).map (projection (run hCH (nextStage a)).H
              (oldRow (hθ.trans (show a < nextStage a from Order.lt_succ (ord a)))
                (newRow (ord θ) θ.2)))) ((run hCH θ).birth.measure d n)) →
            (∀ n, (s n).totalVariation univ = 1) →
            {n | (1 : ℝ) / 6 ≤ s n G}.Infinite ∧ {n | s n G = 0}.Infinite := by
  classical
  obtain ⟨a, hb, hθ, hd, _, t, R, hselected, htrow, hlabel, hwhole⟩ :=
    SignedOrdinalHistory.ordinary_cofinal hCH θ d base
  rcases t with ⟨r, label⟩
  have hr : r = oldRow hθ (newRow (ord θ) θ.2) := Subtype.ext htrow
  subst r
  let r₀ := oldRow hθ (newRow (ord θ) θ.2)
  let r₁ := oldRow
    (hθ.trans (show a < nextStage a from Order.lt_succ (ord a))) (newRow (ord θ) θ.2)
  have hnext : (run hCH (nextStage a)).H = R.coordinates.extended := by
    calc
      _ = (run hCH a).event.result.coordinates.extended :=
        congrArg State.H (successor_execution hCH a)
      _ = R.coordinates.extended :=
        congrArg (fun S : Selected (run hCH a).event.Q => S.result.coordinates.extended) hselected
  have hcarrier :
      (SignedOrdinalRealization.finalPrefix hCH).carrier (nextStage a).1 =
        R.coordinates.carrier := by
    have hc := successor_carrier hCH a
    change (SignedOrdinalRealization.finalPrefix hCH).carrier (nextStage a).1 =
      (Selected.result (run hCH a).event.selected).coordinates.carrier at hc
    rw [hselected] at hc
    exact hc
  have hwhole' : ∀ n, HEq ((run hCH a).event.Q.measure
      (oldRow hθ (newRow (ord θ) θ.2)) label n)
      ((SignedOrdinalRealization.wholeBirth hCH θ).measure d n) := by
    intro n
    exact (hwhole n).trans (SignedOrdinalRealization.whole_measure hCH θ d n).symm
  refine ⟨a, hθ, hb, hd,
    ⟨oldRow hθ (newRow (ord θ) θ.2), label⟩, R, hselected, htrow, hlabel,
    hcarrier, hwhole', ?_⟩
  rw [hnext]
  change ∃ G : Clopens (K R.coordinates.extended),
    ∀ s : ℕ → SignedMeasure (K R.coordinates.extended),
      (∀ n, HEq ((s n).map
        (projection R.coordinates.extended r₁))
        ((run hCH θ).birth.measure d n)) →
      (∀ n, (s n).totalVariation univ = 1) →
      {n | (1 : ℝ) / 6 ≤ s n G}.Infinite ∧ {n | s n G = 0}.Infinite
  let E : K R.coordinates.extended ≃ₜ R.coordinates.carrier :=
    Homeomorph.setCongr R.coordinates.top_carrier
  let B : Base R.coordinates.extended r₁ ≃ₜ Base (run hCH a).H r₀ :=
    Homeomorph.setCongr (R.coordinates.old_carrier (rowIndex r₀))
  let G : Clopens (K R.coordinates.extended) :=
    ⟨E ⁻¹' (R.quantitativeClopen : Set _), R.quantitativeClopen.isClopen.preimage E.continuous⟩
  refine ⟨G, ?_⟩
  intro s hs hn
  let sigma : ℕ → SignedMeasure R.coordinates.carrier := fun n => (s n).map E
  have hp (x : K R.coordinates.extended) :
      R.literalProjection r₀ (E x) = B (projection R.coordinates.extended r₁ x) := by
    apply Subtype.ext
    exact (R.coordinates.restrict_inverse r₀.1 r₀.2.2 (E x)).symm
  have hm (n : ℕ) :
      (sigma n).map (R.literalProjection r₀) = (run hCH a).event.Q.measure r₀ label n := by
    have he : (sigma n).map (R.literalProjection r₀) =
        (s n).map (fun x => B (projection R.coordinates.extended r₁ x)) := by
      apply VectorMeasure.ext
      intro A hA
      calc
        (sigma n).map (R.literalProjection r₀) A =
            sigma n (R.literalProjection r₀ ⁻¹' A) :=
          VectorMeasure.map_apply _ (R.literalProjection r₀).continuous.measurable hA
        _ = s n (E ⁻¹' (R.literalProjection r₀ ⁻¹' A)) :=
          VectorMeasure.map_apply _ E.continuous.measurable
            ((R.literalProjection r₀).continuous.measurable hA)
        _ = s n ((fun x : K R.coordinates.extended =>
            B (projection R.coordinates.extended r₁ x)) ⁻¹' A) := by
          congr 1
          ext x
          exact Iff.of_eq (congrArg (fun y : Base (run hCH a).H r₀ => y ∈ A) (hp x))
        _ = (s n).map (fun x => B (projection R.coordinates.extended r₁ x)) A :=
          (VectorMeasure.map_apply (s n)
            (B.continuous.measurable.comp
              (projection R.coordinates.extended r₁).continuous.measurable) hA).symm
    have hcast : ∀ {C D : Set (Cube (ord θ))} (h : C = D)
        (p : K R.coordinates.extended → C),
        letI : MeasurableSpace C := borel C
        letI : MeasurableSpace D := borel D
        HEq ((s n).map (fun x => Homeomorph.setCongr h (p x))) ((s n).map p) := by
      intro C D h p
      subst D
      rfl
    exact eq_of_heq ((heq_of_eq he).trans
      ((hcast (R.coordinates.old_carrier (rowIndex r₀))
        (projection R.coordinates.extended r₁)).trans ((hs n).trans (hwhole n).symm)))
  have hnorm (n : ℕ) : (sigma n).totalVariation univ = 1 := by
    have hv : ((s n).map E).variation = (s n).variation.map E :=
      E.toMeasurableEquiv.measurableEmbedding.variation_map
    change SignedMeasure.totalVariation ((s n).map E) univ = 1
    rw [SignedMeasure.totalVariation_eq_variation, hv,
      Measure.map_apply E.continuous.measurable MeasurableSet.univ, preimage_univ,
      ← SignedMeasure.totalVariation_eq_variation, hn n]
  have heval (n : ℕ) : sigma n R.quantitativeClopen = s n G :=
    VectorMeasure.map_apply _ E.continuous.measurable R.quantitativeClopen.isClopen.1.measurableSet
  simpa only [heval] using quantitative_g_infinite R sigma hm hnorm

/-! The actual final cone supplies the original signed oscillation and all three
analytic endpoint consequences on the same limit carrier. -/

theorem actual_signed_ball_history_endpoints
    (hCH : Cardinal.continuum.{0} = ℵ₁) :
    (∀ (t : ℕ → SignedMeasure ((SignedOrdinalRealization.finalPrefix hCH).LimitSpace))
      (W : ℕ → Set ((SignedOrdinalRealization.finalPrefix hCH).LimitSpace)),
      (∀ n, (t n).totalVariation.Regular) →
      (∀ n, IsClopen (W n) ∧ (W n).Nonempty) →
      Pairwise (fun i n => Disjoint (W i) (W n)) →
      (∀ n, (t n).totalVariation.real univ = 1) →
      (∀ n, (1 / 2 : ℝ) ≤
        (t n).toJordanDecomposition.posPart.real univ) →
      (∀ n, (t n).totalVariation (W n)ᶜ = 0) →
      ∃ Z : Set ((SignedOrdinalRealization.finalPrefix hCH).LimitSpace),
        IsClopen Z ∧
          {n | (1 / 6 : ℝ) ≤ t n Z}.Infinite ∧
          {n | t n Z = 0}.Infinite) ∧
    (∀ h : StoneCech ℕ →
        WeakDual ℝ C((SignedOrdinalRealization.finalPrefix hCH).LimitSpace, ℝ),
      Continuous h →
      (∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) → ¬ Injective h) ∧
    (∀ (F : ℕ → StrongDual ℝ
        C((SignedOrdinalRealization.finalPrefix hCH).LimitSpace, ℝ))
      (FInf : StrongDual ℝ
        C((SignedOrdinalRealization.finalPrefix hCH).LimitSpace, ℝ)),
      (∀ g, Tendsto (fun n => F n g) atTop (𝓝 (FInf g))) →
      ∀ Φ : StrongDual ℝ (StrongDual ℝ
        C((SignedOrdinalRealization.finalPrefix hCH).LimitSpace, ℝ)),
        Tendsto (fun n => Φ (F n)) atTop (𝓝 (Φ FInf))) ∧
    (∀ (x : ℕ → (SignedOrdinalRealization.finalPrefix hCH).LimitSpace)
      (p : (SignedOrdinalRealization.finalPrefix hCH).LimitSpace),
      Tendsto x atTop (𝓝 p) → ∀ᶠ n in atTop, x n = p) := by
  classical
  let F := (SignedOrdinalRealization.finalPrefix hCH).diagram
  let C := (SignedOrdinalRealization.finalPrefix hCH).cone
  letI : MeasurableSpace C.pt := borel C.pt
  letI : BorelSpace C.pt := ⟨rfl⟩
  letI : ∀ j, Nonempty (F.obj j) := fun j => by
    change Nonempty ((SignedOrdinalRealization.finalPrefix hCH).Space j.unop)
    infer_instance
  letI : ∀ j, MeasurableSpace (F.obj j) := fun j =>
    borel ((F.obj j).toTop)
  letI : ∀ j, BorelSpace (F.obj j) := fun j => ⟨rfl⟩
  have hC : IsLimit C :=
    (SignedOrdinalRealization.finalPrefix hCH).coneIsLimit (Cardinal.isSuccLimit_omega 1)
  have hs : ∀ {i j} (a : i ⟶ j), Surjective (F.map a) := by
    intro i j a y
    obtain ⟨x, hx⟩ := (SignedOrdinalRealization.finalPrefix hCH).onto
      j.unop i.unop (leOfHom a.unop) y
    exact ⟨x, Subtype.ext hx⟩
  let H : RawHistory F := SignedOrdinalRawHistory.rawHistory hCH
  have hO :
      ∀ (t : ℕ → SignedMeasure C.pt) (W : ℕ → Set C.pt),
        (∀ n, (t n).totalVariation.Regular) →
        (∀ n, IsClopen (W n) ∧ (W n).Nonempty) →
        Pairwise (fun i n => Disjoint (W i) (W n)) →
        (∀ n, (t n).totalVariation.real univ = 1) →
        (∀ n, (1 / 2 : ℝ) ≤
          (t n).toJordanDecomposition.posPart.real univ) →
        (∀ n, (t n).totalVariation (W n)ᶜ = 0) →
        ∃ Z : Set C.pt, IsClopen Z ∧
          {n | (1 / 6 : ℝ) ≤ t n Z}.Infinite ∧
          {n | t n Z = 0}.Infinite := by
    intro t W htreg hW hdis hmass hhalf hcarry
    letI : ∀ n, (t n).totalVariation.Regular := htreg
    obtain ⟨b, hb, V, hV, hWV, hne, hdisV, hpres, _⟩ :=
      CountableSignedMeasureReflection.exists_common_stage F C hC hs birthBase t W
        (fun n => (hW n).1)
    let row : BirthStage := ⟨b, hb⟩
    let family : SupportFamily (F.obj (op b)) :=
      { clopen := fun n => ⟨V n, hV n⟩
        nonempty := fun n => (hne n).mpr (hW n).2
        disjoint := fun n m hnm => (hdisV n m).mpr (hdis hnm) }
    have hnorm (n : ℕ) : (t n).totalVariation univ = 1 :=
      (ENNReal.toReal_eq_one_iff _).mp (by simpa only [Measure.real] using hmass n)
    have hbmass (n : ℕ) :
        (SignedMeasure.totalVariation ((t n).map
          (C.π.app (op row.1)).hom.hom)) univ = 1 := by
      have h := ((hpres b le_rfl n).1).1
      change (SignedMeasure.totalVariation ((t n).map
          (C.π.app (op row.1)).hom.hom)) univ = (t n).totalVariation univ at h
      exact h.trans (hnorm n)
    have hsup (n : ℕ) :
        (t n).totalVariation ((C.π.app (op row.1)).hom.hom ⁻¹'
          family.clopen n)ᶜ = 0 := by
      have h := hWV n
      change W n = (C.π.app (op row.1)).hom.hom ⁻¹' family.clopen n at h
      rw [← h]
      exact hcarry n
    obtain ⟨θ, _, d, hbirth, hsupθ⟩ :=
      SignedBallHistoryCapture.exists_original_birth F C H t htreg hnorm hhalf
        row family hsup hbmass
    obtain ⟨a, hθ, hbase, hd, tr, R, hselected, htrow, htlabel, hcarrier,
        hQ, ⟨G, hG⟩⟩ :=
      original_birth_oscillation hCH θ d ⟨b.1, b.2⟩
    let c : Eligible θ d :=
      ⟨(nextStage a).1, max_lt
        (show θ.1 < (nextStage a).1 from hθ.trans
          (show a < nextStage a from Order.lt_succ (ord a)))
        (show d.1 < (nextStage a).1 from hd.trans
          (show a < nextStage a from Order.lt_succ (ord a)))⟩
    have hproj : (C.π.app (op c.1)).hom.hom =
        (SignedOrdinalRealization.finalPrefix hCH).projection c.1 := by
      rfl
    obtain ⟨hregc, hnormc, hmapc, hsupc⟩ :=
      SignedBallHistoryCapture.projected_lift F C H t htreg hnorm θ d hbirth hsupθ c
    have hnext : (SignedOrdinalHistory.run hCH (nextStage a)).H = R.coordinates.extended := by
      calc
        _ = (SignedOrdinalHistory.run hCH a).event.result.coordinates.extended :=
          congrArg State.H (successor_execution hCH a)
        _ = R.coordinates.extended :=
          congrArg (fun S : Selected (SignedOrdinalHistory.run hCH a).event.Q =>
            S.result.coordinates.extended) hselected
    have htop :
        (SignedOrdinalHistory.run hCH (nextStage a)).H.carrier
            (top (ord (nextStage a))) = R.coordinates.carrier := by
      rw [hnext]
      exact R.coordinates.top_carrier
    have hcarrier' :
        (SignedOrdinalRealization.finalPrefix hCH).Space c.1 = R.coordinates.carrier := by
      simpa [c] using hcarrier
    let T : (SignedOrdinalRealization.finalPrefix hCH).Space c.1 ≃ₜ
        K (SignedOrdinalHistory.run hCH (nextStage a)).H :=
      (Homeomorph.setCongr hcarrier').trans (Homeomorph.setCongr htop).symm
    let u : ℕ → SignedMeasure ((SignedOrdinalRealization.finalPrefix hCH).Space c.1) :=
      fun n => (t n).map ((SignedOrdinalRealization.finalPrefix hCH).projection c.1)
    let s' : ℕ → SignedMeasure (K (SignedOrdinalHistory.run hCH (nextStage a)).H) :=
      fun n => (u n).map T
    have hnorm' (n : ℕ) : (s' n).totalVariation univ = 1 := by
      have hv : ((u n).map T).variation = (u n).variation.map T :=
        T.toMeasurableEquiv.measurableEmbedding.variation_map
      change SignedMeasure.totalVariation ((u n).map T) univ = 1
      rw [SignedMeasure.totalVariation_eq_variation,
        hv,
        Measure.map_apply T.continuous.measurable MeasurableSet.univ, preimage_univ,
        ← SignedMeasure.totalVariation_eq_variation]
      have hc := hnormc n
      change (SignedMeasure.totalVariation
        ((t n).map (C.π.app (op c.1)).hom.hom)) univ = 1 at hc
      rw [hproj] at hc
      change (SignedMeasure.totalVariation
        ((t n).map ((SignedOrdinalRealization.finalPrefix hCH).projection c.1))) univ = 1
      exact hc
    have hbirth' : ∀ n, HEq ((s' n).map
        (projection (SignedOrdinalHistory.run hCH (nextStage a)).H
          (oldRow (hθ.trans (show a < nextStage a from Order.lt_succ (ord a)))
            (newRow (ord θ) θ.2))))
        ((SignedOrdinalHistory.run hCH θ).birth.measure d n) := by
      intro n
      have hθc : θ.1 ≤ c.1 :=
        (le_max_left θ.1 d).trans c.2.le
      have hmapc' :
          ((t n).map ((SignedOrdinalRealization.finalPrefix hCH).projection c.1)).map
            ((F.map (homOfLE hθc).op).hom.hom) = ((H.nu θ d).1 n).1 := by
        have hc := hmapc n
        change ((t n).map (C.π.app (op c.1)).hom.hom).map
            ((F.map (homOfLE hθc).op).hom.hom) = ((H.nu θ d).1 n).1 at hc
        rw [hproj] at hc
        exact hc
      have htarget :
          HEq ((s' n).map
            (projection (SignedOrdinalHistory.run hCH (nextStage a)).H
              (oldRow (hθ.trans (show a < nextStage a from Order.lt_succ (ord a)))
                (newRow (ord θ) θ.2))))
            (((t n).map ((SignedOrdinalRealization.finalPrefix hCH).projection c.1)).map
              ((F.map (homOfLE hθc).op).hom.hom)) := by
        let r₁ := oldRow (hθ.trans (show a < nextStage a from Order.lt_succ (ord a)))
          (newRow (ord θ) θ.2)
        have hread := SignedOrdinalRealization.carrier_read hCH (nextStage a)
          (rowIndex r₁)
        have hset :
            (SignedOrdinalRealization.finalPrefix hCH).Space θ.1 =
              (SignedOrdinalHistory.run hCH (nextStage a)).H.carrier (rowIndex r₁) := by
          simpa [r₁, oldRow, SignedOrdinalSuccessor.rowIndex,
            SignedOrdinalSuccessor.index] using hread
        have htype :
            (SignedOrdinalRealization.finalPrefix hCH).Space θ.1 =
              SignedOrdinalSuccessor.Base (SignedOrdinalHistory.run hCH (nextStage a)).H r₁ :=
          congrArg (fun S : Set (Cube (ord θ)) => {x // x ∈ S}) hset
        have htypeF :
            (F.obj (op θ.1)).toTop =
              SignedOrdinalSuccessor.Base (SignedOrdinalHistory.run hCH (nextStage a)).H r₁ := by
          simpa [F, SignedProperLimit.Prefix.diagram] using htype
        let PType := Σ X : Type _, MeasurableSpace X
        let pA : PType := ⟨SignedOrdinalSuccessor.Base
          (SignedOrdinalHistory.run hCH (nextStage a)).H r₁, borel _⟩
        let pB : PType := ⟨(F.obj (op θ.1)).toTop, borel _⟩
        have borel_subtype_heq {S T : Set (Cube (ord θ))} (hST : S = T) :
            HEq (borel {x // x ∈ S}) (borel {x // x ∈ T}) := by
          cases hST
          rfl
        have hmeas0 : HEq
            (borel ((SignedOrdinalRealization.finalPrefix hCH).Space θ.1))
            (borel (SignedOrdinalSuccessor.Base
              (SignedOrdinalHistory.run hCH (nextStage a)).H r₁)) := by
          change HEq
            (borel {x // x ∈ (SignedOrdinalRealization.finalPrefix hCH).carrier θ.1})
            (borel {x // x ∈
              (SignedOrdinalHistory.run hCH (nextStage a)).H.carrier (rowIndex r₁)})
          exact borel_subtype_heq hset
        have hp : pB = pA := by
          apply Sigma.ext htypeF
          dsimp [pA, pB]
          change HEq (borel ((F.obj (op θ.1)).toTop))
            (borel (SignedOrdinalSuccessor.Base
              (SignedOrdinalHistory.run hCH (nextStage a)).H r₁))
          change HEq
            (borel ((SignedOrdinalRealization.finalPrefix hCH).Space θ.1))
            (borel (SignedOrdinalSuccessor.Base
              (SignedOrdinalHistory.run hCH (nextStage a)).H r₁))
          exact hmeas0
        let fA : (SignedOrdinalRealization.finalPrefix hCH).Space c.1 → pA.1 :=
          fun x => projection (SignedOrdinalHistory.run hCH (nextStage a)).H r₁ (T x)
        let fB : (SignedOrdinalRealization.finalPrefix hCH).Space c.1 → pB.1 :=
          fun x => (F.map (homOfLE hθc).op).hom.hom x
        have hpoint (x : (SignedOrdinalRealization.finalPrefix hCH).Space c.1) :
            HEq (fA x) (fB x) := by
          have hpred : ∀ y, y ∈
              (SignedOrdinalHistory.run hCH (nextStage a)).H.carrier (rowIndex r₁) ↔ y ∈
                (SignedOrdinalRealization.finalPrefix hCH).Space θ.1 := by
            intro y
            rw [hset]
            exact Iff.rfl
          exact (Subtype.heq_iff_coe_eq hpred).2 (by rfl)
        have hfun : HEq fA fB := by
          exact Function.hfunext rfl (fun x y hxy => by
            have hxy' : x = y := eq_of_heq hxy
            subst y
            exact hpoint x)
        have hpack :
            (⟨pA, fA⟩ : Σ p : PType, (SignedOrdinalRealization.finalPrefix hCH).Space c.1 → p.1) =
              ⟨pB, fB⟩ := by
          apply Sigma.ext hp.symm
          exact hfun
        let mapAt {X : Type _} [MeasurableSpace X] (μ : SignedMeasure X)
            (p : PType) (f : X → p.1) :=
          letI : MeasurableSpace p.1 := p.2
          μ.map f
        have map_pack_heq : ∀ (p q : PType)
            (f : (SignedOrdinalRealization.finalPrefix hCH).Space c.1 → p.1)
            (g : (SignedOrdinalRealization.finalPrefix hCH).Space c.1 → q.1),
            (⟨p, f⟩ : Σ r : PType,
              (SignedOrdinalRealization.finalPrefix hCH).Space c.1 → r.1) = ⟨q, g⟩ →
            HEq (mapAt (u n) p f) (mapAt (u n) q g) := by
          intro p q f g h
          cases h
          rfl
        have hmap : HEq (mapAt (u n) pA fA) (mapAt (u n) pB fB) := by
          exact map_pack_heq pA pB fA fB hpack
        have hcomp :
            ((s' n).map (projection (SignedOrdinalHistory.run hCH (nextStage a)).H r₁)) =
              (u n).map (fun x => projection
                (SignedOrdinalHistory.run hCH (nextStage a)).H r₁ (T x)) := by
          apply VectorMeasure.ext
          intro V hV
          change ((u n).map T).map
              (projection (SignedOrdinalHistory.run hCH (nextStage a)).H r₁) V =
            (u n).map (fun x => projection
              (SignedOrdinalHistory.run hCH (nextStage a)).H r₁ (T x)) V
          rw [VectorMeasure.map_apply _
            (projection (SignedOrdinalHistory.run hCH (nextStage a)).H r₁).continuous.measurable hV,
            VectorMeasure.map_apply _ T.continuous.measurable
              (hV.preimage (projection
                (SignedOrdinalHistory.run hCH (nextStage a)).H r₁).continuous.measurable),
            VectorMeasure.map_apply _ (by
              exact (projection (SignedOrdinalHistory.run hCH (nextStage a)).H r₁).continuous.measurable.comp
                T.continuous.measurable) hV]
          congr 1
        have hleft :
            (s' n).map (projection (SignedOrdinalHistory.run hCH (nextStage a)).H r₁) =
              mapAt (u n) pA fA := by
          simpa [mapAt, pA, fA] using hcomp
        have hright :
            mapAt (u n) pB fB =
              ((t n).map ((SignedOrdinalRealization.finalPrefix hCH).projection c.1)).map
                ((F.map (homOfLE hθc).op).hom.hom) := by
          rfl
        exact (heq_of_eq hleft).trans (hmap.trans (heq_of_eq hright))
      have hnu : HEq ((H.nu θ d).1 n).1
          ((SignedOrdinalRealization.wholeBirth hCH θ).measure d n) := by
        rfl
      exact (htarget.trans (heq_of_eq hmapc')).trans
        (hnu.trans (SignedOrdinalRealization.whole_measure hCH θ d n))
    obtain ⟨hhigh, hzero⟩ := hG s' hbirth' hnorm'
    let Z : Set C.pt :=
      (SignedOrdinalRealization.finalPrefix hCH).projection c.1 ⁻¹'
        (T ⁻¹' (G : Set _))
    have hZ : IsClopen Z := by
      exact G.isClopen.preimage T.continuous |>.preimage
        ((SignedOrdinalRealization.finalPrefix hCH).projection c.1).continuous
    have heval (n : ℕ) : t n Z = (s' n) G := by
      dsimp [Z, s', u]
      calc
        (t n) ((SignedOrdinalRealization.finalPrefix hCH).projection c.1 ⁻¹'
            T ⁻¹' (G : Set _)) =
            ((t n).map ((SignedOrdinalRealization.finalPrefix hCH).projection c.1))
              (T ⁻¹' (G : Set _)) :=
          (VectorMeasure.map_apply _
            ((SignedOrdinalRealization.finalPrefix hCH).projection c.1).continuous.measurable
            (G.isClopen.preimage T.continuous).1.measurableSet).symm
        _ = (((t n).map ((SignedOrdinalRealization.finalPrefix hCH).projection c.1)).map T) G :=
          (VectorMeasure.map_apply _ T.continuous.measurable G.isClopen.1.measurableSet).symm
    refine ⟨Z, hZ, ?_, ?_⟩
    · have hs : {n | (1 / 6 : ℝ) ≤ t n Z} = {n | (1 / 6 : ℝ) ≤ s' n G} := by
        ext n
        simpa only [Set.mem_setOf_eq, heval n]
      exact hs.symm ▸ hhigh
    · have hs : {n | t n Z = 0} = {n | s' n G = 0} := by
        ext n
        simpa only [Set.mem_setOf_eq, heval n]
      exact hs.symm ▸ hzero
  have hcollision : SignedBallReduction.SignedClopenCollision (K := C.pt) :=
    SignedBallHistoryCapture.signed_clopen_collision F C hC hs H
  have hnon :
      ∀ h : StoneCech ℕ → WeakDual ℝ C(C.pt, ℝ), Continuous h →
        (∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) → ¬ Injective h := by
    intro h hh hbnd
    exact SignedBallReduction.not_injective_signed_ball_of_collision
      hcollision h hh hbnd
  refine ⟨hO, hnon, ?_, ?_⟩
  · intro G GInf hGconv
    exact SignedGrothendieckCriterion.weak_of_signed_clopen_oscillation
      (O := hO) G GInf hGconv
  · intro x p hlim
    exact SignedGrothendieckCriterion.eventually_eq_of_signed_clopen_oscillation
      (O := hO) x p hlim

end D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints
