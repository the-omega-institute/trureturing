/- GID: D5/S3/Topology/InverseLimit/TalagrandTopologicalConsequences
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/TalagrandTopologicalConsequences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: CH gives the literal Talagrand scheme and all signed and topological endpoints on one space. -/

import D5.S3.Topology.Measures.SignedBallReduction
import D5.S3.Topology.InverseLimit.SignedOrdinalRealization
import D5.S3.Topology.InverseLimit.SignedOrdinalReindexedLaws
import D5.S3.Topology.InverseLimit.SignedOrdinalActualG
import D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints
import D5.S3.Topology.InverseLimit.ContinuousFiniteImageTail
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Sequences

/-!
# Point-space consequences of signed dual-ball exclusion

Evaluation embeds a profinite space continuously into the weak-star closed
unit ball of its real continuous dual. Thus exclusion of continuous injections
of beta-N from that whole ball implies the same exclusion for the point space.
The final theorem constructs the literal Talagrand scheme under CH alone and
proves the signed dual-ball, Grothendieck and closed-copy endpoints on that same space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Function

namespace D5.S3.Topology.InverseLimit.TalagrandTopologicalConsequences

universe u

private def evaluation (K : Profinite.{u}) (x : K) : WeakDual ℝ C(K, ℝ) :=
  StrongDual.toWeakDual (ContinuousMap.evalCLM (R := ℝ) x)

private theorem continuous_evaluation (K : Profinite.{u}) :
    Continuous (evaluation K) := by
  apply WeakDual.continuous_of_continuous_eval
  intro g
  exact g.continuous

private theorem norm_evaluation_le_one (K : Profinite.{u}) (x : K) :
    ‖WeakDual.toStrongDual (evaluation K x)‖ ≤ 1 := by
  change ‖ContinuousMap.evalCLM (R := ℝ) x‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simpa only [ContinuousMap.evalCLM_apply, one_mul] using g.norm_coe_le_norm x

private theorem evaluation_injective (K : Profinite.{u}) :
    Injective (evaluation K) := by
  classical
  intro x y hxy
  by_contra hne
  obtain ⟨U, hU, hx, hy⟩ := exists_isClopen_of_totally_separated hne
  have hy' : y ∉ U := hy
  let g : C(K, ℝ) := ⟨U.indicator (fun _ => 1), hU.continuous_indicator continuous_const⟩
  have htest := congrArg (fun F : WeakDual ℝ C(K, ℝ) => F g) hxy
  change g x = g y at htest
  simpa [g, hx, hy'] using htest

private theorem point_space_no_beta_of_signed_ball (K : Profinite.{u})
    (Hball : ∀ h : StoneCech ℕ → WeakDual ℝ C(K, ℝ), Continuous h →
      (∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) → ¬ Injective h) :
    ∀ f : StoneCech ℕ → K, Continuous f → ¬ Injective f := by
  intro f hf hfi
  exact Hball (evaluation K ∘ f) ((continuous_evaluation K).comp hf)
    (fun p => norm_evaluation_le_one K (f p)) ((evaluation_injective K).comp hfi)

open Filter _root_.Topology _root_.TopologicalSpace

universe v

private theorem point_space_size_of_surjection_no_sequences (K : Profinite.{u})
    {X : Type v} [Infinite X] (f : K → X) (hf : Surjective f)
    (hseq : ∀ (x : ℕ → K) (p : K), Tendsto x atTop (𝓝 p) →
      ∀ᶠ n in atTop, x n = p) :
    Infinite K ∧ ¬ FirstCountableTopology K ∧ ¬ MetrizableSpace K := by
  letI : Infinite K := Infinite.of_surjective f hf
  have hnot : ¬ FirstCountableTopology K := by
    intro hfc
    letI : FirstCountableTopology K := hfc
    let e : ℕ ↪ K := Infinite.natEmbedding K
    obtain ⟨p, phi, hphi, hconv⟩ := CompactSpace.tendsto_subseq e
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq (e ∘ phi) p hconv)
    have heq : phi N = phi (N + 1) :=
      e.injective ((hN N le_rfl).trans (hN (N + 1) (Nat.le_succ N)).symm)
    exact (Nat.ne_of_lt (Nat.lt_succ_self N)) (hphi.injective heq)
  refine ⟨inferInstance, hnot, ?_⟩
  intro hm
  letI : MetrizableSpace K := hm
  exact hnot inferInstance

open scoped Cardinal Ordinal

private theorem actual_point_space_consequences
    (hCH : Cardinal.continuum.{0} = ℵ₁)
    (Hball : ∀ h : StoneCech ℕ →
      WeakDual ℝ C((SignedOrdinalRealization.finalPrefix hCH).cone.pt, ℝ),
      Continuous h → (∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) → ¬ Injective h)
    (hseq : ∀ (x : ℕ → (SignedOrdinalRealization.finalPrefix hCH).cone.pt)
      (p : (SignedOrdinalRealization.finalPrefix hCH).cone.pt),
      Tendsto x atTop (𝓝 p) → ∀ᶠ n in atTop, x n = p) :
    (∀ f : StoneCech ℕ → (SignedOrdinalRealization.finalPrefix hCH).cone.pt,
      Continuous f → ¬ Injective f) ∧
    Infinite (SignedOrdinalRealization.finalPrefix hCH).cone.pt ∧
    ¬ FirstCountableTopology (SignedOrdinalRealization.finalPrefix hCH).cone.pt ∧
    ¬ MetrizableSpace (SignedOrdinalRealization.finalPrefix hCH).cone.pt := by
  letI : Infinite (SignedProperLimit.Coord ω) :=
    Infinite.of_injective
      (fun n : ℕ => (⟨(n : Ordinal), Ordinal.natCast_lt_omega0 n⟩ :
        SignedProperLimit.Coord ω))
      (fun _ _ h => Nat.cast_injective (congrArg Subtype.val h))
  letI : Infinite (SignedProperLimit.Cube ω) := inferInstance
  refine ⟨point_space_no_beta_of_signed_ball _ Hball, ?_⟩
  exact point_space_size_of_surjection_no_sequences _
    (fun x => SignedProperLimit.restrict Ordinal.omega0_lt_omega_one.le x.1)
    (SignedOrdinalRealization.initial_onto hCH) hseq

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal ENNReal Topology
open SignedProperLimit SignedBirthEnumeration
open SignedOrdinalHistoryBirth SignedOrdinalHistoryState

private theorem actual_scheme
    (hCH : Cardinal.continuum.{0} = ℵ₁) :
    let H := SignedOrdinalRealization.finalPrefix hCH
    let K := H.LimitSpace
    let W := SignedOrdinalActualReindex.actualBirth hCH
    let ρ := SignedOrdinalActualReindex.eventRow hCH
    let η := SignedOrdinalActualReindex.eta hCH
    let Z := SignedOrdinalActualG.clopen hCH
    let k := SignedOrdinalActualG.column hCH
    -- The old stages and both kinds of maps are literal coordinate restrictions.
    ((∀ c : Label, IsClosed (H.carrier c) ∧ (H.carrier c).Nonempty) ∧
      (∀ (a b : Label) (hab : a ≤ b) (x : H.Space b),
        (H.map a b hab x).1 = restrict hab x.1) ∧
      (∀ (a b : Label) (hab : a ≤ b), Surjective (H.map a b hab)) ∧
      (∀ (a : Label) (x : K),
        (H.projection a x).1 = restrict (le_of_lt a.2) x.1)) ∧
    -- Every initial carrier, including omega, is the original complete cube.
    ((∀ (c : Label), c.1 ≤ ω → H.carrier c = univ) ∧
      Surjective (fun x : K => restrict
        (show (ω : Ordinal.{0}) ≤ ω₁ from Ordinal.omega0_lt_omega_one.le) x.1)) ∧
    -- The one actual final set, its topology, cone, and all onto projections.
    (IsClosed H.limitCarrier ∧ Nonempty K ∧ CompactSpace K ∧ T2Space K ∧
      ZeroDimensionalSpace K ∧
      Nonempty (CategoryTheory.Limits.IsLimit H.cone) ∧
      ∀ a : Label, Surjective (H.projection a)) ∧
    -- Complete whole enumerations; B and V stay those of the original run.
    (∀ θ : Stage, Surjective (W θ).U ∧ Surjective (W θ).B ∧
      Surjective (W θ).nu ∧
      (W θ).B = (SignedOrdinalRealization.wholeBirth hCH θ).B ∧
      (W θ).V = (SignedOrdinalRealization.wholeBirth hCH θ).V ∧
      ∀ (δ : Label) (n : ℕ),
        Measure.Regular ((W θ).measure δ n).toJordanDecomposition.posPart ∧
        Measure.Regular ((W θ).measure δ n).toJordanDecomposition.negPart ∧
        ((W θ).measure δ n).totalVariation univ = 1 ∧
        ((W θ).measure δ n).totalVariation ((W θ).V.clopen n : Set _)ᶜ = 0 ∧
        (1 / 2 : ℝ≥0∞) ≤ ((W θ).measure δ n).toJordanDecomposition.posPart univ) ∧
    -- Every proper cutoff retains the full original Laws, including every-choice
    -- signed F and its regular reference of totalVariation.real univ <= 1.
    -- Its nu reads THIS W, at every Label and every natural index.
    (∀ (l : Ordinal.{0}) (hl : l < ω₁),
      let P := SignedOrdinalRealization.properSlice hCH hl
      let D := SignedOrdinalReindexedLaws.properData hCH hl
      (∀ c : Coord l, P.carrier c = H.carrier ⟨c.1, c.2.trans hl⟩) ∧
      P.Laws D ∧
      ∀ (c : Coord l) (hc : ω ≤ c.1) (δ : Label) (n : ℕ),
        (D.nu c δ n).1 = (W ⟨⟨c.1, c.2.trans hl⟩, hc⟩).measure δ n) ∧
    -- The SAME eta is used for launch and all-signed-lift G on literal succ(a).
    -- Z and k are fixed before the arbitrary complete lift sequence is supplied.
    (∀ a : Stage, ∃ hra : ρ a ≤ a, η a ≤ a.1 ∧
      (∀ n : ℕ,
        ((W a).V.clopen n : Set (H.Space a.1)) =
          H.map (ρ a).1 a.1 hra ⁻¹'
            (((W (ρ a)).U (η a)).clopen n : Set _)) ∧
      StrictMono (k a) ∧
      ∀ (s : ℕ → SignedMeasure (H.Space (nextStage a).1))
        (hmap : ∀ n, (s n).map
          (H.map (ρ a).1 (nextStage a).1
            (hra.trans (Order.le_succ (ord a)))) =
          (W (ρ a)).measure (η a) n)
        (hmass : ∀ n, (s n).totalVariation univ = 1),
        (∀ q : ℕ,
          (q % 2 = 0 → (1 : ℝ) / 6 < s (k a q) (Z a)) ∧
          (q % 2 ≠ 0 → s (k a q) (Z a) = 0)) ∧
        ({n | (1 : ℝ) / 6 ≤ s n (Z a)}.Infinite ∧
          {n | s n (Z a) = 0}.Infinite)) ∧
    -- Every row and every NEW whole label is actually treated cofinally.
    (∀ (θ : Stage) (δ base : Label),
      ∃ a : Stage, base < a.1 ∧ θ < a ∧ ρ a = θ ∧ η a = δ) := by
  let H := SignedOrdinalRealization.finalPrefix hCH
  let K := H.LimitSpace
  let W := SignedOrdinalActualReindex.actualBirth hCH
  let ρ := SignedOrdinalActualReindex.eventRow hCH
  let η := SignedOrdinalActualReindex.eta hCH
  let Z := SignedOrdinalActualG.clopen hCH
  let k := SignedOrdinalActualG.column hCH
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro c
      exact ⟨H.closed c, H.nonempty c⟩
    · intro a b hab x
      rfl
    · intro a b hab y
      obtain ⟨x, hx⟩ := H.onto a b hab y
      exact ⟨x, Subtype.ext hx⟩
    · intro a x
      rfl
  · exact ⟨SignedOrdinalRealization.initial_carrier hCH,
      SignedOrdinalRealization.initial_onto hCH⟩
  · have hcompact : IsCompact H.limitCarrier :=
      isCompact_iff_compactSpace.mpr
        (inferInstance : CompactSpace H.LimitSpace)
    refine ⟨hcompact.isClosed, ?_, inferInstance, inferInstance, inferInstance,
      ⟨H.coneIsLimit (Cardinal.isSuccLimit_omega 1)⟩,
      H.projection_surjective (Cardinal.isSuccLimit_omega 1)⟩
    obtain ⟨x, hx⟩ := SignedOrdinalRealization.initial_onto hCH (fun _ => false)
    exact ⟨x⟩
  · intro θ
    refine ⟨(W θ).Uonto, (W θ).Bonto, (W θ).nuonto, rfl, rfl, ?_⟩
    intro δ n
    let b := (W θ).nu δ
    have hb := b.2 n
    exact ⟨(b.1 n).2.1, (b.1 n).2.2, hb.1, hb.2.1, hb.2.2⟩
  · intro l hl
    refine ⟨?_, SignedOrdinalReindexedLaws.properLaws hCH hl, ?_⟩
    · intro c
      rfl
    · intro c hc δ n
      exact SignedOrdinalReindexedLaws.nu_reindexBirth hCH hl c hc δ n
        (SignedOrdinalActualReindex.actualDelayedSupport hCH
          ⟨⟨c.1, c.2.trans hl⟩, hc⟩)
  · intro a
    refine ⟨SignedOrdinalActualReindex.eventRow_le hCH a,
      SignedOrdinalActualReindex.eta_le hCH a, ?_,
      SignedOrdinalActualG.column_strictMono hCH a, ?_⟩
    · intro n
      exact SignedOrdinalActualReindex.universal_launch hCH a n
    · intro s hmap hmass
      exact ⟨fun q => SignedOrdinalActualG.quantitative_g hCH a s hmap hmass q,
        SignedOrdinalActualG.infinite_values hCH a s hmap hmass⟩
  · exact SignedOrdinalActualReindex.actual_cofinal hCH


open SignedOrdinalSuccessor
open D5.S3.Topology.Measures.SignedSplitSuccessor (splitCarrier)

/-- Literal geometry required by the original scheme, on the same fixed run. -/
private theorem actual_geometric_limits
    (hCH : Cardinal.continuum.{0} = ℵ₁) :
    let H := SignedOrdinalRealization.finalPrefix hCH
    (∀ a : Stage,
      (SignedOrdinalActualG.clopen hCH a : Set (H.Space (nextStage a).1)) =
        {x | x.1 (SignedSuccessorCoordinates.last (ord a)) = true}) ∧
    (∀ (l : Label), ω < l.1 → Order.IsSuccLimit l.1 →
      H.carrier l = (SignedOrdinalRealization.properSlice hCH l.2).limitCarrier) ∧
    H.limitCarrier = {x | ∀ a : Label,
      restrict (le_of_lt a.2) x ∈ H.carrier a} := by
  let H := SignedOrdinalRealization.finalPrefix hCH
  refine ⟨?_, ?_, rfl⟩
  · intro a
    ext x
    rfl
  · intro l hw hl
    let a : Stage := ⟨l, hw.le⟩
    let R := SignedOrdinalHistoryLimit.result a
      (fun b _ => SignedOrdinalHistory.run hCH b)
      (fun b c _ _ hbc => SignedOrdinalHistory.coherent hCH b c hbc) hw hl
    calc
      H.carrier l = (SignedOrdinalHistory.run hCH a).H.carrier (top (ord a)) :=
        SignedOrdinalRealization.top_read hCH a
      _ = R.extended.carrier (top (ord a)) := by
        exact congrArg (fun S : SignedOrdinalHistoryState.State a =>
          S.H.carrier (top (ord a))) (SignedOrdinalHistory.limit_execution hCH a hw hl)
      _ = (SignedOrdinalHistoryPast.strictPrefix a.1.2.le
          (fun b _ => SignedOrdinalHistory.run hCH b)
          (fun b c _ _ hbc => SignedOrdinalHistory.coherent hCH b c hbc)).limitCarrier :=
        R.top_carrier
      _ = (SignedOrdinalRealization.properSlice hCH l.2).limitCarrier := rfl

/-- Every original successor is the literal Boolean insertion of its closed cover. -/
private theorem actual_successor_split
    (hCH : Cardinal.continuum.{0} = ℵ₁) :
    let H := SignedOrdinalRealization.finalPrefix hCH
    ∀ a : Stage, ∃ Y Z : Set (H.Space a.1),
      IsClosed Y ∧ IsClosed Z ∧ Y ∪ Z = univ ∧
      H.carrier (nextStage a).1 =
        Set.range (fun z : splitCarrier Y Z =>
          fun i : Coord (Order.succ (ord a)) =>
            if hi : i.1 < ord a then z.1.1.1 ⟨i.1, hi⟩ else z.1.2) := by
  classical
  dsimp only
  intro a
  let R := (SignedOrdinalHistory.run hCH a).event.result
  let E := Homeomorph.setCongr (SignedOrdinalRealization.top_read hCH a)
  let Y := E ⁻¹' R.Y
  let Z := E ⁻¹' R.Z
  refine ⟨Y, Z, R.closedY.preimage E.continuous,
    R.closedZ.preimage E.continuous, ?_, ?_⟩
  · change E ⁻¹' R.Y ∪ E ⁻¹' R.Z = univ
    rw [← Set.preimage_union, R.cover, Set.preimage_univ]
  · rw [SignedOrdinalRealization.successor_carrier hCH a]
    change R.coordinates.carrier = _
    rw [R.coordinates.range_eq]
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      let z' : splitCarrier Y Z := ⟨(E.symm z.1.1, z.1.2), by
        change ((E (E.symm z.1.1) ∈ R.Y ∧ z.1.2 = false) ∨
          (E (E.symm z.1.1) ∈ R.Z ∧ z.1.2 = true))
        have hz := z.2
        change ((z.1.1 ∈ R.Y ∧ z.1.2 = false) ∨
          (z.1.1 ∈ R.Z ∧ z.1.2 = true)) at hz
        have he : E (E.symm z.1.1) = z.1.1 := E.apply_symm_apply _
        exact he.symm ▸ hz⟩
      refine ⟨z', ?_⟩
      funext i
      exact (R.coordinates.insert z i).symm
    · rintro ⟨z, rfl⟩
      let z' : splitCarrier R.Y R.Z := ⟨(E z.1.1, z.1.2), by exact z.2⟩
      refine ⟨z', ?_⟩
      funext i
      exact R.coordinates.insert z' i

/-- Under CH, the literal constructed Talagrand scheme has the full original
signed and topological endpoints on one space, with no extra prediction axiom. -/
theorem actual_CH_Talagrand_scheme_and_endpoints
    (hCH : Cardinal.continuum.{0} = ℵ₁) :
    let H := SignedOrdinalRealization.finalPrefix hCH
    let K := H.LimitSpace
    let W := SignedOrdinalActualReindex.actualBirth hCH
    let ρ := SignedOrdinalActualReindex.eventRow hCH
    let η := SignedOrdinalActualReindex.eta hCH
    let Z := SignedOrdinalActualG.clopen hCH
    let k := SignedOrdinalActualG.column hCH
    (
    -- The old stages and both kinds of maps are literal coordinate restrictions.
    ((∀ c : Label, IsClosed (H.carrier c) ∧ (H.carrier c).Nonempty) ∧
      (∀ (a b : Label) (hab : a ≤ b) (x : H.Space b),
        (H.map a b hab x).1 = restrict hab x.1) ∧
      (∀ (a b : Label) (hab : a ≤ b), Surjective (H.map a b hab)) ∧
      (∀ (a : Label) (x : K),
        (H.projection a x).1 = restrict (le_of_lt a.2) x.1)) ∧
    -- Every initial carrier, including omega, is the original complete cube.
    ((∀ (c : Label), c.1 ≤ ω → H.carrier c = univ) ∧
      Surjective (fun x : K => restrict
        (show (ω : Ordinal.{0}) ≤ ω₁ from Ordinal.omega0_lt_omega_one.le) x.1)) ∧
    -- The one actual final set, its topology, cone, and all onto projections.
    (IsClosed H.limitCarrier ∧ Nonempty K ∧ CompactSpace K ∧ T2Space K ∧
      ZeroDimensionalSpace K ∧
      Nonempty (CategoryTheory.Limits.IsLimit H.cone) ∧
      ∀ a : Label, Surjective (H.projection a)) ∧
    -- Complete whole enumerations; B and V stay those of the original run.
    (∀ θ : Stage, Surjective (W θ).U ∧ Surjective (W θ).B ∧
      Surjective (W θ).nu ∧
      (W θ).B = (SignedOrdinalRealization.wholeBirth hCH θ).B ∧
      (W θ).V = (SignedOrdinalRealization.wholeBirth hCH θ).V ∧
      ∀ (δ : Label) (n : ℕ),
        Measure.Regular ((W θ).measure δ n).toJordanDecomposition.posPart ∧
        Measure.Regular ((W θ).measure δ n).toJordanDecomposition.negPart ∧
        ((W θ).measure δ n).totalVariation univ = 1 ∧
        ((W θ).measure δ n).totalVariation ((W θ).V.clopen n : Set _)ᶜ = 0 ∧
        (1 / 2 : ℝ≥0∞) ≤ ((W θ).measure δ n).toJordanDecomposition.posPart univ) ∧
    -- Every proper cutoff retains the full original Laws, including every-choice
    -- signed F and its regular reference of totalVariation.real univ <= 1.
    -- Its nu reads THIS W, at every Label and every natural index.
    (∀ (l : Ordinal.{0}) (hl : l < ω₁),
      let P := SignedOrdinalRealization.properSlice hCH hl
      let D := SignedOrdinalReindexedLaws.properData hCH hl
      (∀ c : Coord l, P.carrier c = H.carrier ⟨c.1, c.2.trans hl⟩) ∧
      P.Laws D ∧
      ∀ (c : Coord l) (hc : ω ≤ c.1) (δ : Label) (n : ℕ),
        (D.nu c δ n).1 = (W ⟨⟨c.1, c.2.trans hl⟩, hc⟩).measure δ n) ∧
    -- The SAME eta is used for launch and all-signed-lift G on literal succ(a).
    -- Z and k are fixed before the arbitrary complete lift sequence is supplied.
    (∀ a : Stage, ∃ hra : ρ a ≤ a, η a ≤ a.1 ∧
      (∀ n : ℕ,
        ((W a).V.clopen n : Set (H.Space a.1)) =
          H.map (ρ a).1 a.1 hra ⁻¹'
            (((W (ρ a)).U (η a)).clopen n : Set _)) ∧
      StrictMono (k a) ∧
      ∀ (s : ℕ → SignedMeasure (H.Space (nextStage a).1))
        (hmap : ∀ n, (s n).map
          (H.map (ρ a).1 (nextStage a).1
            (hra.trans (Order.le_succ (ord a)))) =
          (W (ρ a)).measure (η a) n)
        (hmass : ∀ n, (s n).totalVariation univ = 1),
        (∀ q : ℕ,
          (q % 2 = 0 → (1 : ℝ) / 6 < s (k a q) (Z a)) ∧
          (q % 2 ≠ 0 → s (k a q) (Z a) = 0)) ∧
        ({n | (1 : ℝ) / 6 ≤ s n (Z a)}.Infinite ∧
          {n | s n (Z a) = 0}.Infinite)) ∧
    -- Every row and every NEW whole label is actually treated cofinally.
    (∀ (θ : Stage) (δ base : Label),
      ∃ a : Stage, base < a.1 ∧ θ < a ∧ ρ a = θ ∧ η a = δ)
    ) ∧
    (∀ a : Label, CompactSpace (H.Space a) ∧ T2Space (H.Space a) ∧
      ZeroDimensionalSpace (H.Space a) ∧ MetrizableSpace (H.Space a)) ∧
    -- Literal geometric equations, including the successor closed-cover split.
    (∀ a : Stage, ∃ Y Z : Set (H.Space a.1),
      IsClosed Y ∧ IsClosed Z ∧ Y ∪ Z = univ ∧
      H.carrier (nextStage a).1 =
        Set.range (fun z : splitCarrier Y Z =>
          fun i : Coord (Order.succ (ord a)) =>
            if hi : i.1 < ord a then z.1.1.1 ⟨i.1, hi⟩ else z.1.2)) ∧
    (∀ a : Stage, (Z a : Set (H.Space (nextStage a).1)) =
      {x | x.1 (SignedSuccessorCoordinates.last (ord a)) = true}) ∧
    (∀ l : Label, ω < l.1 → Order.IsSuccLimit l.1 →
      H.carrier l = (SignedOrdinalRealization.properSlice hCH l.2).limitCarrier) ∧
    H.limitCarrier = {x | ∀ a : Label,
      restrict (le_of_lt a.2) x ∈ H.carrier a} ∧
    -- Full normalized regular signed oscillation on the very same final K.
    (∀ (t : ℕ → SignedMeasure K) (V : ℕ → Set K),
      (∀ n, (t n).totalVariation.Regular) →
      (∀ n, IsClopen (V n) ∧ (V n).Nonempty) →
      Pairwise (fun i n => Disjoint (V i) (V n)) →
      (∀ n, (t n).totalVariation.real univ = 1) →
      (∀ n, (1 / 2 : ℝ) ≤ (t n).toJordanDecomposition.posPart.real univ) →
      (∀ n, (t n).totalVariation (V n)ᶜ = 0) →
      ∃ B : Set K, IsClopen B ∧
        {n | (1 / 6 : ℝ) ≤ t n B}.Infinite ∧ {n | t n B = 0}.Infinite) ∧
    -- Theorem A, with the stronger finite-image and finite-copy conclusions.
    (∀ (A : Set K), IsClosed A → ∀ (f : A → K), Continuous f →
      Disjoint A (range f) → (range f).Finite) ∧
    (∀ (A B : Set K), IsClosed A → (A ≃ₜ B) → Disjoint A B →
      A.Finite ∧ B.Finite) ∧
    (∀ (T : ℕ → Set K), (∀ n, IsCompact (T n)) →
      (∀ n, (T n).Nonempty) →
      (∀ n, ∃ A B : Set K, A ⊆ T n ∧ B ⊆ T n ∧ Disjoint A B ∧
        Nonempty (T (n + 1) ≃ₜ A) ∧ Nonempty (T (n + 1) ≃ₜ B)) → False) ∧
    -- The whole real signed dual unit ball, arbitrary Grothendieck tests,
    -- and convergence to the actual point limit; no supplier hypotheses.
    (∀ h : StoneCech ℕ → WeakDual ℝ C(K, ℝ), Continuous h →
      (∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) → ¬ Injective h) ∧
    (∀ (F : ℕ → StrongDual ℝ C(K, ℝ)) (FInf : StrongDual ℝ C(K, ℝ)),
      (∀ g, Tendsto (fun n => F n g) atTop (𝓝 (FInf g))) →
      ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
        Tendsto (fun n => Φ (F n)) atTop (𝓝 (Φ FInf))) ∧
    (∀ (x : ℕ → K) (p : K), Tendsto x atTop (𝓝 p) →
      ∀ᶠ n in atTop, x n = p) ∧
    (∀ f : StoneCech ℕ → K, Continuous f → ¬ Injective f) ∧
    Infinite K ∧ ¬ FirstCountableTopology K ∧ ¬ MetrizableSpace K := by
  have hscheme := actual_scheme hCH
  have hstages : ∀ a : Label,
      CompactSpace ((SignedOrdinalRealization.finalPrefix hCH).Space a) ∧
      T2Space ((SignedOrdinalRealization.finalPrefix hCH).Space a) ∧
      ZeroDimensionalSpace ((SignedOrdinalRealization.finalPrefix hCH).Space a) ∧
      MetrizableSpace ((SignedOrdinalRealization.finalPrefix hCH).Space a) := by
    intro a
    letI : Countable (Coord a.1) :=
      (Cardinal.countable_Iio_of_lt_omega_one a.2).to_subtype
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hsplit := actual_successor_split hCH
  rcases actual_geometric_limits hCH with ⟨hcylinder, hlimit, hthreads⟩
  rcases SignedBallHistoryEndpoints.actual_signed_ball_history_endpoints hCH with
    ⟨hO, hball, hgroth, hseq⟩
  rcases ContinuousFiniteImageTail.actual_CH_finite_image_and_copy_obstructions hCH with
    ⟨hFI, hAH, hno2DCP⟩
  rcases actual_point_space_consequences hCH hball hseq with
    ⟨hpoint, hinfinite, hfirst, hmetric⟩
  exact ⟨hscheme, hstages, hsplit, hcylinder, hlimit, hthreads, hO, hFI, hAH, hno2DCP,
    hball, hgroth, hseq, hpoint, hinfinite, hfirst, hmetric⟩

end D5.S3.Topology.InverseLimit.TalagrandTopologicalConsequences
