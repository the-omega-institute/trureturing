/- Transient source/statement/axiom evidence for W0/W2. -/
import D5.S3.Topology.Measures.AtlasFiniteSignedCheck
import D5.S3.ObserverMemory.ProObjects.CompactObservationFactorization
import D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability
import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

/-! Exact task applications; all declarations in this module are transient evidence. -/
set_option pp.universes true
noncomputable section
open Classical
open MeasureTheory Set TopologicalSpace
open scoped BigOperators
open D5.S3.ObserverMemory.ProObjects.CompactObservationFactorization
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange
open D5.S3.Topology.Measures.FiniteObservationVariation
open D5.S3.Topology.Measures.NormPreservingLifts
open D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.TotalVariation.Pinsker
open AtlasFiniteSignedCheck
namespace AtlasObservationCheck

-- This map statement is about actual laws and actual signed differences.
theorem probability_difference_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : ProbabilityMeasure X) (f : X → Y) (hf : Measurable f) :
    ((μ : Measure X).toSignedMeasure - (ν : Measure X).toSignedMeasure).map f =
      (μ.map f : Measure Y).toSignedMeasure - (ν.map f : Measure Y).toSignedMeasure := by
  apply VectorMeasure.ext
  intro A hA
  rw [VectorMeasure.map_apply _ hf hA]
  simp only [sub_apply, Measure.toSignedMeasure_apply_measurable (hf hA),
    Measure.toSignedMeasure_apply_measurable hA, ProbabilityMeasure.toMeasure_map,
    map_measureReal_apply hf hA]

theorem probability_variation {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ ν : ProbabilityMeasure X) :
    ((μ : Measure X).toSignedMeasure - (ν : Measure X).toSignedMeasure).totalVariation.real univ =
      2 * totalVariation (massVector μ) (massVector ν) := by
  rw [full_variation]
  simp only [sub_apply, Measure.toSignedMeasure_apply_measurable (measurableSet_singleton _),
    totalVariation, massVector]
  ring

section W0
variable {K I A : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [ZeroDimensionalSpace K] [MeasurableSpace K] [BorelSpace K]
variable {O : I → Type*} [∀ i, TopologicalSpace (O i)] [∀ i, DiscreteTopology (O i)]
  [∀ i, Fintype (O i)] [∀ i, MeasurableSpace (O i)] [∀ i, BorelSpace (O i)]

theorem actual_probability_readout
    (q : ∀ i, C(K, O i))
    (hsep : Function.Injective (fun x : K => fun i => q i x))
    (μ ν : A → ProbabilityMeasure K)
    (hp : ∀ a, Measure.Regular
      ((μ a : Measure K).toSignedMeasure - (ν a : Measure K).toSignedMeasure).toJordanDecomposition.posPart)
    (hn : ∀ a, Measure.Regular
      ((μ a : Measure K).toSignedMeasure - (ν a : Measure K).toSignedMeasure).toJordanDecomposition.negPart)
    (hcompact : IsCompact (Set.range (fun a => signedFunctional
      ((μ a : Measure K).toSignedMeasure - (ν a : Measure K).toSignedMeasure))))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ J : Finset I, ∀ a,
      let r := finiteObservationReadout (fun i x => q i x) J
      let V := ((μ a : Measure K).toSignedMeasure - (ν a : Measure K).toSignedMeasure).totalVariation.real univ
      (V / 2 - δ < totalVariation (massVector ((μ a).map r)) (massVector ((ν a).map r)) ∧
       totalVariation (massVector ((μ a).map r)) (massVector ((ν a).map r)) ≤ V / 2) ∧
      ∀ y, (((μ a : Measure K).toSignedMeasure - (ν a : Measure K).toSignedMeasure).map r) {y} =
        massVector ((μ a).map r) y - massVector ((ν a).map r) y := by
  obtain ⟨J, hJ⟩ := exists_uniform_finite_readout_variation q hsep
    (fun a => (μ a : Measure K).toSignedMeasure - (ν a : Measure K).toSignedMeasure)
    hp hn hcompact (2 * δ) (by positivity)
  refine ⟨J, fun a => ?_⟩
  let r := finiteObservationReadout (fun i x => q i x) J
  have hr : Measurable r := (continuous_pi (fun j => (q j.val).continuous)).measurable
  have hj := hJ a
  rw [probability_difference_map _ _ r hr, probability_variation ((μ a).map r) ((ν a).map r)] at hj
  refine ⟨⟨by change _ / 2 - δ < _; linarith [hj.1], by change _ ≤ _ / 2; linarith [hj.2]⟩, ?_⟩
  intro y
  rw [probability_difference_map _ _ r hr]
  simp only [sub_apply, Measure.toSignedMeasure_apply_measurable (measurableSet_singleton y), massVector]
  rfl

-- Native Mathlib tvDist is FULL variation, not the statistical half convention.
theorem exact_check_1 (μ ν : ProbabilityMeasure K) :
    MeasureTheory.tvDist (μ : Measure K) (ν : Measure K) =
      ((μ : Measure K).toSignedMeasure - (ν : Measure K).toSignedMeasure).totalVariation.real univ := by
  rw [MeasureTheory.tvDist, MeasureTheory.etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist,
    ← SignedMeasure.totalVariation_eq_variation]
  rfl
end W0

-- The exact factorization telescope, with measurable structures added explicitly.
section Window
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]
variable {Q : ℕ → Type*} [∀ n, Finite (Q n)] [∀ n, TopologicalSpace (Q n)]
  [∀ n, DiscreteTopology (Q n)] [∀ n, MeasurableSpace (Q n)] [∀ n, BorelSpace (Q n)]
variable (q : ∀ n, X → Q n) (p : ∀ n, Q (n+1) → Q n)
  (hq : ∀ n, Continuous (q n)) (hsurj : ∀ n, Function.Surjective (q n))
  (hcompat : ∀ n x, q n x = p n (q (n+1) x))
  (hbasis : IsTopologicalBasis {U : Set X | ∃ n z, U = q n ⁻¹' {z}})
variable {Y Action : Type*} [Finite Y] [TopologicalSpace Y] [DiscreteTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] [Finite Action]

include p hq hsurj hcompat hbasis in
theorem whole_response_law (F : Action → X → X) (hF : ∀ a, Continuous (F a))
    (o : X → Y) (ho : Continuous o) (H : ℕ) :
    let W := {w : List Action // w.length ≤ H}
    let response : X → (W → Y) := fun x w => o (runWord F w.val x)
    ∃ N, ∃ g : Q N → (W → Y),
      (∀ x, g (q N x) = response x) ∧
      (∀ μ : Measure X, μ.map response = (μ.map (q N)).map g) ∧
      (∀ μ ν : Measure X, μ.map (q N) = ν.map (q N) → μ.map response = ν.map response) ∧
      (∀ μ ν : Measure X,
        measurableTotalVariation (μ.map response) (ν.map response) ≤
          measurableTotalVariation (μ.map (q N)) (ν.map (q N))) := by
  classical
  dsimp only
  let W := {w : List Action // w.length ≤ H}
  letI : Fintype Action := Fintype.ofFinite Action
  letI : Fintype Y := Fintype.ofFinite Y
  letI : Fintype W := (List.finite_length_le Action H).fintype
  let response : X → (W → Y) := fun x w => o (runWord F w.val x)
  obtain ⟨N, hN⟩ := (compact_observation_factorization
    (Y := Y) q p hq hsurj hcompat hbasis).2 F hF o ho H
  let g : Q N → (W → Y) := fun z => response (Function.surjInv (hsurj N) z)
  have hg (x : X) : g (q N x) = response x := by
    funext w
    exact hN _ x (Function.rightInverse_surjInv (hsurj N) (q N x)) w.val w.property
  have hgm : Measurable g := measurable_of_countable g
  have hfactor : g ∘ q N = response := funext hg
  have hlaw (μ : Measure X) : μ.map response = (μ.map (q N)).map g := by
    rw [Measure.map_map hgm (hq N).measurable, hfactor]
  exact ⟨N, g, hg, hlaw,
    fun μ ν h => by rw [hlaw, hlaw, h],
    fun μ ν => by rw [hlaw, hlaw]; exact measurable_total_variation_map_le _ _ g hgm⟩

-- The public window conjunct fixes the whole table on each stage fiber.
theorem window_finite_TV {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (N : ℕ) (g : Q N → T)
    (μ ν : ProbabilityMeasure X) :
    letI : Fintype (Q N) := Fintype.ofFinite (Q N)
    totalVariation (massVector (((μ.map (q N)).map g)))
      (massVector (((ν.map (q N)).map g))) ≤
      totalVariation (massVector (μ.map (q N))) (massVector (ν.map (q N))) := by
  letI : Fintype (Q N) := Fintype.ofFinite (Q N)
  exact finite_tv_map g (μ.map (q N)) (ν.map (q N))

-- W0 may be transferred to a nested level only with BOTH original telescopes.
include p hq hsurj hcompat hbasis in
theorem nested_stage_recovery
    [T2Space X] [ZeroDimensionalSpace X]
    (hsep : Function.Injective (fun x => fun n => q n x))
    {A : Type*} (s : A → SignedMeasure X)
    (hp : ∀ a, Measure.Regular (s a).toJordanDecomposition.posPart)
    (hn : ∀ a, Measure.Regular (s a).toJordanDecomposition.negPart)
    (hc : IsCompact (Set.range (fun a => signedFunctional (s a))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ a,
      (s a).totalVariation.real univ - ε < (SignedMeasure.totalVariation ((s a).map (q N))).real univ ∧
      (SignedMeasure.totalVariation ((s a).map (q N))).real univ ≤ (s a).totalVariation.real univ := by
  classical
  letI : ∀ n, Fintype (Q n) := fun n => Fintype.ofFinite (Q n)
  let sensors : ∀ n, C(X, Q n) := fun n => ⟨q n, hq n⟩
  obtain ⟨J, hJ⟩ := exists_uniform_finite_readout_variation sensors hsep s hp hn hc ε hε
  let r := finiteObservationReadout (fun n x => q n x) J
  have hr : Continuous r := continuous_pi (fun j => hq j.val)
  obtain ⟨N, g, hg, _⟩ := (compact_observation_factorization.{_, _, _, 0}
    (Y := FiniteObservationOutput Q J) q p hq hsurj hcompat hbasis).1 r hr
  have hgmeas : Measurable g := measurable_of_countable g
  have heq (a : A) : ((s a).map (q N)).map g = (s a).map r := by
    apply VectorMeasure.ext
    intro B hB
    rw [VectorMeasure.map_apply _ hgmeas hB,
      VectorMeasure.map_apply _ (hq N).measurable (hgmeas hB),
      VectorMeasure.map_apply _ hr.measurable hB]
    congr 1
    ext x
    change g (q N x) ∈ B ↔ r x ∈ B
    rw [hg x]
  have contract (a : A) :
      (SignedMeasure.totalVariation ((s a).map r)).real univ ≤ (SignedMeasure.totalVariation ((s a).map (q N))).real univ := by
    have h := VectorMeasure.variation_map_le (μ := (s a).map (q N)) (φ := g) univ
    rw [← SignedMeasure.totalVariation_eq_variation,
      ← SignedMeasure.totalVariation_eq_variation,
      Measure.map_apply hgmeas MeasurableSet.univ, preimage_univ, heq a] at h
    exact ENNReal.toReal_mono (measure_ne_top _ _) h
  refine ⟨N, fun a => ⟨(hJ a).1.trans_le (contract a), ?_⟩⟩
  have h := VectorMeasure.variation_map_le (μ := s a) (φ := q N) univ
  rw [← SignedMeasure.totalVariation_eq_variation, ← SignedMeasure.totalVariation_eq_variation,
    Measure.map_apply (hq N).measurable MeasurableSet.univ, preimage_univ] at h
  exact ENNReal.toReal_mono (measure_ne_top _ _) h
end Window

-- Separate native finite-thread result; no change of measurable carrier or universal stage.
theorem exact_check_2 {B : ℕ → Type*} [∀ l, Finite (B l)] [∀ l, MeasurableSpace (B l)]
    [∀ l, MeasurableSingletonClass (B l)] (q : (l : ℕ) → B (l+1) → B l) (n : ℕ)
    (P Q : Measure (Fin n → D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation.Thread B q))
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    measurableTotalVariation P Q = ⨆ l, measurableTotalVariation
      (P.map (D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation.levelProjection q n l))
      (Q.map (D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation.levelProjection q n l)) :=
  D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation.total_variation_eq_iSup_level q n P Q

#check @actual_probability_readout
#check @whole_response_law
#check @nested_stage_recovery
#print axioms probability_difference_map
#print axioms probability_variation
#print axioms actual_probability_readout
#print axioms whole_response_law
#print axioms window_finite_TV
#print axioms nested_stage_recovery
#check @exact_check_1
#print axioms exact_check_1
#check @exact_check_2
#print axioms exact_check_2

#check @probability_difference_map
#check @probability_variation
#check @window_finite_TV

end AtlasObservationCheck
