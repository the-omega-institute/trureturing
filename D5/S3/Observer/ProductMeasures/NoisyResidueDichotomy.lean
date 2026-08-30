/- GID: D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy
   generality: I
   mirror-B: D5/B/S3/Observer/ProductMeasures/NoisyResidueDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Noisy residue products split by energy; zero, empty, and dependence are audited. -/
/- Library-search audit trail (2026-08-25): Six searches covered exact object names,
   Mathlib vocabulary, digest text, repository neighbors, generalized product-law
   shapes, and measure/information/probability synonyms. Repository neighbors include
   `SignalKakutaniDichotomy`, finite marginal readouts, and shared-source dependence,
   but none proves this criterion. Pinned Mathlib has no Kakutani product theorem;
   Loogle absolute-continuity and singularity shapes found no bridge, and LeanSearch
   API attempts failed. The exact independence bridge found and reused is
   `iIndepFun.map_fun_eq_infinitePi_map₀'`. -/

import Mathlib.Probability.Distributions.Uniform
import D5.S3.Observer.ProductMeasures.FinitePmfDichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory Topology

noncomputable section

namespace D5.S3.Observer.ProductMeasures.NoisyResidueDichotomy

open D5.S3.Observer.ProductMeasures.FinitePmfLikelihood
open D5.S3.Observer.ProductMeasures.FinitePmfDichotomy

universe u v w

variable {Output : Nat -> Type u}
  [∀ i, MeasurableSpace (Output i)]
  [∀ i, MeasurableSingletonClass (Output i)]
  [∀ i, Fintype (Output i)]

/-- The coordinate law obtained by applying a noisy channel to a state's residue. -/
def noisyResidueLaw {State : Type v} {Residue : Nat -> Type w}
    {Out : Nat -> Type u}
    (residue : (i : Nat) -> State -> Residue i)
    (channel : (i : Nat) -> Residue i -> PMF (Out i))
    (state : State) (i : Nat) : PMF (Out i) :=
  channel i (residue i state)

/-- The coordinatewise squared Hellinger energy between two states. -/
def pairLocalHellingerEnergy {State : Type v}
    (law : State -> (i : Nat) -> PMF (Output i))
    (x y : State) (i : Nat) : Real :=
  energy (law x i) (law y i)

/-- The coordinates whose local Hellinger energy cannot distinguish the two states. -/
def blindCoordinates {State : Type v}
    (law : State -> (i : Nat) -> PMF (Output i))
    (x y : State) : Set Nat :=
  {i | pairLocalHellingerEnergy law x y i = 0}

/-- The infinite transcript assembled from a countable family of observations. -/
def infiniteTranscript {Omega : Type v}
    (observation : (i : Nat) -> Omega -> Output i)
    (omega : Omega) (i : Nat) : Output i :=
  observation i omega

/-- The countable product law associated with a state's coordinate laws. -/
def transcriptLaw {State : Type v}
    (law : State -> (i : Nat) -> PMF (Output i))
    (state : State) : Measure ((i : Nat) -> Output i) :=
  productLaw (law state)

/-- Noisy-residue product laws are singular exactly when their energy is not summable. -/
theorem noisy_residue_product_completion_criterion
    {State : Type v} {Residue : Nat -> Type w}
    (residue : (i : Nat) -> State -> Residue i)
    (channel : (i : Nat) -> Residue i -> PMF (Output i))
    (x y : State)
    (hlocal : ∀ i,
      (noisyResidueLaw residue channel x i).toMeasure ≪
          (noisyResidueLaw residue channel y i).toMeasure ∧
        (noisyResidueLaw residue channel y i).toMeasure ≪
          (noisyResidueLaw residue channel x i).toMeasure) :
    transcriptLaw (noisyResidueLaw residue channel) x ⟂ₘ
        transcriptLaw (noisyResidueLaw residue channel) y ↔
      ¬Summable (pairLocalHellingerEnergy
        (noisyResidueLaw residue channel) x y) := by
  exact (finite_pmf_kakutani_dichotomy hlocal).1

#print axioms noisy_residue_product_completion_criterion

/-- Independent transcripts satisfy the same energy-versus-singularity criterion. -/
theorem noisy_residue_independent_completion_criterion
    {State : Type v} {Residue : Nat -> Type w}
    {OmegaP OmegaQ : Type*} [MeasurableSpace OmegaP] [MeasurableSpace OmegaQ]
    (residue : (i : Nat) -> State -> Residue i)
    (channel : (i : Nat) -> Residue i -> PMF (Output i))
    (x y : State) (P : Measure OmegaP) (Q : Measure OmegaQ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : (i : Nat) -> OmegaP -> Output i)
    (Y : (i : Nat) -> OmegaQ -> Output i)
    (hXlaw : ∀ i, HasLaw (X i)
      (noisyResidueLaw residue channel x i).toMeasure P)
    (hYlaw : ∀ i, HasLaw (Y i)
      (noisyResidueLaw residue channel y i).toMeasure Q)
    (hXind : iIndepFun X P) (hYind : iIndepFun Y Q)
    (hlocal : ∀ i,
      (noisyResidueLaw residue channel x i).toMeasure ≪
          (noisyResidueLaw residue channel y i).toMeasure ∧
        (noisyResidueLaw residue channel y i).toMeasure ≪
          (noisyResidueLaw residue channel x i).toMeasure) :
    P.map (infiniteTranscript X) ⟂ₘ Q.map (infiniteTranscript Y) ↔
      ¬Summable (pairLocalHellingerEnergy
        (noisyResidueLaw residue channel) x y) := by
  have hP : P.map (infiniteTranscript X) =
      transcriptLaw (noisyResidueLaw residue channel) x := by
    rw [transcriptLaw, productLaw]
    have hind := hXind.map_fun_eq_infinitePi_map₀'
      (fun i => (hXlaw i).aemeasurable)
    change P.map (fun omega i => X i omega) = _
    rw [hind]
    congr 1
    funext i
    exact (hXlaw i).map_eq
  have hQ : Q.map (infiniteTranscript Y) =
      transcriptLaw (noisyResidueLaw residue channel) y := by
    rw [transcriptLaw, productLaw]
    have hind := hYind.map_fun_eq_infinitePi_map₀'
      (fun i => (hYlaw i).aemeasurable)
    change Q.map (fun omega i => Y i omega) = _
    rw [hind]
    congr 1
    funext i
    exact (hYlaw i).map_eq
  rw [hP, hQ]
  exact noisy_residue_product_completion_criterion
    residue channel x y hlocal

#print axioms noisy_residue_independent_completion_criterion

omit [∀ i, MeasurableSingletonClass (Output i)] in
/-- Equal coordinate laws have zero total energy and equal product laws. -/
theorem equal_local_laws_zero_energy
    {State : Type v} (law : State -> (i : Nat) -> PMF (Output i))
    (x y : State) (heq : ∀ i, law x i = law y i) :
    let e := pairLocalHellingerEnergy law x y
    e = 0 ∧ Summable e ∧ (∑' i, e i) = 0 ∧ transcriptLaw law x = transcriptLaw law y := by
  dsimp only
  have henergy : pairLocalHellingerEnergy law x y = 0 := by
    funext i
    rw [pairLocalHellingerEnergy, heq i, energy]
    exact D5.S3.TotalVariation.Hellinger.hellinger_sq_self _
  have hlaw : law x = law y := by
    funext i
    exact heq i
  refine ⟨henergy, ?_, ?_, ?_⟩
  · rw [henergy]
    exact summable_zero
  · rw [henergy]
    exact tsum_zero
  · simp [transcriptLaw, hlaw]

#print axioms equal_local_laws_zero_energy

/-- A singleton output alphabet has identically zero local Hellinger energy. -/
theorem singleton_output_energy_zero :
    (fun _ : Nat => D5.S3.TotalVariation.Hellinger.hellingerSq
      (fun o => ((PMF.pure PUnit.unit : PMF PUnit) o).toReal)
      (fun o => ((PMF.pure PUnit.unit : PMF PUnit) o).toReal)) =
      (0 : Nat -> Real) := by
  funext i
  exact D5.S3.TotalVariation.Hellinger.hellinger_sq_self _

#print axioms singleton_output_energy_zero

/-- An empty output alphabet cannot support a probability mass function. -/
theorem empty_output_has_no_pmf (p : PMF Empty) : False := by
  have hmass := p.tsum_coe
  simp at hmass

#print axioms empty_output_has_no_pmf

private def localAcCounterexampleP (_ : Nat) : PMF Bool :=
  PMF.pure true

private def localAcCounterexampleQ (i : Nat) : PMF Bool :=
  if i = 0 then PMF.pure false else PMF.pure true

/-- Without local mutual absolute continuity, finite energy can coexist with singularity. -/
theorem local_mutual_absolute_continuity_is_necessary :
    ∃ p q : Nat -> PMF Bool,
      ¬(∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
        (q i).toMeasure ≪ (p i).toMeasure) ∧
      Summable (fun i => D5.S3.TotalVariation.Hellinger.hellingerSq
        (fun o => (p i o).toReal) (fun o => (q i o).toReal)) ∧
      productLaw p ⟂ₘ productLaw q := by
  refine ⟨localAcCounterexampleP, localAcCounterexampleQ, ?_, ?_, ?_⟩
  · intro hlocal
    have hac := (hlocal 0).1
    have hzero : (localAcCounterexampleQ 0).toMeasure ({true} : Set Bool) = 0 := by
      simp [localAcCounterexampleQ]
    have := hac hzero
    simp [localAcCounterexampleP] at this
  · apply summable_of_hasFiniteSupport
    rw [Function.HasFiniteSupport]
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro i hi
    simp only [Set.mem_singleton_iff]
    by_contra hne
    change D5.S3.TotalVariation.Hellinger.hellingerSq
      (fun o => (localAcCounterexampleP i o).toReal)
      (fun o => (localAcCounterexampleQ i o).toReal) ≠ 0 at hi
    apply hi
    have heq : localAcCounterexampleQ i = localAcCounterexampleP i := by
      simp [localAcCounterexampleP, localAcCounterexampleQ, hne]
    rw [heq]
    exact D5.S3.TotalVariation.Hellinger.hellinger_sq_self _
  · apply Measure.MutuallySingular.mk
      (s := {x | x 0 = false}) (t := {x | x 0 = true})
    · calc
        productLaw localAcCounterexampleP {x | x 0 = false} =
            (productLaw localAcCounterexampleP).map (fun x => x 0) {false} := by
          rw [Measure.map_apply (measurable_pi_apply 0)
            (Set.toFinite _).measurableSet]
          congr 1
        _ = (localAcCounterexampleP 0).toMeasure {false} := by
          rw [productLaw, Measure.infinitePi_map_eval]
        _ = 0 := by
          simp [localAcCounterexampleP]
    · calc
        productLaw localAcCounterexampleQ {x | x 0 = true} =
            (productLaw localAcCounterexampleQ).map (fun x => x 0) {true} := by
          rw [Measure.map_apply (measurable_pi_apply 0)
            (Set.toFinite _).measurableSet]
          congr 1
        _ = (localAcCounterexampleQ 0).toMeasure {true} := by
          rw [productLaw, Measure.infinitePi_map_eval]
        _ = 0 := by
          simp [localAcCounterexampleQ]
    · intro x hx
      by_cases h : x 0 = false
      · exact Or.inl h
      · exact Or.inr (Bool.eq_true_of_not_eq_false h)

#print axioms local_mutual_absolute_continuity_is_necessary

private def independenceCounterexampleSource : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

private instance independenceCounterexampleSource_isProbabilityMeasure :
    IsProbabilityMeasure independenceCounterexampleSource := by
  unfold independenceCounterexampleSource
  infer_instance

private def repeatedSourceObservation (i : Nat) (u : Bool) : Bool :=
  if i = 0 ∨ i = 1 then u else false

private def opposedSourceObservation (i : Nat) (u : Bool) : Bool :=
  if i = 0 then u else if i = 1 then !u else false

private def independenceCounterexampleLaw (i : Nat) : PMF Bool :=
  if i = 0 ∨ i = 1 then PMF.uniformOfFintype Bool else PMF.pure false

private lemma repeatedSourceObservation_hasLaw (i : Nat) :
    HasLaw (repeatedSourceObservation i) (independenceCounterexampleLaw i).toMeasure
      independenceCounterexampleSource := by
  constructor
  · exact (measurable_of_finite _).aemeasurable
  · rw [independenceCounterexampleSource,
      PMF.toMeasure_map (repeatedSourceObservation i)
        (PMF.uniformOfFintype Bool) (measurable_of_finite _)]
    congr 1
    ext b
    by_cases hi0 : i = 0
    · subst i
      simp [repeatedSourceObservation, independenceCounterexampleLaw]
    · by_cases hi1 : i = 1
      · subst i
        simp [repeatedSourceObservation, independenceCounterexampleLaw]
      · have hfun : repeatedSourceObservation i = Function.const Bool false := by
          funext u
          simp [repeatedSourceObservation, hi0, hi1]
        rw [hfun]
        simp [independenceCounterexampleLaw, hi0, hi1]

private lemma opposedSourceObservation_hasLaw (i : Nat) :
    HasLaw (opposedSourceObservation i) (independenceCounterexampleLaw i).toMeasure
      independenceCounterexampleSource := by
  constructor
  · exact (measurable_of_finite _).aemeasurable
  · rw [independenceCounterexampleSource,
      PMF.toMeasure_map (opposedSourceObservation i)
        (PMF.uniformOfFintype Bool) (measurable_of_finite _)]
    congr 1
    ext b
    by_cases hi0 : i = 0
    · subst i
      simp [opposedSourceObservation, independenceCounterexampleLaw]
    · by_cases hi1 : i = 1
      · subst i
        cases b <;>
          norm_num [opposedSourceObservation, independenceCounterexampleLaw,
            PMF.map_apply, PMF.uniformOfFintype_apply, Fintype.card_bool]
      · have hfun : opposedSourceObservation i = Function.const Bool false := by
          funext u
          simp [opposedSourceObservation, hi0, hi1]
        rw [hfun]
        simp [independenceCounterexampleLaw, hi0, hi1]

private lemma independenceCounterexample_singular :
    independenceCounterexampleSource.map
        (infiniteTranscript repeatedSourceObservation) ⟂ₘ
      independenceCounterexampleSource.map
        (infiniteTranscript opposedSourceObservation) := by
  have hrepeat : Measurable (infiniteTranscript repeatedSourceObservation) :=
    measurable_pi_lambda _ fun _ => measurable_of_finite _
  have hopposed : Measurable (infiniteTranscript opposedSourceObservation) :=
    measurable_pi_lambda _ fun _ => measurable_of_finite _
  have heq : MeasurableSet {z : Nat → Bool | z 0 = z 1} :=
    measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1)
  have hne : MeasurableSet {z : Nat → Bool | z 0 ≠ z 1} := by
    exact heq.compl
  apply Measure.MutuallySingular.mk
      (s := {z : Nat → Bool | z 0 ≠ z 1})
      (t := {z : Nat → Bool | z 0 = z 1})
  · rw [Measure.map_apply hrepeat hne]
    simp [infiniteTranscript, repeatedSourceObservation]
  · rw [Measure.map_apply hopposed heq]
    simp [infiniteTranscript, opposedSourceObservation]
  · intro z hz
    by_cases h : z 0 = z 1
    · exact Or.inr h
    · exact Or.inl h

/-- Matching marginals do not imply the criterion when coordinate independence is omitted. -/
theorem coordinate_independence_is_necessary :
    ∃ (source : Measure Bool) (law : Nat -> PMF Bool)
      (X Y : Nat -> Bool -> Bool),
      IsProbabilityMeasure source ∧
      (∀ i, HasLaw (X i) (law i).toMeasure source) ∧
      (∀ i, HasLaw (Y i) (law i).toMeasure source) ∧
      (∀ i, (law i).toMeasure ≪ (law i).toMeasure ∧
        (law i).toMeasure ≪ (law i).toMeasure) ∧
      ¬(source.map (infiniteTranscript X) ⟂ₘ
          source.map (infiniteTranscript Y) ↔
        ¬Summable (fun i => energy (Output := fun _ => Bool) (i := i)
          (law i) (law i))) := by
  refine ⟨independenceCounterexampleSource, independenceCounterexampleLaw,
    repeatedSourceObservation, opposedSourceObservation, inferInstance,
    repeatedSourceObservation_hasLaw, opposedSourceObservation_hasLaw,
    fun _ => ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩, ?_⟩
  intro hcriterion
  have henergy : Summable (fun i => energy (Output := fun _ => Bool) (i := i)
      (independenceCounterexampleLaw i) (independenceCounterexampleLaw i)) := by
    have hzero : (fun i => energy (Output := fun _ => Bool) (i := i)
        (independenceCounterexampleLaw i) (independenceCounterexampleLaw i)) = 0 := by
      funext i
      exact D5.S3.TotalVariation.Hellinger.hellinger_sq_self _
    rw [hzero]
    exact summable_zero
  exact (hcriterion.mp independenceCounterexample_singular) henergy

#print axioms coordinate_independence_is_necessary


end D5.S3.Observer.ProductMeasures.NoisyResidueDichotomy
