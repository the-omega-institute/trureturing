/- GID: D5/S3/Resource/VandermondeHyperbolicRefutation
   generality: G
   mirror-B: D5/B/S3/Resource/VandermondeHyperbolicRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Resource/VandermondeHyperbolicRefutation.claim; result=D5/S3/Resource/VandermondeHyperbolicRefutation.result; claim=D5/S3/Resource/VandermondeHyperbolicRefutation.claim
   digest: A twenty-column quadratic-curve code violates the universal hyperbolic bound. -/
import D5.S3.Resource.MinimumRetrievalTime
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Resource.VandermondeHyperbolicRefutation

open D5.S3.Resource.MinimumRetrievalTime
open MeasureTheory Set
open scoped BigOperators ENNReal

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def quadraticCurve {K : Type*} [Field K] (parameter : K) : Fin 3 → K :=
  fun coordinate => parameter ^ coordinate.val


def observedTypes {alphabet types : Type*} [DecidableEq types]
    (labels : alphabet → types) (time : ℕ) (sample : ℕ → alphabet) : Finset types :=
  Finset.univ.image (fun index : Fin time => labels (sample index.val))


def physicalParameter (index : Fin 20) : ZMod 11 :=
  if index.val < 10 then 0 else (index.val - 9 : ℕ)

def columns (index : Fin 20) : Fin 3 → ZMod 11 :=
  quadraticCurve (physicalParameter index)

def hyperbolicBound (K : Type*) [Field K] : Prop :=
  ∀ firstSize secondSize : ℕ, ∀ (_hfirst : 0 < firstSize), 0 < secondSize →
    2 ≤ max firstSize secondSize →
    ∀ length : ℕ, ∀ (_hlength : firstSize + secondSize ≤ length),
    letI : NeZero length := ⟨by omega⟩
    ∀ generator : Fin length → (Fin (firstSize + secondSize) → K),
      Matrix.rank (Matrix.of (fun row column => generator column row)) =
        firstSize + secondSize →
      (firstSize : ℝ) / (∫ sample, (retrievalTime generator
        (firstCoordinateFile K firstSize secondSize) sample).toReal
        ∂uniformSamples (Fin length)) +
      (secondSize : ℝ) / (∫ sample, (retrievalTime generator
        (secondCoordinateFile K firstSize secondSize) sample).toReal
        ∂uniformSamples (Fin length)) ≤ 1

def claim : Prop :=
  ∀ model : FiniteFieldModel, @hyperbolicBound model.carrier model.field

theorem result : ¬ claim := by
  have hnegative : ¬ hyperbolicBound (ZMod 11) := by
    classical
    have hgeometry {K : Type} [Field K] (parameters : Finset K) :
        (firstCoordinateFile K 1 2 ≤ Submodule.span K
          (quadraticCurve '' (parameters : Set K)) ↔
          0 ∈ parameters ∨ 3 ≤ parameters.card) ∧
        (secondCoordinateFile K 1 2 ≤ Submodule.span K
          (quadraticCurve '' (parameters : Set K)) ↔ 3 ≤ parameters.card) := by
      classical
      let generated := Submodule.span K (quadraticCurve '' (parameters : Set K))
      let basis := Pi.basisFun K (Fin 3)
      have hfirstIndices : {coordinate : Fin (1 + 2) | coordinate.val < 1} = {0} := by
        ext coordinate
        fin_cases coordinate <;> decide
      have hsecondIndices : {coordinate : Fin (1 + 2) | 1 ≤ coordinate.val} = {1, 2} := by
        ext coordinate
        fin_cases coordinate <;> decide
      have hfirst : firstCoordinateFile K 1 2 = Submodule.span K {basis 0} := by
        simp only [firstCoordinateFile, hfirstIndices, Set.image_singleton]
        rfl
      have hsecond : secondCoordinateFile K 1 2 = Submodule.span K {basis 1, basis 2} := by
        simp only [secondCoordinateFile, hsecondIndices, Set.image_pair]
        rfl
      have hzero : quadraticCurve (0 : K) = basis 0 := by
        ext coordinate
        fin_cases coordinate <;> simp [quadraticCurve, basis, Pi.basisFun_apply]
      have hlarge : 3 ≤ parameters.card → generated = ⊤ := by
        intro hcard
        obtain ⟨first, second, third, hfirstMem, hsecondMem, hthirdMem,
          hfirstSecond, hfirstThird, hsecondThird⟩ :=
          Finset.two_lt_card_iff.mp (by omega : 2 < parameters.card)
        let nodes : Fin 3 → K := ![first, second, third]
        have hinjective : Function.Injective nodes := by
          intro left right heq
          fin_cases left <;> fin_cases right <;> simp_all [nodes]
        have hindependent : LinearIndependent K (fun index : Fin 3 =>
            quadraticCurve (nodes index)) :=
          Matrix.linearIndependent_rows_of_det_ne_zero
            (Matrix.det_vandermonde_ne_zero_iff.mpr hinjective)
        have hspan : Submodule.span K (Set.range (fun index : Fin 3 =>
            quadraticCurve (nodes index))) = ⊤ :=
          hindependent.span_eq_top_of_card_eq_finrank (by simp)
        apply top_unique
        rw [← hspan]
        apply Submodule.span_mono
        rintro vector ⟨index, rfl⟩
        refine ⟨nodes index, ?_, rfl⟩
        fin_cases index <;> simp_all [nodes]
      have hcover : parameters.card ≤ 2 → ∃ first second : K,
          parameters ⊆ {first, second} ∧
          (0 ∉ parameters → first ≠ 0 ∧ second ≠ 0) := by
        intro hcard
        have hcases : parameters.card = 0 ∨ parameters.card = 1 ∨ parameters.card = 2 := by
          omega
        rcases hcases with hempty | hone | htwo
        · have hemptySet := Finset.card_eq_zero.mp hempty
          exact ⟨1, 1, by simp [hemptySet], fun _ => ⟨one_ne_zero, one_ne_zero⟩⟩
        · obtain ⟨parameter, rfl⟩ := Finset.card_eq_one.mp hone
          refine ⟨parameter, parameter, by simp, ?_⟩
          intro hnotZero
          have hnonzero : parameter ≠ 0 := by simpa [eq_comm] using hnotZero
          exact ⟨hnonzero, hnonzero⟩
        · obtain ⟨first, second, _, rfl⟩ := Finset.card_eq_two.mp htwo
          refine ⟨first, second, Finset.Subset.refl _, ?_⟩
          intro hnotZero
          simpa [eq_comm] using hnotZero
      have hobstruction : ∀ first second : K, parameters ⊆ {first, second} →
          ∀ vector ∈ generated,
            vector 2 - (first + second) * vector 1 + (first * second) * vector 0 = 0 := by
        intro first second hsubset
        let functional : (Fin 3 → K) →ₗ[K] K :=
          LinearMap.proj 2 - (first + second) • LinearMap.proj 1 +
            (first * second) • LinearMap.proj 0
        have hkernel : generated ≤ LinearMap.ker functional := by
          apply Submodule.span_le.mpr
          rintro vector ⟨parameter, hparameter, rfl⟩
          have hchoice := Finset.mem_insert.mp (hsubset hparameter)
          rcases hchoice with rfl | hchoice
          · simp [LinearMap.mem_ker, functional, quadraticCurve]
            ring
          · have heq := Finset.mem_singleton.mp hchoice
            subst parameter
            simp [LinearMap.mem_ker, functional, quadraticCurve]
            ring
        intro vector hvector
        simpa [LinearMap.mem_ker, functional] using hkernel hvector
      constructor
      · rw [hfirst, Submodule.span_singleton_le_iff_mem]
        constructor
        · intro hmem
          by_contra hfailure
          have hnotZero : 0 ∉ parameters := fun hzeroMem => hfailure (Or.inl hzeroMem)
          have hsmall : parameters.card ≤ 2 := by
            have := fun hcard => hfailure (Or.inr hcard)
            omega
          obtain ⟨first, second, hsubset, hnonzero⟩ := hcover hsmall
          have heq := hobstruction first second hsubset (basis 0) hmem
          have hproduct : first * second = 0 := by
            simpa [basis, Pi.basisFun_apply] using heq
          exact (mul_ne_zero (hnonzero hnotZero).1 (hnonzero hnotZero).2) hproduct
        · rintro (hzeroMem | hcard)
          · rw [← hzero]
            exact Submodule.subset_span ⟨0, hzeroMem, rfl⟩
          · change basis 0 ∈ generated
            rw [hlarge hcard]
            trivial
      · constructor
        · intro hfile
          by_contra hsmall
          obtain ⟨first, second, hsubset, _⟩ := hcover (by omega)
          have hlast : basis 2 ∈ generated := hfile (by
            rw [hsecond]
            exact Submodule.subset_span (by simp))
          have heq := hobstruction first second hsubset (basis 2) hlast
          have hfalse : (1 : K) = 0 := by
            simpa [basis, Pi.basisFun_apply] using heq
          exact one_ne_zero hfalse
        · intro hcard
          change secondCoordinateFile K 1 2 ≤ generated
          rw [hlarge hcard]
          exact le_top
    have hprefixProbability {alphabet types : Type}
        [Fintype alphabet] [Nonempty alphabet] [MeasurableSpace alphabet]
        [MeasurableSingletonClass alphabet] [DecidableEq types]
        (labels : alphabet → types) (allowed : Finset types) (hallowed : 2 ≤ allowed.card)
        (time : ℕ) :
        ((uniformSamples alphabet) {sample | observedTypes labels time sample ⊆ allowed ∧
          (observedTypes labels time sample).card ≤ 2}).toReal =
          (∑ pair ∈ allowed.powersetCard 2,
            ((Finset.univ.filter (fun index => labels index ∈ pair)).card /
              (Fintype.card alphabet : ℝ)) ^ time) -
          ((allowed.card : ℝ) - 2) * (∑ label ∈ allowed,
            ((Finset.univ.filter (fun index => labels index = label)).card /
              (Fintype.card alphabet : ℝ)) ^ time) +
          (((allowed.card - 1).choose 2 : ℕ) : ℝ) * (if time = 0 then 1 else 0) := by
      classical
      let μ := uniformSamples alphabet
      haveI : IsProbabilityMeasure μ := by
        dsimp [μ, uniformSamples]
        infer_instance
      let contained (subset : Finset types) : Set (ℕ → alphabet) :=
        {sample | observedTypes labels time sample ⊆ subset}
      let indicator (subset : Finset types) (sample : ℕ → alphabet) : ℝ :=
        if sample ∈ contained subset then 1 else 0
      have hcylinder : ∀ subset : Finset types, contained subset =
          Set.pi (Finset.range time) (fun _ => {index | labels index ∈ subset}) := by
        intro subset
        ext sample
        simp only [contained, observedTypes, Finset.image_subset_iff, Finset.mem_univ,
          forall_true_left, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe,
          Finset.mem_range]
        exact ⟨fun h index hindex => h ⟨index, hindex⟩,
          fun h index => h index.val index.isLt⟩
      have hmeas : ∀ subset : Finset types, MeasurableSet (contained subset) := by
        intro subset
        rw [hcylinder]
        exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ =>
          (Set.to_countable _).measurableSet)
      have hprobability : ∀ subset : Finset types,
          (μ (contained subset)).toReal =
          ((Finset.univ.filter (fun index => labels index ∈ subset)).card /
            (Fintype.card alphabet : ℝ)) ^ time := by
        intro subset
        rw [hcylinder]
        dsimp only [μ, uniformSamples]
        rw [Measure.infinitePi_pi _ (fun _ _ => (Set.to_countable _).measurableSet)]
        simp only [PMF.toMeasure_uniformOfFintype_apply _ (Set.to_countable _).measurableSet,
          Finset.prod_const, Finset.card_range, Fintype.card_subtype,
          ENNReal.toReal_pow, ENNReal.toReal_div,
          ENNReal.toReal_natCast]
        simp
      have hintegrable : ∀ subset : Finset types, Integrable (indicator subset) μ := by
        intro subset
        have hind := (integrable_const (μ := μ) (1 : ℝ)).indicator (hmeas subset)
        have heq : indicator subset = (contained subset).indicator (fun _ => (1 : ℝ)) := by
          funext sample
          simp only [indicator, Set.indicator_apply]
        rw [heq]
        exact hind
      have hintegral : ∀ subset : Finset types, (∫ sample, indicator subset sample ∂μ) =
          ((Finset.univ.filter (fun index => labels index ∈ subset)).card /
            (Fintype.card alphabet : ℝ)) ^ time := by
        intro subset
        rw [← hprobability]
        simpa [indicator, Set.indicator, Measure.real_def] using
          (integral_indicator_one (μ := μ) (hmeas subset) :
            (∫ sample, (contained subset).indicator (fun _ => (1 : ℝ)) sample ∂μ) = _)
      have hcount : ∀ (observed : Finset types) (order : ℕ),
          (∑ subset ∈ allowed.powersetCard order, (if observed ⊆ subset then (1 : ℝ) else 0)) =
          (((allowed.powersetCard order).filter (observed ⊆ ·)).card : ℝ) := by
        intro observed order
        rw [← Finset.sum_filter]
        simp
      have hpointwise : ∀ sample : ℕ → alphabet,
          (if observedTypes labels time sample ⊆ allowed ∧
              (observedTypes labels time sample).card ≤ 2 then (1 : ℝ) else 0) =
          (∑ pair ∈ allowed.powersetCard 2, indicator pair sample) -
          ((allowed.card : ℝ) - 2) * (∑ label ∈ allowed, indicator {label} sample) +
          (((allowed.card - 1).choose 2 : ℕ) : ℝ) * indicator ∅ sample := by
        intro sample
        let observed := observedTypes labels time sample
        have hsingles : (∑ label ∈ allowed, indicator {label} sample) =
            ∑ subset ∈ allowed.powersetCard 1, indicator subset sample := by
          simp only [Finset.powersetCard_one, Finset.sum_map, Function.Embedding.coeFn_mk]
        rw [hsingles]
        simp only [indicator, contained, Set.mem_setOf_eq]
        change (if observed ⊆ allowed ∧ observed.card ≤ 2 then (1 : ℝ) else 0) =
          (∑ pair ∈ allowed.powersetCard 2, if observed ⊆ pair then (1 : ℝ) else 0) -
          ((allowed.card : ℝ) - 2) *
            (∑ singleton ∈ allowed.powersetCard 1, if observed ⊆ singleton then (1 : ℝ) else 0) +
          (((allowed.card - 1).choose 2 : ℕ) : ℝ) * (if observed ⊆ ∅ then 1 else 0)
        rw [hcount observed 2, hcount observed 1]
        by_cases hsubset : observed ⊆ allowed
        · by_cases hsmall : observed.card ≤ 2
          · rw [Finset.card_filter_powersetCard_subset observed allowed 2 hsubset hsmall]
            have hcases : observed.card = 0 ∨ observed.card = 1 ∨ observed.card = 2 := by
              omega
            rcases hcases with hzero | hone | htwo
            · have hempty := Finset.card_eq_zero.mp hzero
              rw [Finset.card_filter_powersetCard_subset observed allowed 1 hsubset (by omega)]
              simp only [hempty, Finset.card_empty, Nat.sub_zero,
                Finset.empty_subset, true_and, if_true, Nat.choose_one_right, mul_one]
              rw [Nat.cast_choose_two, Nat.cast_choose_two,
                Nat.cast_sub (by omega : 1 ≤ allowed.card)]
              norm_num <;> ring
            · rw [Finset.card_filter_powersetCard_subset observed allowed 1 hsubset (by omega)]
              have hnonempty : ¬ observed ⊆ ∅ := by
                intro h; have := Finset.card_le_card h; simp only [Finset.card_empty] at this
                omega
              simp only [hsubset, hsmall, and_self, if_true, hone, Nat.reduceSub,
                Nat.choose_one_right, Nat.choose_zero_right, hnonempty, if_false,
                mul_zero, add_zero, Nat.cast_one]
              rw [Nat.cast_sub (by omega : 1 ≤ allowed.card)]
              norm_num <;> ring
            · have hfilter : (allowed.powersetCard 1).filter (observed ⊆ ·) = ∅ := by
                apply Finset.filter_eq_empty_iff.mpr
                intro subset hmem hsub
                have := Finset.card_le_card hsub
                have := (Finset.mem_powersetCard.mp hmem).2
                omega
              have hnonempty : ¬ observed ⊆ ∅ := by
                intro h; have := Finset.card_le_card h; simp only [Finset.card_empty] at this
                omega
              simp [hsubset, hsmall, htwo, hfilter, hnonempty]
          · have hfilters : ∀ order ≤ 2,
                (allowed.powersetCard order).filter (observed ⊆ ·) = ∅ := by
              intro order horder
              apply Finset.filter_eq_empty_iff.mpr
              intro subset hmem hsub
              have := Finset.card_le_card hsub
              have := (Finset.mem_powersetCard.mp hmem).2
              omega
            have hnonempty : ¬ observed ⊆ ∅ := by
              intro h; have := Finset.card_le_card h; simp only [Finset.card_empty] at this
              omega
            simp [hsmall, hfilters 2 (by omega), hfilters 1 (by omega), hnonempty]
        · have hfilters : ∀ order,
              (allowed.powersetCard order).filter (observed ⊆ ·) = ∅ := by
            intro order
            apply Finset.filter_eq_empty_iff.mpr
            intro subset hmem hsub
            exact hsubset (hsub.trans (Finset.mem_powersetCard.mp hmem).1)
          have hnonempty : ¬ observed ⊆ ∅ := fun h => hsubset (h.trans (Finset.empty_subset _))
          simp [hsubset, hfilters, hnonempty]
      have hempty : indicator ∅ = fun _ => if time = 0 then (1 : ℝ) else 0 := by
        funext sample
        by_cases htime : time = 0
        · subst time
          simp [indicator, contained, observedTypes]
        · have hnonempty : observedTypes labels time sample ≠ ∅ := by
            have hmem : labels (sample 0) ∈ observedTypes labels time sample := by
              exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
            intro hemptySet
            simpa [hemptySet] using hmem
          simp [indicator, contained, Finset.subset_empty, htime, hnonempty]
      have hfailureMeas : MeasurableSet {sample | observedTypes labels time sample ⊆ allowed ∧
          (observedTypes labels time sample).card ≤ 2} := by
        let wordEvent : Set (Fin time → alphabet) := {word |
          (Finset.univ.image (fun index => labels (word index))) ⊆ allowed ∧
          (Finset.univ.image (fun index => labels (word index))).card ≤ 2}
        exact (Set.to_countable wordEvent).measurableSet.preimage
          (measurable_pi_iff.mpr (fun index => measurable_pi_apply index.val))
      have hpairInt : Integrable
          (fun sample => ∑ pair ∈ allowed.powersetCard 2, indicator pair sample) μ :=
        integrable_finsetSum _ (fun pair _ => hintegrable pair)
      have hsingleInt : Integrable
          (fun sample => ∑ label ∈ allowed, indicator {label} sample) μ :=
        integrable_finsetSum _ (fun label _ => hintegrable {label})
      change μ.real _ = _
      rw [← integral_indicator_one (μ := μ) hfailureMeas]
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
      simp_rw [hpointwise]
      calc
        _ = (∫ sample, (∑ pair ∈ allowed.powersetCard 2, indicator pair sample) -
              ((allowed.card : ℝ) - 2) * (∑ label ∈ allowed, indicator {label} sample) ∂μ) +
            (∫ sample, (((allowed.card - 1).choose 2 : ℕ) : ℝ) * indicator ∅ sample ∂μ) :=
          integral_add (hpairInt.sub (hsingleInt.const_mul ((allowed.card : ℝ) - 2)))
            ((hintegrable ∅).const_mul (((allowed.card - 1).choose 2 : ℕ) : ℝ))
        _ = _ := by
          rw [integral_sub hpairInt (hsingleInt.const_mul ((allowed.card : ℝ) - 2)),
            integral_const_mul, integral_const_mul,
            integral_finsetSum _ (fun pair _ => hintegrable pair),
            integral_finsetSum _ (fun label _ => hintegrable {label})]
          rw [hempty]
          simp_rw [hintegral]
          simp [Finset.mem_singleton]
    let μ := uniformSamples (Fin 20)
    haveI : IsProbabilityMeasure μ := by dsimp [μ, uniformSamples]; infer_instance
    have hfull : Submodule.span (ZMod 11) (Set.range columns) = ⊤ := by
      let nodes : Fin 3 → ZMod 11 := fun index => index.val
      have hinjective : Function.Injective nodes := by decide
      have hindependent : LinearIndependent (ZMod 11)
          (fun index : Fin 3 => quadraticCurve (nodes index)) :=
        Matrix.linearIndependent_rows_of_det_ne_zero
          (Matrix.det_vandermonde_ne_zero_iff.mpr hinjective)
      have hspan := hindependent.span_eq_top_of_card_eq_finrank (by simp)
      apply top_unique
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro vector ⟨index, rfl⟩
      fin_cases index
      · exact Submodule.subset_span ⟨0, rfl⟩
      · exact Submodule.subset_span ⟨10, rfl⟩
      · exact Submodule.subset_span ⟨11, rfl⟩
    have hprefix : ∀ sample time, prefixSpan columns sample time =
        Submodule.span (ZMod 11) (quadraticCurve ''
          (observedTypes physicalParameter time sample : Set (ZMod 11))) := by
      intro sample time
      simp only [prefixSpan, columns, observedTypes, Finset.coe_image, Finset.coe_univ,
        Set.image_univ]
      rw [← Set.range_comp]
      rfl
    let mixed : Finset (ZMod 11) := Finset.univ.erase 0
    have hfirstFailure : ∀ time, {sample | ¬ recovered columns
        (firstCoordinateFile (ZMod 11) 1 2) time sample} =
        {sample | observedTypes physicalParameter time sample ⊆ mixed ∧
          (observedTypes physicalParameter time sample).card ≤ 2} := by
      intro time
      ext sample
      rw [Set.mem_setOf_eq, recovered, hprefix,
        (hgeometry (observedTypes physicalParameter time sample)).1]
      simp only [not_or, not_le, Set.mem_setOf_eq]
      have hsubset : observedTypes physicalParameter time sample ⊆ mixed ↔
          0 ∉ observedTypes physicalParameter time sample := by
        simp [mixed, Finset.subset_iff]
      rw [hsubset]
      constructor
      · rintro ⟨hzero, hcard⟩
        exact ⟨hzero, by omega⟩
      · rintro ⟨hzero, hcard⟩
        exact ⟨hzero, by omega⟩
    have hsecondFailure : ∀ time, {sample | ¬ recovered columns
        (secondCoordinateFile (ZMod 11) 1 2) time sample} =
        {sample | observedTypes physicalParameter time sample ⊆ Finset.univ ∧
          (observedTypes physicalParameter time sample).card ≤ 2} := by
      intro time
      ext sample
      rw [Set.mem_setOf_eq, recovered, hprefix,
        (hgeometry (observedTypes physicalParameter time sample)).2]
      simp only [Set.mem_setOf_eq, Finset.subset_univ, true_and]
      omega
    have hsingleCount : ∀ parameter : ZMod 11,
        (Finset.univ.filter (fun index : Fin 20 => physicalParameter index = parameter)).card =
          if parameter = 0 then 10 else 1 := by decide
    have hpairCount : ∀ pair : Finset (ZMod 11), pair.card = 2 →
        (Finset.univ.filter (fun index : Fin 20 => physicalParameter index ∈ pair)).card =
          if 0 ∈ pair then 11 else 2 := by
      intro pair hcard
      rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ pair physicalParameter]
      simp_rw [hsingleCount]
      have hsplit : ∀ parameter : ZMod 11,
          (if parameter = 0 then (10 : ℕ) else 1) =
            1 + (if parameter = 0 then 9 else 0) := by
        intro parameter
        split_ifs <;> decide
      simp_rw [hsplit]
      simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
        Finset.sum_ite_eq', hcard]
      split_ifs <;> norm_num
    have hmixedCard : mixed.card = 10 := by decide
    have hpairZero : (((Finset.univ : Finset (ZMod 11)).powersetCard 2).filter
        (fun pair => 0 ∈ pair)).card = 10 := by decide
    have hpairNonzero : (((Finset.univ : Finset (ZMod 11)).powersetCard 2).filter
        (fun pair => 0 ∉ pair)).card = 45 := by decide
    have hfirstTail : ∀ time,
        (μ {sample | ¬ recovered columns (firstCoordinateFile (ZMod 11) 1 2)
          time sample}).toReal =
          45 * (1 / 10 : ℝ) ^ time - 80 * (1 / 20 : ℝ) ^ time +
          36 * (0 : ℝ) ^ time := by
      intro time
      rw [hfirstFailure]
      have hformula := hprefixProbability physicalParameter mixed
        (by rw [hmixedCard]; omega) time
      rw [hformula]
      have hnozero : ∀ pair ∈ mixed.powersetCard 2, 0 ∉ pair := by
        intro pair hpair hzero
        have := (Finset.mem_powersetCard.mp hpair).1 hzero
        simp [mixed] at this
      have hpairSum : (∑ pair ∈ mixed.powersetCard 2,
          ((Finset.univ.filter (fun index : Fin 20 => physicalParameter index ∈ pair)).card /
            (Fintype.card (Fin 20) : ℝ)) ^ time) = 45 * (1 / 10 : ℝ) ^ time := by
        have heq : ∀ pair ∈ mixed.powersetCard 2,
            (Finset.univ.filter (fun index : Fin 20 => physicalParameter index ∈ pair)).card =
            2 := fun pair hp => by
          rw [hpairCount pair (Finset.mem_powersetCard.mp hp).2, if_neg (hnozero pair hp)]
        trans ∑ pair ∈ mixed.powersetCard 2, (1 / 10 : ℝ) ^ time
        · apply Finset.sum_congr rfl
          intro pair hp
          rw [heq pair hp]
          norm_num
        · norm_num [Finset.card_powersetCard, hmixedCard, Nat.choose]
      have hsingleSum : (∑ parameter ∈ mixed,
          ((Finset.univ.filter (fun index : Fin 20 => physicalParameter index = parameter)).card /
            (Fintype.card (Fin 20) : ℝ)) ^ time) = 10 * (1 / 20 : ℝ) ^ time := by
        trans ∑ parameter ∈ mixed, (1 / 20 : ℝ) ^ time
        · apply Finset.sum_congr rfl
          intro parameter hp
          rw [hsingleCount, if_neg (by simpa [mixed, eq_comm] using
            (Finset.mem_erase.mp hp).1)]
          simp
        · simp [hmixedCard]
      rw [hpairSum, hsingleSum, hmixedCard]
      norm_num [Nat.choose]
      by_cases htime : time = 0
      · subst time; norm_num
      · simp [htime, zero_pow htime]
        ring
    have hsecondTail : ∀ time,
        (μ {sample | ¬ recovered columns (secondCoordinateFile (ZMod 11) 1 2)
          time sample}).toReal =
          10 * (11 / 20 : ℝ) ^ time + 45 * (1 / 10 : ℝ) ^ time -
          9 * (1 / 2 : ℝ) ^ time - 90 * (1 / 20 : ℝ) ^ time +
          45 * (0 : ℝ) ^ time := by
      intro time
      rw [hsecondFailure]
      have hformula := hprefixProbability physicalParameter Finset.univ
        (by decide) time
      rw [hformula]
      have hpairSum : (∑ pair ∈ (Finset.univ : Finset (ZMod 11)).powersetCard 2,
          ((Finset.univ.filter (fun index : Fin 20 => physicalParameter index ∈ pair)).card /
            (Fintype.card (Fin 20) : ℝ)) ^ time) =
          10 * (11 / 20 : ℝ) ^ time + 45 * (1 / 10 : ℝ) ^ time := by
        trans ∑ pair ∈ (Finset.univ : Finset (ZMod 11)).powersetCard 2,
          if 0 ∈ pair then (11 / 20 : ℝ) ^ time else (1 / 10 : ℝ) ^ time
        · apply Finset.sum_congr rfl
          intro pair hp
          rw [hpairCount pair (Finset.mem_powersetCard.mp hp).2]
          split_ifs <;> norm_num
        · rw [Finset.sum_ite]
          simp [hpairZero, hpairNonzero]
      have hsingleSum : (∑ parameter : ZMod 11,
          ((Finset.univ.filter (fun index : Fin 20 => physicalParameter index = parameter)).card /
            (Fintype.card (Fin 20) : ℝ)) ^ time) =
          (1 / 2 : ℝ) ^ time + 10 * (1 / 20 : ℝ) ^ time := by
        simp_rw [hsingleCount]
        trans ∑ parameter : ZMod 11,
          if parameter = 0 then (1 / 2 : ℝ) ^ time else (1 / 20 : ℝ) ^ time
        · apply Finset.sum_congr rfl
          intro parameter _
          split_ifs <;> norm_num
        · rw [Finset.sum_ite]
          have hzeroSingle : ((Finset.univ : Finset (ZMod 11)).filter
              (fun parameter => parameter = 0)).card = 1 := by decide
          have hnonzeroSingle : ((Finset.univ : Finset (ZMod 11)).filter
              (fun parameter => parameter ≠ 0)).card = 10 := by decide
          simp [hzeroSingle, hnonzeroSingle]
      rw [hpairSum, hsingleSum]
      norm_num [Nat.choose]
      by_cases htime : time = 0
      · subst time; norm_num
      · simp [htime, zero_pow htime]
        ring
    obtain ⟨_, _, hfirstSeries, _, _, _, _, hfirstMean⟩ :=
      retrieval_time_probability_bridge columns (firstCoordinateFile (ZMod 11) 1 2)
        (by rw [hfull]; exact le_top)
    obtain ⟨_, _, hsecondSeries, _, _, _, _, hsecondMean⟩ :=
      retrieval_time_probability_bridge columns (secondCoordinateFile (ZMod 11) 1 2)
        (by rw [hfull]; exact le_top)
    have hs0 : Summable (fun time : ℕ => (0 : ℝ) ^ time) :=
      (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(0 : ℝ)‖ < 1)).summable
    have hs20 : Summable (fun time : ℕ => (1 / 20 : ℝ) ^ time) :=
      (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 20 : ℝ)‖ < 1)).summable
    have hs10 : Summable (fun time : ℕ => (1 / 10 : ℝ) ^ time) :=
      (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 10 : ℝ)‖ < 1)).summable
    have hs2 : Summable (fun time : ℕ => (1 / 2 : ℝ) ^ time) :=
      (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).summable
    have hs55 : Summable (fun time : ℕ => (11 / 20 : ℝ) ^ time) :=
      (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(11 / 20 : ℝ)‖ < 1)).summable
    have hfirstExpectation : (∫ sample, (retrievalTime columns
        (firstCoordinateFile (ZMod 11) 1 2) sample).toReal ∂μ) = 34 / 19 := by
      rw [hfirstMean, hfirstSeries, ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
      trans (∑' time : ℕ, (45 * (1 / 10 : ℝ) ^ time - 80 * (1 / 20 : ℝ) ^ time +
        36 * (0 : ℝ) ^ time))
      · exact tsum_congr hfirstTail
      rw [Summable.tsum_add ((hs10.mul_left 45).sub (hs20.mul_left 80)) (hs0.mul_left 36),
        Summable.tsum_sub (hs10.mul_left 45) (hs20.mul_left 80)]
      simp only [tsum_mul_left]
      rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 10 : ℝ)‖ < 1),
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 20 : ℝ)‖ < 1),
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(0 : ℝ)‖ < 1)]
      norm_num
    have hsecondExpectation : (∫ sample, (retrievalTime columns
        (secondCoordinateFile (ZMod 11) 1 2) sample).toReal ∂μ) = 767 / 171 := by
      rw [hsecondMean, hsecondSeries, ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
      trans (∑' time : ℕ, (10 * (11 / 20 : ℝ) ^ time + 45 * (1 / 10 : ℝ) ^ time -
        9 * (1 / 2 : ℝ) ^ time - 90 * (1 / 20 : ℝ) ^ time + 45 * (0 : ℝ) ^ time))
      · exact tsum_congr hsecondTail
      rw [Summable.tsum_add
          ((((hs55.mul_left 10).add (hs10.mul_left 45)).sub (hs2.mul_left 9)).sub
            (hs20.mul_left 90)) (hs0.mul_left 45),
        Summable.tsum_sub
          (((hs55.mul_left 10).add (hs10.mul_left 45)).sub (hs2.mul_left 9))
            (hs20.mul_left 90),
        Summable.tsum_sub ((hs55.mul_left 10).add (hs10.mul_left 45)) (hs2.mul_left 9),
        Summable.tsum_add (hs55.mul_left 10) (hs10.mul_left 45)]
      simp only [tsum_mul_left]
      rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(11 / 20 : ℝ)‖ < 1),
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 10 : ℝ)‖ < 1),
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1),
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 20 : ℝ)‖ < 1),
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(0 : ℝ)‖ < 1)]
      norm_num
    have hrank : Matrix.rank (Matrix.of (fun row column => columns column row)) = 1 + 2 := by
      rw [Matrix.rank_eq_finrank_span_cols]
      change Module.finrank (ZMod 11) (Submodule.span (ZMod 11) (Set.range columns)) = _
      rw [hfull]
      simp
    intro hfieldBound
    have hbound := hfieldBound 1 2
      (by decide) (by decide) (by decide) 20 (by decide) columns hrank
    rw [hfirstExpectation, hsecondExpectation] at hbound
    norm_num at hbound
  intro hclaim
  exact hnegative (hclaim ⟨ZMod 11, inferInstance, inferInstance⟩)

end D5.S3.Resource.VandermondeHyperbolicRefutation
