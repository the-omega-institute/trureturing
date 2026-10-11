/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Probability transport of the actual stopped-word laws to complete legal tails. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open FourthSegmentStoppedLaw NativeFullResidual NativeBorelCommonFlow NativeBorelRepresentation
open NativeConditionalControl.Tail

private theorem inclusion_embedding (s : ActivePhase) :
    MeasurableEmbedding (Subtype.val : ValidTail s → RawTail) :=
  ⟨Subtype.val_injective, measurable_subtype_coe, fun E _ =>
    (Set.to_countable _).measurableSet⟩

private theorem stopped_legal (s : ActivePhase) (ω : Stream) : Valid s (stoppedReadWord s ω) := by
  cases h : stoppedReadWord s ω with
  | none => trivial
  | some w => exact ((stopped_word_fiber s ω w).mp h).2

private theorem legal_range_mass (s : ActivePhase) (r : unitInterval) :
    explicitStoppedWordLaw s r (Set.range (Subtype.val : ValidTail s → RawTail)) = 1 := by
  rw [← (actual_fourth_segment_stopped_word_law r s).2,
    Measure.map_apply (measurable_stopped_read_word s) (Set.to_countable _).measurableSet]
  have he : (stoppedReadWord s) ⁻¹' Set.range (Subtype.val : ValidTail s → RawTail) =
      Set.univ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨⟨stoppedReadWord s ω, stopped_legal s ω⟩, rfl⟩
  rw [he, measure_univ]

/-- The law is pulled back from the actual stopped-word law, with legal range mass one. -/
def native (s : ActivePhase) (r : unitInterval) : ProbabilityMeasure (ValidTail s) :=
  ⟨(explicitStoppedWordLaw s r).comap Subtype.val, ⟨by
    rw [(inclusion_embedding s).comap_apply, Set.image_univ]
    exact legal_range_mass s r⟩⟩

theorem native_coordinate (s : ActivePhase) (r : unitInterval) (t : ValidTail s) :
    (native s r : Measure _) {t} = explicitStoppedWordLaw s r {t.val} := by
  change (explicitStoppedWordLaw s r).comap (Subtype.val : ValidTail s → RawTail) {t} = _
  rw [(inclusion_embedding s).comap_apply, Set.image_singleton]

/-- Mapping the transported probability law back recovers the actual native law. -/
theorem native_map (s : ActivePhase) (r : unitInterval) :
    (native s r : Measure (ValidTail s)).map (Subtype.val : ValidTail s → RawTail) = explicitStoppedWordLaw s r := by
  apply Measure.ext_of_singleton
  intro t
  rw [(inclusion_embedding s).map_apply]
  by_cases h : Valid s t
  · have he : (Subtype.val : ValidTail s → RawTail) ⁻¹' {t} = {⟨t, h⟩} := by
      ext x
      simp [Subtype.ext_iff]
    rw [he, native_coordinate]
  · have he : (Subtype.val : ValidTail s → RawTail) ⁻¹' {t} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hx => h (hx ▸ x.property)
    rw [he, measure_empty]
    cases t with
    | none => exact False.elim (h trivial)
    | some w => simp only [explicit_finite_mass, Valid] at h ⊢; rw [if_neg h]

theorem native_atoms (r : unitInterval) :
    (∀ n i, (native .p r : Measure _) {pAtom n i} =
      (if i = 0 then alphaMass r else betaMass r ^ 2) *
        (alphaMass r * betaMass r) ^ n) ∧
    (native .beta r : Measure _) {betaStop} = betaMass r ∧
    (∀ n i, (native .beta r : Measure _) {betaAtom n i} =
      alphaMass r * (if i = 0 then alphaMass r else betaMass r ^ 2) *
        (alphaMass r * betaMass r) ^ n) ∧
    (∀ s, (native s r : Measure _) {infinity s} = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i
    rw [native_coordinate]
    change explicitStoppedWordLaw .p r {some (pWord n i)} = _
    rw [explicit_finite_mass, if_pos ⟨i, n, rfl⟩, p_word_mass]
  · rw [native_coordinate]
    change explicitStoppedWordLaw .beta r {some [1]} = _
    rw [explicit_finite_mass,
      if_pos ⟨1, Or.inl ⟨rfl, rfl⟩⟩]
    simp [betaStop, wordMass, betaMass]
  · intro n i
    rw [native_coordinate]
    change explicitStoppedWordLaw .beta r {some (0 :: pWord n i)} = _
    rw [explicit_finite_mass, if_pos ⟨i, Or.inr ⟨n, rfl⟩⟩]
    change wordMass r (0 :: pWord n i) = _
    simp only [wordMass, List.map_cons, List.prod_cons]
    rw [bernoulli_alpha]
    change alphaMass r * wordMass r (pWord n i) = _
    rw [p_word_mass, mul_assoc]
  · intro s
    rw [native_coordinate]
    cases s <;> simp [infinity, explicitStoppedWordLaw, Measure.sum_apply]

private theorem p_atom_tail (j n : ℕ) (i : Letter) :
    pAtom n i ∈ tailSet .p j ↔ j ≤ n := by
  fin_cases i <;> simp [tailSet, pAtom, infinity, p_word_injective]

private theorem beta_atom_tail (j n : ℕ) (i : Letter) :
    betaAtom n i ∈ tailSet .beta j ↔ j ≤ n := by
  fin_cases i <;> simp [tailSet, betaAtom, infinity, p_word_injective]

private theorem beta_stop_not_tail (j : ℕ) : betaStop ∉ tailSet .beta j := by
  simp [tailSet, betaStop, betaAtom, infinity]

private theorem native_p_expansion (r : unitInterval) :
    (native .p r : Measure _) = Measure.sum (fun n : ℕ =>
      (alphaMass r * (alphaMass r * betaMass r) ^ n) • Measure.dirac (pAtom n 0) +
      (betaMass r ^ 2 * (alphaMass r * betaMass r) ^ n) • Measure.dirac (pAtom n 1)) := by
  apply Measure.ext_of_singleton
  rintro ⟨t, ht⟩
  cases t with
  | none =>
    simpa [infinity, Measure.sum_apply, pAtom] using (native_atoms r).2.2.2 .p
  | some w =>
    obtain ⟨i, n, rfl⟩ := ht
    have h := (native_atoms r).1 n i
    fin_cases i <;>
      simpa [pAtom, Measure.sum_apply, Pi.single_apply, p_word_injective] using h

private theorem native_beta_expansion (r : unitInterval) :
    (native .beta r : Measure _) = betaMass r • Measure.dirac betaStop +
      Measure.sum (fun n : ℕ =>
        (alphaMass r ^ 2 * (alphaMass r * betaMass r) ^ n) • Measure.dirac (betaAtom n 0) +
        (alphaMass r * betaMass r ^ 2 * (alphaMass r * betaMass r) ^ n) •
          Measure.dirac (betaAtom n 1)) := by
  apply Measure.ext_of_singleton
  rintro ⟨t, ht⟩
  cases t with
  | none =>
    simpa [infinity, Measure.sum_apply, betaAtom, betaStop] using
      (native_atoms r).2.2.2 .beta
  | some w =>
    obtain ⟨i, hi⟩ := ht
    rcases hi with ⟨rfl, rfl⟩ | ⟨n, rfl⟩
    · simpa [betaStop, betaAtom, Measure.sum_apply] using (native_atoms r).2.1
    · have h := (native_atoms r).2.2.1 n i
      fin_cases i <;>
        simpa [betaStop, betaAtom, Measure.sum_apply, Pi.single_apply, p_word_injective, pow_two] using h

private theorem geometric_tail (z d : ℝ≥0∞) (j : ℕ) :
    (∑' n : ℕ, if j ≤ n then d * z ^ n else 0) = z ^ j * ∑' n : ℕ, d * z ^ n := by
  classical
  have h : (∑' n : ℕ, if j ≤ n + j then d * z ^ (n + j) else 0) =
      ∑' n : ℕ, if j ≤ n then d * z ^ n else 0 := by
    apply Function.Injective.tsum_eq (g := fun n : ℕ => n + j)
      (f := fun n : ℕ => if j ≤ n then d * z ^ n else 0)
      (fun _ _ he => Nat.add_right_cancel he)
    intro n hn
    by_cases hj : j ≤ n
    · exact ⟨n - j, Nat.sub_add_cancel hj⟩
    · exact False.elim (hn (by simp [hj]))
  rw [← h]
  simp only [Nat.le_add_left, if_true]
  calc
    _ = ∑' n : ℕ, z ^ j * (d * z ^ n) := tsum_congr (fun n => by
      rw [pow_add]
      ac_rfl)
    _ = _ := ENNReal.tsum_mul_left

/-- Every source tail has its exact mass, including the suspended depth-zero factor. -/
theorem native_tails (r : unitInterval) (j : ℕ) :
    (native .p r : Measure _) (tailSet .p j) = (alphaMass r * betaMass r) ^ j ∧
    (native .beta r : Measure _) (tailSet .beta j) =
      alphaMass r * (alphaMass r * betaMass r) ^ j := by
  classical
  have hp : ∀ j, (native .p r : Measure _) (tailSet .p j) =
      ∑' n : ℕ, if j ≤ n then
        (alphaMass r + betaMass r ^ 2) * (alphaMass r * betaMass r) ^ n else 0 := by
    intro j
    rw [native_p_expansion, Measure.sum_apply _ (Set.to_countable _).measurableSet]
    apply tsum_congr
    intro n
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
      smul_eq_mul, Set.indicator_apply, Pi.one_apply, p_atom_tail]
    split_ifs <;> simp [add_mul]
  have hp0 : ∑' n : ℕ,
      (alphaMass r + betaMass r ^ 2) * (alphaMass r * betaMass r) ^ n = 1 := by
    have h0 : tailSet .p 0 = Set.univ := by
      ext t
      rcases t with ⟨t, ht⟩
      cases t with
      | none => simp [tailSet, infinity]
      | some w =>
        obtain ⟨i, n, rfl⟩ := ht
        change pAtom n i ∈ tailSet .p 0 ↔ True
        simp [p_atom_tail]
    simpa [h0] using (hp 0).symm
  refine ⟨?_, ?_⟩
  · rw [hp, geometric_tail, hp0, mul_one]
  · rw [native_beta_expansion, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply, Set.indicator_of_notMem (beta_stop_not_tail j),
      smul_zero, zero_add, Measure.sum_apply _ (Set.to_countable _).measurableSet]
    calc
      _ = alphaMass r * (∑' n : ℕ, if j ≤ n then
          (alphaMass r + betaMass r ^ 2) * (alphaMass r * betaMass r) ^ n else 0) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro n
        simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
          smul_eq_mul, Set.indicator_apply, Pi.one_apply, beta_atom_tail]
        split_ifs <;> simp [pow_two, mul_add, add_mul, mul_assoc]
      _ = _ := by rw [geometric_tail, hp0, mul_one]

theorem native_emission (s : ActivePhase) (r : unitInterval) :
    emission s (native s r) = alphaMass r := by
  cases s with
  | p => simpa [emission] using (native_atoms r).1 0 0
  | beta =>
    change 1 - (native .beta r : Measure _) {betaStop} = alphaMass r
    rw [(native_atoms r).2.1]
    have h : alphaMass r + betaMass r = 1 := by
      simp [alphaMass, betaMass, ← ENNReal.coe_add]
    rw [← h, ENNReal.add_sub_cancel_right (by simp [betaMass])] 

def endpoint (b : Bool) : unitInterval := if b then upperRate else lowerRate

private theorem endpoint_regular (s : ActivePhase) (b : Bool) :
    Regular s (native s (endpoint b)) := by
  have hr : lower ≤ alphaMass (endpoint b) ∧ alphaMass (endpoint b) ≤ upper := by
    constructor
    · apply (ENNReal.toReal_le_toReal (by unfold lower; finiteness)
        (by simp [alphaMass])).mp
      cases b <;> norm_num [endpoint, alphaMass, lowerRate, upperRate, lower]
    · apply (ENNReal.toReal_le_toReal (by simp [alphaMass])
        (by unfold upper; finiteness)).mp
      cases b <;> norm_num [endpoint, alphaMass, lowerRate, upperRate, upper]
  have hz : alphaMass (endpoint b) * betaMass (endpoint b) ≤ tailRate := by
    apply (ENNReal.toReal_le_toReal (by unfold alphaMass betaMass; finiteness)
      (by unfold tailRate; finiteness)).mp
    cases b <;> norm_num [endpoint, alphaMass, betaMass, lowerRate, upperRate, tailRate,
      unitInterval.symm, ENNReal.toReal_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [native_emission]; exact hr.1
  · rw [native_emission]; exact hr.2
  · intro j
    cases s with
    | p =>
      change (native .p (endpoint b) : Measure _) (tailSet .p j) ≤ 1 * tailRate ^ j
      rw [(native_tails _ _).1, one_mul]
      exact pow_le_pow_left₀ bot_le hz j
    | beta =>
      change (native .beta (endpoint b) : Measure _) (tailSet .beta j) ≤ upper * tailRate ^ j
      rw [(native_tails _ _).2]
      exact mul_le_mul' hr.2 (pow_le_pow_left₀ bot_le hz j)

/-- The two original native endpoints inhabit the exact regular descriptor spaces. -/
def nativeEndpoint (s : ActivePhase) (b : Bool) : RegularDescriptor s :=
  ⟨native s (endpoint b), endpoint_regular s b⟩

/-- The endpoint boxes hold at every complete atom with the original min/max ordering. -/
theorem native_endpoint_boxes (s : ActivePhase) (b : Bool) : EndpointBox (nativeEndpoint s b) := by
  intro t
  change min _ _ ≤ (native s (endpoint b) : Measure _) {t} ∧
    (native s (endpoint b) : Measure _) {t} ≤ max _ _
  rw [native_coordinate]
  cases b
  · exact ⟨min_le_left _ _, le_max_left _ _⟩
  · exact ⟨min_le_right _ _, le_max_right _ _⟩

private theorem native_prefixB (r : unitInterval) :
    (native .p r : Measure _).comap prependB = betaMass r • (native .beta r : Measure _) := by
  apply Measure.ext_of_singleton
  intro t
  rw [prependB_embedding.comap_apply, Set.image_singleton, Measure.smul_apply, smul_eq_mul]
  rcases t with ⟨t, ht⟩
  cases t with
  | none =>
    change (native .p r : Measure _) {infinity .p} =
        betaMass r * (native .beta r : Measure _) {infinity .beta}
    rw [(native_atoms r).2.2.2, (native_atoms r).2.2.2, mul_zero]
  | some w =>
    obtain ⟨i, hi⟩ := ht
    rcases hi with ⟨rfl, rfl⟩ | ⟨n, rfl⟩
    · change (native .p r : Measure _) {pAtom 0 1} =
        betaMass r * (native .beta r : Measure _) {betaStop}
      rw [(native_atoms r).1, (native_atoms r).2.1]
      simp [pow_two]
    · have he : prependB (betaAtom n i) = pAtom (n + 1) i := by
        apply Subtype.ext
        exact congrArg some (p_word_succ n i).symm
      change (native .p r : Measure _) {prependB (betaAtom n i)} =
        betaMass r * (native .beta r : Measure _) {betaAtom n i}
      rw [he, (native_atoms r).1, (native_atoms r).2.2.1, pow_succ]
      ring

private theorem native_prefixA (r : unitInterval) :
    (native .beta r : Measure _).comap prependA = alphaMass r • (native .p r : Measure _) := by
  apply Measure.ext_of_singleton
  intro t
  rw [prependA_embedding.comap_apply, Set.image_singleton, Measure.smul_apply, smul_eq_mul]
  rcases t with ⟨t, ht⟩
  cases t with
  | none =>
    change (native .beta r : Measure _) {infinity .beta} =
        alphaMass r * (native .p r : Measure _) {infinity .p}
    rw [(native_atoms r).2.2.2, (native_atoms r).2.2.2, mul_zero]
  | some w =>
    obtain ⟨i, n, rfl⟩ := ht
    change (native .beta r : Measure _) {betaAtom n i} =
      alphaMass r * (native .p r : Measure _) {pAtom n i}
    rw [(native_atoms r).1, (native_atoms r).2.2.1]
    ring

/-- Both residuals agree with the whole opposite native law, including infinity. -/
theorem native_endpoint_residuals (b : Bool) :
    residualB (nativeEndpoint .p b) = law (nativeEndpoint .beta b) ∧
    residualA (nativeEndpoint .beta b) = law (nativeEndpoint .p b) := by
  have hr0 : alphaMass (endpoint b) ≠ 0 := by
    intro h
    have ht := congrArg ENNReal.toReal h
    cases b <;> norm_num [endpoint, alphaMass, lowerRate, upperRate] at ht
  have hs0 : betaMass (endpoint b) ≠ 0 := by
    intro h
    have ht := congrArg ENNReal.toReal h
    cases b <;> norm_num [endpoint, betaMass, lowerRate, upperRate, unitInterval.symm] at ht
  have hr : alphaMass (endpoint b) ≠ ∞ := by simp [alphaMass]
  have hs : betaMass (endpoint b) ≠ ∞ := by simp [betaMass]
  have hc : 1 - alphaMass (endpoint b) = betaMass (endpoint b) := by
    have h : betaMass (endpoint b) + alphaMass (endpoint b) = 1 := by
      simp [alphaMass, betaMass, ← ENNReal.coe_add]
    rw [← h, ENNReal.add_sub_cancel_right (by simp [alphaMass])] 
  constructor
  · change (1 - emission .p (native .p (endpoint b)))⁻¹ •
      (native .p (endpoint b) : Measure _).comap prependB = _
    rw [native_emission, hc, native_prefixB, smul_smul,
      ENNReal.inv_mul_cancel hs0 hs, one_smul]
    rfl
  · change (emission .beta (native .beta (endpoint b)))⁻¹ •
      (native .beta (endpoint b) : Measure _).comap prependA = _
    rw [native_emission, native_prefixA, smul_smul,
      ENNReal.inv_mul_cancel hr0 hr, one_smul]
    rfl

private def endpointMixture {X : Type*} [MeasurableSpace X]
    (a b : X) (θ : unitInterval) : Measure X :=
  betaMass θ • Measure.dirac a + alphaMass θ • Measure.dirac b

private instance mixture_probability {X : Type*} [MeasurableSpace X]
    (a b : X) (θ : unitInterval) : IsProbabilityMeasure (endpointMixture a b θ) := by
  constructor
  simp [endpointMixture, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    alphaMass, betaMass, ← ENNReal.coe_add]

private theorem endpoints_distinct (s : ActivePhase) :
    nativeEndpoint s false ≠ nativeEndpoint s true := by
  intro h
  have he := congrArg (fun D : RegularDescriptor s => emission s D.val) h
  change emission s (native s (endpoint false)) = emission s (native s (endpoint true)) at he
  rw [native_emission, native_emission] at he
  have hr := congrArg ENNReal.toReal he
  norm_num [endpoint, alphaMass, lowerRate, upperRate, ] at hr

private def endpointSuccessor (s t : ActivePhase) (D : RegularDescriptor s) : RegularDescriptor t := by
  classical
  exact if D = nativeEndpoint s true then nativeEndpoint t true else nativeEndpoint t false

private theorem successor_measurable (s t : ActivePhase) :
    Measurable (endpointSuccessor s t) := by
  classical
  exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const

private theorem successor_endpoint (s t : ActivePhase) (b : Bool) :
    endpointSuccessor s t (nativeEndpoint s b) = nativeEndpoint t b := by
  classical
  cases b <;> simp [endpointSuccessor, endpoints_distinct]

private def endpointKernel (s t : ActivePhase) :
    Kernel (RegularDescriptor s) (RegularDescriptor t) :=
  Kernel.deterministic (endpointSuccessor s t) (successor_measurable s t)

private instance endpointKernel_markov (s t : ActivePhase) : IsMarkovKernel (endpointKernel s t) :=
  inferInstanceAs (IsMarkovKernel (Kernel.deterministic _ _))

private theorem mixture_compProd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] (a b : X) (f : X → Y) (hf : Measurable f) (θ : unitInterval) :
    endpointMixture a b θ ⊗ₘ Kernel.deterministic f hf =
      endpointMixture (a, f a) (b, f b) θ := by
  ext E hE
  rw [endpointMixture, Measure.compProd_add_left, Measure.compProd_smul_left,
    Measure.compProd_smul_left]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_compProd_apply hE, Kernel.deterministic_apply,
    Measure.dirac_apply' _ (measurable_prodMk_left hE), endpointMixture,
    Measure.dirac_apply' _ hE]
  by_cases ha : (a, f a) ∈ E <;> by_cases hb : (b, f b) ∈ E <;>
    simp [Set.indicator, ha, hb]

private theorem mixture_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (a b : X × Y) (θ : unitInterval) :
    (endpointMixture a b θ).fst = endpointMixture a.1 b.1 θ := by
  simp [Measure.fst, endpointMixture, Measure.map_add, measurable_fst,
    Measure.map_smul, Measure.map_dirac]

private theorem mixture_snd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (a b : X × Y) (θ : unitInterval) :
    (endpointMixture a b θ).snd = endpointMixture a.2 b.2 θ := by
  simp [Measure.snd, endpointMixture, Measure.map_add, measurable_snd,
    Measure.map_smul, Measure.map_dirac]

private theorem mixture_ae {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (a b : X) (θ : unitInterval) (P : X → Prop) (ha : P a) (hb : P b) :
    ∀ᵐ x ∂endpointMixture a b θ, P x := by
  rw [endpointMixture, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure (by simpa only [ae_dirac_eq, Filter.eventually_pure] using ha) _,
    Measure.ae_smul_measure (by simpa only [ae_dirac_eq, Filter.eventually_pure] using hb) _⟩

/-- These are mixtures of Diracs at endpoint descriptors, for every interval weight. -/
def endpointCommonFlow (θ : unitInterval) : CommonFlow where
  nuP := endpointMixture (nativeEndpoint .p false) (nativeEndpoint .p true) θ
  nuB := endpointMixture (nativeEndpoint .beta false) (nativeEndpoint .beta true) θ
  probP := inferInstance
  probB := inferInstance
  GammaB := endpointMixture (nativeEndpoint .p false, nativeEndpoint .beta false)
    (nativeEndpoint .p true, nativeEndpoint .beta true) θ
  GammaA := endpointMixture (nativeEndpoint .beta false, nativeEndpoint .p false)
    (nativeEndpoint .beta true, nativeEndpoint .p true) θ
  probGammaB := inferInstance
  probGammaA := inferInstance
  B := endpointKernel .p .beta
  A := endpointKernel .beta .p
  markovB := inferInstance
  markovA := inferInstance
  marginB₁ := mixture_fst _ _ _
  marginB₂ := mixture_snd _ _ _
  marginA₁ := mixture_fst _ _ _
  marginA₂ := mixture_snd _ _ _
  disintegrateB := ⟨by
    rw [mixture_fst]
    simpa only [endpointKernel, successor_endpoint] using mixture_compProd
      (nativeEndpoint .p false) (nativeEndpoint .p true)
      (endpointSuccessor .p .beta) (successor_measurable .p .beta) θ⟩
  disintegrateA := ⟨by
    rw [mixture_fst]
    simpa only [endpointKernel, successor_endpoint] using mixture_compProd
      (nativeEndpoint .beta false) (nativeEndpoint .beta true)
      (endpointSuccessor .beta .p) (successor_measurable .beta .p) θ⟩
  normalizedB := by
    apply mixture_ae
    all_goals
      rw [(native_endpoint_residuals _).1]
      change law _ = (lawKernel .beta) ∘ₘ Measure.dirac
        (endpointSuccessor .p .beta (nativeEndpoint .p _))
      rw [successor_endpoint]
      simpa only [lawKernel, Kernel.coe_mk] using (Measure.dirac_bind (lawKernel .beta).measurable
        (nativeEndpoint .beta _)).symm
  normalizedA := by
    apply mixture_ae
    all_goals
      rw [(native_endpoint_residuals _).2]
      change law _ = (lawKernel .p) ∘ₘ Measure.dirac
        (endpointSuccessor .beta .p (nativeEndpoint .beta _))
      rw [successor_endpoint]
      simpa only [lawKernel, Kernel.coe_mk] using (Measure.dirac_bind (lawKernel .p).measurable
        (nativeEndpoint .p _)).symm
  boxP := mixture_ae _ _ _ _ (native_endpoint_boxes .p false) (native_endpoint_boxes .p true)
  boxB := mixture_ae _ _ _ _ (native_endpoint_boxes .beta false) (native_endpoint_boxes .beta true)

/-- The native upper singleton has exactly the mixture weight; no weight is divided out. -/
private theorem endpoint_native_mass (θ : unitInterval) :
    (endpointCommonFlow θ).nuP {nativeEndpoint .p true} = alphaMass θ := by
  simp [endpointCommonFlow, endpointMixture, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply, endpoints_distinct]

/-- Every weight is attained by a full common flow; the witness is the endpoint edge mixture. -/
theorem endpoint_flow_inhabited (θ : unitInterval) :
    ∃ F : CommonFlow, F.nuP {nativeEndpoint .p true} = alphaMass θ :=
  ⟨endpointCommonFlow θ, endpoint_native_mass θ⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws
