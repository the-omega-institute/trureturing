/- GID: D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bernoulli product misses finite-support image; identity and degenerate cases audited. -/

import Mathlib

/- Library-search audit trail (2026-08-26): Mathlib `Measure.infinitePi_map_restrict`,
   `Measure.infinitePi_map_eval`, `iIndepFun_infinitePi`, and Borel-Cantelli were found.
   No projective-limit wrapper was needed: this module directly constructs the product
   measure. The index is Nat; no primality property is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ENNReal

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.FiniteMarginalGlobalReadoutContrast

open Filter MeasureTheory ProbabilityTheory Set

/- The coordinate law and its direct countable product. -/
def fairBias : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

def fairMarginal : Measure Bool := bernoulliMeasure true false fairBias

instance fairMarginal_isProbabilityMeasure : IsProbabilityMeasure fairMarginal := by
  unfold fairMarginal
  infer_instance

def fairProduct : Measure (Nat -> Bool) :=
  Measure.infinitePi (fun _ : Nat => fairMarginal)

instance fairProduct_isProbabilityMeasure : IsProbabilityMeasure fairProduct := by
  unfold fairProduct
  infer_instance

def finiteMarginal (J : Finset Nat) : Measure (J -> Bool) :=
  Measure.pi (fun _ : J => fairMarginal)

instance finiteMarginal_isProbabilityMeasure (J : Finset Nat) :
    IsProbabilityMeasure (finiteMarginal J) := by
  unfold finiteMarginal
  infer_instance

/- The global objects are finite subsets, read as finitely supported Boolean paths. -/
def readout (A : Finset Nat) : Nat -> Bool := fun n => decide (n ∈ A)

def finiteSupport : Set (Nat -> Bool) :=
  {x | (Function.support x).Finite}

def activationEvent (n : Nat) : Set (Nat -> Bool) :=
  (fun x => x n) ⁻¹' ({true} : Set Bool)

private theorem activation_event_measurable (n : Nat) :
    MeasurableSet (activationEvent n) := by
  exact measurable_pi_apply n (measurableSet_singleton true)

private theorem fair_marginal_true :
    fairMarginal ({true} : Set Bool) =
      (unitInterval.toNNReal fairBias : ENNReal) := by
  rw [fairMarginal, bernoulliMeasure_apply_of_mem_of_notMem fairBias
    (measurableSet_singleton true) (by decide) (by decide)]

private theorem fair_activation_mass_ne_zero :
    (unitInterval.toNNReal fairBias : ENNReal) ≠ 0 := by
  apply ne_of_gt
  rw [ENNReal.coe_pos, ← NNReal.coe_pos]
  change (0 : Real) < (1 / 2 : Real)
  norm_num

private theorem fair_product_activation (n : Nat) :
    fairProduct (activationEvent n) =
      (unitInterval.toNNReal fairBias : ENNReal) := by
  calc
    fairProduct (activationEvent n) =
        (fairProduct).map (fun x : Nat -> Bool => x n) ({true} : Set Bool) := by
      exact (Measure.map_apply (by fun_prop) (measurableSet_singleton true)).symm
    _ = fairMarginal ({true} : Set Bool) := by
      rw [fairProduct, Measure.infinitePi_map_eval]
    _ = (unitInterval.toNNReal fairBias : ENNReal) := fair_marginal_true

private theorem activation_events_independent :
    iIndepSet activationEvent fairProduct := by
  have hindependent :
      iIndepFun (fun n (x : Nat -> Bool) => x n) fairProduct := by
    exact iIndepFun_infinitePi (P := fun _ : Nat => fairMarginal)
      (X := fun _ : Nat => (id : Bool -> Bool)) (fun _ => measurable_id)
  apply (iIndepSet_iff_meas_biInter activation_event_measurable).2
  intro indices
  simpa only [activationEvent] using
    hindependent.measure_inter_preimage_eq_mul indices
      (fun _ _ => measurableSet_singleton true)

private theorem activation_measure_tsum_top :
    (∑' n, fairProduct (activationEvent n)) = ∞ := by
  rw [show (∑' n, fairProduct (activationEvent n)) =
      ∑' _ : Nat, (unitInterval.toNNReal fairBias : ENNReal) by
    apply tsum_congr
    intro n
    exact fair_product_activation n]
  exact ENNReal.tsum_const_eq_top_of_ne_zero fair_activation_mass_ne_zero

private theorem finite_support_disjoint_limsup (x : Nat -> Bool)
    (hfinite : (Function.support x).Finite) :
    x ∉ limsup activationEvent atTop := by
  rw [mem_limsup_iff_frequently_mem, Nat.frequently_atTop_iff_infinite]
  intro hinfinite
  apply hinfinite
  have heq : {n | x ∈ activationEvent n} = Function.support x := by
    ext n
    cases h : x n <;> simp [activationEvent, Function.support, h]
  rw [heq]
  exact hfinite

private theorem finite_support_measure_zero :
    fairProduct finiteSupport = 0 := by
  have hlimsup : fairProduct (limsup activationEvent atTop) = 1 :=
    measure_limsup_eq_one (fun n => activation_event_measurable n)
      activation_events_independent activation_measure_tsum_top
  have hlimsupMeasurable : MeasurableSet (limsup activationEvent atTop) :=
    MeasurableSet.measurableSet_limsup (fun n => activation_event_measurable n)
  apply measure_mono_null
  · intro x hfinite
    exact Set.mem_compl (finite_support_disjoint_limsup x hfinite)
  · exact (prob_compl_eq_zero_iff hlimsupMeasurable).2 hlimsup

private theorem readout_mem_finiteSupport (A : Finset Nat) :
    readout A ∈ finiteSupport := by
  change (Function.support (readout A)).Finite
  have hsupport : Function.support (readout A) = (A : Set Nat) := by
    ext n
    by_cases h : n ∈ A <;> simp [readout, Function.support, h]
  rw [hsupport]
  exact A.finite_toSet

/- A countable image is measurable in this countable-coordinate measurable space. -/
theorem readout_image_measurable :
    MeasurableSet (Set.range readout) := by
  exact (Set.countable_range readout).measurableSet

#print axioms readout_image_measurable

theorem finite_marginal_family_probability :
    ∀ J : Finset Nat, IsProbabilityMeasure (finiteMarginal J) := by
  intro J
  infer_instance

#print axioms finite_marginal_family_probability

theorem finite_marginal_family_compatible :
    ∀ J : Finset Nat,
      Measure.map J.restrict fairProduct = finiteMarginal J := by
  intro J
  exact Measure.infinitePi_map_restrict _

#print axioms finite_marginal_family_compatible

theorem readout_image_null :
    fairProduct (Set.range readout) = 0 := by
  apply measure_mono_null
  · intro x hx
    rcases hx with ⟨A, rfl⟩
    exact readout_mem_finiteSupport A
  · exact finite_support_measure_zero

#print axioms readout_image_null

def identityReadout : (Nat -> Bool) -> Nat -> Bool := id

theorem identity_readout_image_full :
    fairProduct (Set.range identityReadout) = 1 := by
  simpa [identityReadout] using
    (show fairProduct (Set.range (id : (Nat -> Bool) -> Nat -> Bool)) = 1 by
      rw [Set.range_eq_univ.2 Function.surjective_id, measure_univ])

#print axioms identity_readout_image_full

def constantReadout : PUnit -> Nat -> Bool := fun _ _ => false

theorem constant_readout_image_null :
    fairProduct (Set.range constantReadout) = 0 := by
  have hsubset : Set.range constantReadout ⊆ finiteSupport := by
    rintro x ⟨u, rfl⟩
    change (Function.support (constantReadout u)).Finite
    simp [constantReadout, Function.support]
  exact measure_mono_null hsubset finite_support_measure_zero

#print axioms constant_readout_image_null

theorem surjective_readout_has_full_image
    {X O : Type} [MeasurableSpace O] (nu : Measure O)
    (q : X -> O) (hq : Function.Surjective q) :
    nu (Set.range q) = nu Set.univ := by
  rw [Set.range_eq_univ.2 hq]

#print axioms surjective_readout_has_full_image

def finiteReadout (J : Finset Nat) : Finset J -> (J -> Bool) :=
  fun A j => decide (j ∈ A)

theorem finite_readout_surjective (J : Finset Nat) :
    Function.Surjective (finiteReadout J) := by
  intro x
  let A : Finset J := Finset.univ.filter (fun j => x j = true)
  refine ⟨A, ?_⟩
  funext j
  simp [finiteReadout, A]

#print axioms finite_readout_surjective

theorem finite_index_readout_image_full (J : Finset Nat) :
    finiteMarginal J (Set.range (finiteReadout J)) = 1 := by
  rw [Set.range_eq_univ.2 (finite_readout_surjective J), measure_univ]

#print axioms finite_index_readout_image_full

theorem empty_domain_readout_image_empty {O : Type} (q : Empty -> O) :
    Set.range q = ∅ := by
  exact Set.range_eq_empty_iff.2 inferInstance

#print axioms empty_domain_readout_image_empty

theorem singleton_domain_readout_image_singleton {O : Type} (q : PUnit -> O) :
    Set.range q = {q PUnit.unit} := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    cases u
    rfl
  · intro hy
    refine ⟨PUnit.unit, ?_⟩
    simpa using hy.symm

#print axioms singleton_domain_readout_image_singleton

/- The counterexample and the positive comparison are stated together. -/
theorem fpod_principle_120_1 :
    (∀ J : Finset Nat, IsProbabilityMeasure (finiteMarginal J)) ∧
      (∀ J : Finset Nat,
        Measure.map J.restrict fairProduct = finiteMarginal J) ∧
      MeasurableSet (Set.range readout) ∧
      fairProduct (Set.range readout) = 0 ∧
      fairProduct (Set.range identityReadout) = 1 := by
  refine ⟨finite_marginal_family_probability,
    finite_marginal_family_compatible, readout_image_measurable,
    readout_image_null, identity_readout_image_full⟩

#print axioms fpod_principle_120_1

end D5.S3.Observer.ProbabilisticClosure.FiniteMarginalGlobalReadoutContrast
