/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Probability.Independence.InfinitePi]
   utility: none
   digest: The normalized conditional suffix law on the actual golden biased boundary. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace
import Mathlib.Probability.Independence.InfinitePi

/-! Prepending and deleting original address coordinates under the actual product law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (H)
open BiasedBoundaryTrace (Omega M bit cylinder G J)
open MeasureTheory hiding cylinder
open ProbabilityTheory
open scoped ENNReal

/-- Delete the first n original coordinates. -/
def tail (n : ℕ) (ω : Omega) : Omega := fun i => ω (i+n)

/-- Prepend a finite original address to a ray. -/
def prepend (p : Address) (ω : Omega) : Omega :=
  fun i => if i < p.length then p.getD i false else ω (i-p.length)

/-- The actual normalized restriction, including the empty prefix. -/
def conditional (p : Address) : Measure Omega :=
  (M (cylinder p))⁻¹ • M.restrict (cylinder p)

private theorem tail_measurable (n : ℕ) : Measurable (tail n) := by
  exact measurable_pi_iff.mpr (fun i => measurable_pi_apply (i+n))

private theorem prepend_measurable (p : Address) : Measurable (prepend p) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i < p.length
  · simpa only [prepend, hi, ite_true] using (measurable_const : Measurable
      (fun _ : Omega => p.getD i false))
  · simpa only [prepend, hi, ite_false] using measurable_pi_apply (i-p.length)

private theorem prefix_event (p : Address) :
    cylinder p = (fun ω : Omega => fun i : {i : ℕ // i < p.length} => ω i.val) ⁻¹'
      {fun i : {i : ℕ // i < p.length} => p.getD i.val false} := by
  ext ω
  change (∀ i ∈ Finset.range p.length, ω i ∈ {p.getD i false}) ↔ _
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    exact h i.val (Finset.mem_range.mpr i.property)
  · intro h i hi
    exact congrFun h ⟨i, Finset.mem_range.mp hi⟩

private theorem prefix_tail_independent (p : Address) :
    IndepFun (fun ω : Omega => fun i : {i : ℕ // i < p.length} => ω i.val)
      (tail p.length) M := by
  have hI : iIndepFun (fun i : ℕ => fun ω : Omega => ω i) M :=
    iIndepFun_infinitePi (P := fun _ : ℕ => bit) (X := fun _ x => x)
      (fun _ => measurable_id)
  have hD : Disjoint {i : ℕ | i < p.length} {i : ℕ | p.length ≤ i} := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact (Nat.not_lt_of_ge hj) hi
  have h := hI.indepFun_set {i : ℕ | i < p.length} {i : ℕ | p.length ≤ i}
    hD (fun i => measurable_pi_apply i)
  have hR : Measurable (fun f : ({i : ℕ // p.length ≤ i} → Bool) =>
      fun j : ℕ => f ⟨j+p.length, Nat.le_add_left _ _⟩) := by fun_prop
  exact h.comp measurable_id hR

private theorem tail_law (n : ℕ) : M.map (tail n) = M := by
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => bit)
    (show Function.Injective (fun i : ℕ => i+n) from fun _ _ h => Nat.add_right_cancel h)

private theorem restricted_tail_law (p : Address) :
    (M.restrict (cylinder p)).map (tail p.length) = M (cylinder p) • M := by
  ext s hs
  rw [Measure.map_apply (tail_measurable _) hs,
    Measure.restrict_apply ((tail_measurable _) hs),
    Measure.smul_apply, smul_eq_mul]
  have h := (prefix_tail_independent p).measure_inter_preimage_eq_mul
    {fun i : {i : ℕ // i < p.length} => p.getD i.val false} s
    (measurableSet_singleton _) hs
  rw [← prefix_event] at h
  have ht := congrArg (fun μ : Measure Omega => μ s) (tail_law p.length)
  rw [Measure.map_apply (tail_measurable _) hs] at ht
  rw [Set.inter_comm, h, ht]

private theorem prepend_tail (p : Address) (ω : Omega) (hω : ω ∈ cylinder p) :
    prepend p (tail p.length ω) = ω := by
  funext i
  by_cases hi : i < p.length
  · have h := hω i (Finset.mem_range.mpr hi)
    simpa only [prepend, hi, ite_true] using h.symm
  · have he : i-p.length+p.length = i := by omega
    simp only [prepend, hi, ite_false, tail, he]

private theorem prepend_unnormalized (p : Address) :
    M (cylinder p) • M.map (prepend p) = M.restrict (cylinder p) := by
  calc
    _ = (M (cylinder p) • M).map (prepend p) :=
      (Measure.map_smul _ (prepend_measurable p).aemeasurable).symm
    _ = ((M.restrict (cylinder p)).map (tail p.length)).map (prepend p) := by
      rw [restricted_tail_law]
    _ = (M.restrict (cylinder p)).map (prepend p ∘ tail p.length) :=
      Measure.map_map (prepend_measurable p) (tail_measurable _)
    _ = (M.restrict (cylinder p)).map id := by
      apply Measure.map_congr
      apply ae_restrict_of_forall_mem
      · rw [prefix_event]
        exact (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val))
          (measurableSet_singleton _)
      · exact fun ω hω => prepend_tail p ω hω
    _ = _ := Measure.map_id

private theorem cylinder_nonzero (p : Address) : M (cylinder p) ≠ 0 := by
  classical
  have ha : 0 < FiniteSourceMass.a := inv_pos.mpr Real.goldenRatio_pos
  have ha1 : FiniteSourceMass.a < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hbit (c : Bool) : bit {c} ≠ 0 := by
    unfold bit
    cases c
    · rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem _
        (measurableSet_singleton false) (by simp) (by simp)]
      apply ENNReal.coe_ne_zero.mpr
      exact_mod_cast ha.ne'
    · rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem _
        (measurableSet_singleton true) (by simp) (by simp)]
      apply ENNReal.coe_ne_zero.mpr
      exact_mod_cast (sub_pos.mpr ha1).ne'
  rw [M, cylinder, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hbit _)

/-- Deleting the prefix has the original suffix law under the actual restriction;
prepending pushes the original law to the normalized restricted measure. -/
private theorem prepend_conditional_law :
    (∀ p : Address, (M.restrict (cylinder p)).map (tail p.length) = M (cylinder p) • M) ∧
    (∀ p : Address, MeasurePreserving (prepend p) M (conditional p)) ∧
    conditional [] = M := by
  refine ⟨restricted_tail_law, ?_, ?_⟩
  · intro p
    refine ⟨prepend_measurable p, ?_⟩
    change M.map (prepend p) = (M (cylinder p))⁻¹ • M.restrict (cylinder p)
    rw [← prepend_unnormalized, smul_smul,
      ENNReal.inv_mul_cancel (cylinder_nonzero p) (measure_ne_top M _), one_smul]
  · simp [conditional, cylinder]

private theorem conditional_le (p : Address) :
    conditional p ≤ (M (cylinder p))⁻¹ • M := by
  exact smul_le_smul_left (M (cylinder p))⁻¹ Measure.restrict_le_self

private theorem conditional_memLp (p : Address) (F : G) : MemLp F 2 (conditional p) :=
  (Lp.memLp F).of_measure_le_smul (by simp [cylinder_nonzero]) (conditional_le p)

private theorem prepend_quasi (p : Address) : QuasiMeasurePreserving (prepend p) M M := by
  refine ⟨prepend_measurable p, ?_⟩
  rw [(prepend_conditional_law.2.1 p).map_eq]
  exact Measure.absolutelyContinuous_of_le_smul (conditional_le p)

private theorem pullback_memLp (p : Address) (F : G) : MemLp (F ∘ prepend p) 2 M :=
  (conditional_memLp p F).comp_measurePreserving (prepend_conditional_law.2.1 p)

private def pullbackLinear (p : Address) : G →ₗ[ℝ] G where
  toFun F := (pullback_memLp p F).toLp (F ∘ prepend p)
  map_add' F K := by
    apply Lp.ext
    filter_upwards [(pullback_memLp p (F+K)).coeFn_toLp,
      Lp.coeFn_add ((pullback_memLp p F).toLp _) ((pullback_memLp p K).toLp _),
      (pullback_memLp p F).coeFn_toLp, (pullback_memLp p K).coeFn_toLp,
      (prepend_quasi p).ae_eq_comp (Lp.coeFn_add F K)] with ω h1 h2 h3 h4 h5
    exact h1.trans (h5.trans (by simpa only [Pi.add_apply, Function.comp_apply, h3, h4] using h2.symm))
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(pullback_memLp p (c • F)).coeFn_toLp,
      Lp.coeFn_smul c ((pullback_memLp p F).toLp _),
      (pullback_memLp p F).coeFn_toLp,
      (prepend_quasi p).ae_eq_comp (Lp.coeFn_smul c F)] with ω h1 h2 h3 h4
    exact h1.trans (h4.trans (by simpa only [Pi.smul_apply, Function.comp_apply,
      RingHom.id_apply, h3] using h2.symm))

/-- The exact measure-scaling bound for conditional restriction. -/
def pullbackBound (p : Address) : ℝ :=
  ((M (cylinder p))⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal).toReal

private theorem pullback_norm (p : Address) (F : G) :
    ‖pullbackLinear p F‖ ≤ pullbackBound p * ‖F‖ := by
  have hc : (M (cylinder p))⁻¹ ≠ ⊤ := by simp [cylinder_nonzero]
  have hb := eLpNorm_le_of_measure_le_smul (f := (F : Omega → ℝ)) (p := 2) (conditional_le p)
  rw [← eLpNorm_comp_measurePreserving (conditional_memLp p F).aestronglyMeasurable
    (prepend_conditional_law.2.1 p)] at hb
  have ht : (M (cylinder p))⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm F 2 M ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hc)
      (Lp.memLp F).eLpNorm_ne_top
  have hm := ENNReal.toReal_mono ht hb
  change ‖(pullback_memLp p F).toLp (F ∘ prepend p)‖ ≤ _
  rw [Lp.norm_toLp]
  simpa only [pullbackBound, ENNReal.toReal_mul, ← Lp.norm_def] using hm

/-- Conditional composition is bounded into the original ambient L2 space. -/
def pullback (p : Address) : G →L[ℝ] G :=
  (pullbackLinear p).mkContinuous (pullbackBound p) (pullback_norm p)

/-- The actual joined infinite boundary trace pulled back to suffix rays. -/
def conditionalTrace (p : Address) : H →L[ℝ] G := (pullback p).comp J

/-- The actual conditional law and its all-L2 composition, including empty prefixes. -/
theorem conditional_pullback_law :
    (∀ p : Address, M (cylinder p) ≠ 0) ∧
    (∀ p : Address, (M.restrict (cylinder p)).map (tail p.length) = M (cylinder p) • M) ∧
    (∀ p : Address, MeasurePreserving (prepend p) M (conditional p)) ∧
    conditional [] = M ∧
    (∀ (p : Address) (F : G), pullback p F =ᵐ[M] F ∘ prepend p) ∧
    (∀ (p : Address) (F : G), ‖pullback p F‖ ≤ pullbackBound p * ‖F‖) ∧
    (∀ (p : Address) (z : H), conditionalTrace p z =ᵐ[M] (J z) ∘ prepend p) ∧
    (∀ (p : Address) (ω : Omega), tail p.length (prepend p ω) = ω) := by
  refine ⟨cylinder_nonzero, prepend_conditional_law.1, prepend_conditional_law.2.1,
    prepend_conditional_law.2.2, fun p F => (pullback_memLp p F).coeFn_toLp,
    pullback_norm, (fun p z => (pullback_memLp p (J z)).coeFn_toLp), ?_⟩
  intro p ω
  funext i
  have hi : ¬ i+p.length < p.length := by omega
  simp only [tail, prepend, hi, ite_false, Nat.add_sub_cancel]

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw
