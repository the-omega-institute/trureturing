/- GID: D5/S3/Observer/ProductMeasures/FinitePmfLikelihood
   generality: G
   mirror-B: D5/B/S3/Observer/ProductMeasures/FinitePmfLikelihood
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite PMF products are absolutely continuous when Hellinger energy is summable. -/
/- Library-search audit trail (2026-08-25): Pinned Mathlib searches for Kakutani,
   Hellinger product measures, infinite-product absolute continuity, and likelihood
   ratios found no product dichotomy. The proof reuses `Measure.eq_infinitePi`,
   `PMF.integral_eq_sum`, Lp completeness, and with-density absolute continuity. -/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProductMeasure
import D5.S3.TotalVariation.Hellinger

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory Topology

noncomputable section

namespace D5.S3.Observer.ProductMeasures.FinitePmfLikelihood

universe u

local instance factOneLeTwo : Fact (1 ≤ (2 : ENNReal)) :=
  fact_one_le_two_ennreal

local instance factOneLeOne : Fact (1 ≤ (1 : ENNReal)) :=
  fact_one_le_one_ennreal

private lemma norm_toLp_two_sq {A : Type*} [MeasurableSpace A]
    {mu : Measure A} (f : A -> Real) (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂mu := by
  rw [Lp.norm_toLp,
    hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num [Real.norm_eq_abs, sq_abs]
  have hnonneg : 0 ≤ ∫ x, f x ^ 2 ∂mu := integral_nonneg fun _ => sq_nonneg _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
  convert Real.rpow_inv_natCast_pow hnonneg (by norm_num : (2 : Nat) ≠ 0) using 1
  all_goals norm_num

variable {Output : Nat -> Type u}
  [∀ i, MeasurableSpace (Output i)]
  [∀ i, MeasurableSingletonClass (Output i)]
  [∀ i, Fintype (Output i)]

variable {i : Nat}

/-- The real-valued mass function associated with a finite probability mass function. -/
def pmfRealMass (p : PMF (Output i)) (o : Output i) : Real :=
  (p o).toReal

/-- The square-root likelihood ratio, totalized to zero when the denominator vanishes. -/
def rootLikelihood (p q : PMF (Output i)) (o : Output i) : Real :=
  Real.sqrt (pmfRealMass p o) / Real.sqrt (pmfRealMass q o)

/-- The Bhattacharyya affinity of two finite probability mass functions. -/
def affinity (p q : PMF (Output i)) : Real :=
  D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
    (pmfRealMass p) (pmfRealMass q)

/-- The squared Hellinger energy, with the repository convention `H² = 2 * (1 - ρ)`. -/
def energy (p q : PMF (Output i)) : Real :=
  D5.S3.TotalVariation.Hellinger.hellingerSq
    (pmfRealMass p) (pmfRealMass q)

/-- The product of square-root likelihood ratios over the first `n` coordinates. -/
def prefixRootLikelihood (p q : (i : Nat) -> PMF (Output i))
    (n : Nat) (x : (i : Nat) -> Output i) : Real :=
  ∏ i ∈ Finset.range n, rootLikelihood (p i) (q i) (x i)

/-- The product of coordinate affinities on the half-open interval `[m, n)`. -/
def tailAffinity (p q : (i : Nat) -> PMF (Output i))
    (m n : Nat) : Real :=
  ∏ i ∈ Finset.Ico m n, affinity (p i) (q i)

/-- The countable product measure determined by finite coordinate laws. -/
def productLaw (p : (i : Nat) -> PMF (Output i)) :
    Measure ((i : Nat) -> Output i) :=
  Measure.infinitePi fun i => (p i).toMeasure

omit [∀ i, MeasurableSpace (Output i)]
    [∀ i, MeasurableSingletonClass (Output i)] [∀ i, Fintype (Output i)] in
/-- Real PMF masses are nonnegative. -/
lemma pmfRealMass_nonneg (p : PMF (Output i)) (o : Output i) :
    0 <= pmfRealMass p o := by
  exact ENNReal.toReal_nonneg

#print axioms pmfRealMass_nonneg

omit [∀ i, MeasurableSpace (Output i)]
    [∀ i, MeasurableSingletonClass (Output i)] [∀ i, Fintype (Output i)] in
private lemma pmfRealMass_sum [Fintype (Output i)] (p : PMF (Output i)) :
    ∑ o, pmfRealMass p o = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rw [tsum_fintype] at h
  change (∑ o, (p o).toReal) = 1
  rw [← ENNReal.toReal_sum (s := Finset.univ)
    (fun o _ => PMF.apply_ne_top p o)]
  simpa using h

omit [∀ i, Fintype (Output i)] in
/-- Locally equivalent PMFs have exactly the same zero-mass points. -/
lemma mass_zero_iff_of_ac
    {p q : PMF (Output i)}
    (hpq : p.toMeasure ≪ q.toMeasure)
    (hqp : q.toMeasure ≪ p.toMeasure) (o : Output i) :
    pmfRealMass p o = 0 ↔ pmfRealMass q o = 0 := by
  rw [pmfRealMass, pmfRealMass, ENNReal.toReal_eq_zero_iff,
    ENNReal.toReal_eq_zero_iff]
  simp only [PMF.apply_ne_top, or_false]
  constructor
  · intro hp
    have hp' : p.toMeasure ({o} : Set (Output i)) = 0 := by
      simpa [PMF.toMeasure_apply_singleton] using hp
    have hq' := hqp hp'
    simpa [PMF.toMeasure_apply_singleton] using hq'
  · intro hq
    have hq' : q.toMeasure ({o} : Set (Output i)) = 0 := by
      simpa [PMF.toMeasure_apply_singleton] using hq
    have hp' := hpq hq'
    simpa [PMF.toMeasure_apply_singleton] using hp'

#print axioms mass_zero_iff_of_ac

omit [∀ i, Fintype (Output i)] in
private lemma rootLikelihood_sq_weight
    {p q : PMF (Output i)}
    (hpq : p.toMeasure ≪ q.toMeasure)
    (hqp : q.toMeasure ≪ p.toMeasure) (o : Output i) :
    pmfRealMass q o * rootLikelihood p q o ^ 2 = pmfRealMass p o := by
  by_cases hq : pmfRealMass q o = 0
  · have hp := (mass_zero_iff_of_ac hpq hqp o).2 hq
    simp [rootLikelihood, hq, hp]
  · have hqpos : 0 < pmfRealMass q o :=
      lt_of_le_of_ne (pmfRealMass_nonneg q o) (Ne.symm hq)
    rw [rootLikelihood, div_pow]
    rw [Real.sq_sqrt (pmfRealMass_nonneg p o),
      Real.sq_sqrt (pmfRealMass_nonneg q o)]
    field_simp

omit [∀ i, Fintype (Output i)] in
private lemma rootLikelihood_weight
    {p q : PMF (Output i)}
    (hpq : p.toMeasure ≪ q.toMeasure)
    (hqp : q.toMeasure ≪ p.toMeasure) (o : Output i) :
    pmfRealMass q o * rootLikelihood p q o =
      Real.sqrt (pmfRealMass p o * pmfRealMass q o) := by
  by_cases hq : pmfRealMass q o = 0
  · have hp := (mass_zero_iff_of_ac hpq hqp o).2 hq
    simp [rootLikelihood, hq, hp]
  · have hqpos : 0 < pmfRealMass q o :=
      lt_of_le_of_ne (pmfRealMass_nonneg q o) (Ne.symm hq)
    have hsqrtq : Real.sqrt (pmfRealMass q o) ≠ 0 :=
      (Real.sqrt_pos.2 hqpos).ne'
    calc
      pmfRealMass q o * rootLikelihood p q o =
          Real.sqrt (pmfRealMass q o) ^ 2 *
            (Real.sqrt (pmfRealMass p o) / Real.sqrt (pmfRealMass q o)) := by
        rw [rootLikelihood, Real.sq_sqrt (pmfRealMass_nonneg q o)]
      _ = Real.sqrt (pmfRealMass q o) * Real.sqrt (pmfRealMass p o) := by
        field_simp [hsqrtq]
      _ = Real.sqrt (pmfRealMass p o * pmfRealMass q o) := by
        rw [mul_comm, ← Real.sqrt_mul (pmfRealMass_nonneg p o)]

omit [∀ i, Fintype (Output i)] in
private lemma integral_rootLikelihood_sq [Finite (Output i)]
    {p q : PMF (Output i)}
    (hpq : p.toMeasure ≪ q.toMeasure)
    (hqp : q.toMeasure ≪ p.toMeasure) :
    ∫ o, rootLikelihood p q o ^ 2 ∂q.toMeasure = 1 := by
  letI : Fintype (Output i) := Fintype.ofFinite (Output i)
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  change (∑ o, pmfRealMass q o * rootLikelihood p q o ^ 2) = 1
  calc
    _ = ∑ o, pmfRealMass p o :=
      Finset.sum_congr rfl fun o _ => rootLikelihood_sq_weight hpq hqp o
    _ = 1 := pmfRealMass_sum p

private lemma integral_rootLikelihood
    {p q : PMF (Output i)}
    (hpq : p.toMeasure ≪ q.toMeasure)
    (hqp : q.toMeasure ≪ p.toMeasure) :
    ∫ o, rootLikelihood p q o ∂q.toMeasure = affinity p q := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  change (∑ o, pmfRealMass q o * rootLikelihood p q o) = affinity p q
  rw [affinity, D5.S3.TotalVariation.Bhattacharyya.bhattacharyya]
  exact Finset.sum_congr rfl fun o _ => rootLikelihood_weight hpq hqp o

omit [∀ i, Fintype (Output i)] in
private lemma setIntegral_rootLikelihood_sq [Finite (Output i)]
    {p q : PMF (Output i)}
    (hpq : p.toMeasure ≪ q.toMeasure)
    (hqp : q.toMeasure ≪ p.toMeasure)
    (s : Set (Output i)) (hs : MeasurableSet s) :
    ∫ o in s, rootLikelihood p q o ^ 2 ∂q.toMeasure =
      (p.toMeasure s).toReal := by
  letI : Fintype (Output i) := Fintype.ofFinite (Output i)
  rw [← integral_indicator hs, PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  rw [PMF.toMeasure_apply_fintype]
  have htoReal : (∑ o, s.indicator p o).toReal =
      ∑ o, (s.indicator p o).toReal := by
    rw [show (∑ o, s.indicator p o) =
        ∑ o ∈ Finset.univ, s.indicator p o by simp]
    rw [ENNReal.toReal_sum
      (fun o _ => by
        by_cases hos : o ∈ s <;> simp [hos, PMF.apply_ne_top])]
  rw [htoReal]
  apply Finset.sum_congr rfl
  intro o ho
  by_cases hos : o ∈ s
  · simp only [Set.indicator_of_mem hos]
    change pmfRealMass q o * rootLikelihood p q o ^ 2 = pmfRealMass p o
    exact rootLikelihood_sq_weight hpq hqp o
  · simp [Set.indicator_of_notMem hos]

omit [∀ i, MeasurableSpace (Output i)] [∀ i, MeasurableSingletonClass (Output i)] in
/-- Hellinger energy equals twice one minus Bhattacharyya affinity. -/
lemma energy_eq_two_mul_one_sub_affinity
    (p q : PMF (Output i)) :
    energy p q = 2 * (1 - affinity p q) := by
  apply D5.S3.TotalVariation.Hellinger.hellinger_sq_eq_two_sub
  · exact ⟨pmfRealMass_nonneg p, pmfRealMass_sum p⟩
  · exact ⟨pmfRealMass_nonneg q, pmfRealMass_sum q⟩

#print axioms energy_eq_two_mul_one_sub_affinity

omit [∀ i, MeasurableSpace (Output i)] [∀ i, MeasurableSingletonClass (Output i)] in
/-- Bhattacharyya affinity is nonnegative. -/
lemma affinity_nonneg (p q : PMF (Output i)) :
    0 ≤ affinity p q := by
  exact Finset.sum_nonneg fun o _ => Real.sqrt_nonneg _

#print axioms affinity_nonneg

omit [∀ i, MeasurableSpace (Output i)] [∀ i, MeasurableSingletonClass (Output i)] in
private lemma affinity_le_one (p q : PMF (Output i)) :
    affinity p q ≤ 1 := by
  have h : 0 ≤ energy p q := by
    rw [energy, D5.S3.TotalVariation.Hellinger.hellingerSq]
    positivity
  rw [energy_eq_two_mul_one_sub_affinity p q] at h
  exact le_of_sub_nonneg (by linarith)

omit [∀ i, Fintype (Output i)] in
private lemma prefixRootLikelihood_stronglyMeasurable [∀ i, Countable (Output i)]
    (p q : (i : Nat) -> PMF (Output i)) (n : Nat) :
    StronglyMeasurable (prefixRootLikelihood p q n) := by
  unfold prefixRootLikelihood
  apply Finset.stronglyMeasurable_fun_prod
  intro i hi
  exact (measurable_of_countable (rootLikelihood (p i) (q i))).stronglyMeasurable.comp_measurable
    (measurable_pi_apply i)

omit [∀ i, Fintype (Output i)] in
/-- Every finite-prefix square-root likelihood belongs to `L²` of the reference law. -/
lemma prefixRootLikelihood_memLp_two
    [∀ i, Finite (Output i)]
    (p q : (i : Nat) -> PMF (Output i)) (n : Nat) :
    MemLp (prefixRootLikelihood p q n) 2 (productLaw q) := by
  letI (i : Nat) : Fintype (Output i) := Fintype.ofFinite (Output i)
  letI : IsProbabilityMeasure (productLaw q) := by
    unfold productLaw
    infer_instance
  exact MemLp.of_bound
    (prefixRootLikelihood_stronglyMeasurable p q n).aestronglyMeasurable
    (∏ i ∈ Finset.range n, ∑ o, |rootLikelihood (p i) (q i) o|) <|
      .of_forall fun x => by
        rw [Real.norm_eq_abs, prefixRootLikelihood, Finset.abs_prod]
        apply Finset.prod_le_prod
        · intro i hi
          exact abs_nonneg _
        · intro i hi
          exact Finset.single_le_sum
            (fun o _ => abs_nonneg (rootLikelihood (p i) (q i) o))
            (Finset.mem_univ (x i))

#print axioms prefixRootLikelihood_memLp_two

omit [∀ i, Fintype (Output i)] in
private lemma integral_prefix_factor [∀ i, Countable (Output i)]
    (q : (i : Nat) -> PMF (Output i))
    (f : (i : Nat) -> Output i -> Real) (n : Nat) :
    ∫ x, (∏ i ∈ Finset.range n, f i (x i)) ∂productLaw q =
      ∏ i ∈ Finset.range n, ∫ o, f i o ∂(q i).toMeasure := by
  let X : (i : Fin n) -> ((j : Nat) -> Output j) -> Output i :=
    fun i x => x i
  let f' : (i : Fin n) -> Output i -> Real := fun i => f i
  have hind : iIndepFun X (productLaw q) := by
    exact (iIndepFun_infinitePi (P := fun i => (q i).toMeasure)
      (X := fun _ => id) (fun _ => measurable_id)).precomp Fin.val_injective
  have hfactor := hind.integral_fun_prod_comp
    (fun i => (measurable_pi_apply (i : Nat)).aemeasurable)
    (fun i => (measurable_of_countable (f' i)).aestronglyMeasurable)
  simp only [Finset.prod_range]
  rw [hfactor]
  apply Finset.prod_congr rfl
  intro i hi
  let hpres := measurePreserving_eval_infinitePi (fun j => (q j).toMeasure) (i : Nat)
  rw [← hpres.map_eq]
  exact (integral_map (measurable_pi_apply (i : Nat)).aemeasurable
    (measurable_of_countable (f i)).aestronglyMeasurable).symm

omit [∀ i, Fintype (Output i)] in
private lemma integral_prefixRootLikelihood_sq [∀ i, Finite (Output i)]
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure) (n : Nat) :
    ∫ x, prefixRootLikelihood p q n x ^ 2 ∂productLaw q = 1 := by
  letI (i : Nat) : Fintype (Output i) := Fintype.ofFinite (Output i)
  rw [show (fun x => prefixRootLikelihood p q n x ^ 2) =
      fun x => ∏ i ∈ Finset.range n, rootLikelihood (p i) (q i) (x i) ^ 2 by
    funext x
    rw [prefixRootLikelihood, Finset.prod_pow]]
  rw [integral_prefix_factor q
    (fun i o => rootLikelihood (p i) (q i) o ^ 2) n]
  simp_rw [integral_rootLikelihood_sq (hlocal _).1 (hlocal _).2]
  simp

/-- The expected prefix square-root likelihood is the prefix product of affinities. -/
lemma integral_prefixRootLikelihood
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure) (n : Nat) :
    ∫ x, prefixRootLikelihood p q n x ∂productLaw q =
      ∏ i ∈ Finset.range n, affinity (p i) (q i) := by
  unfold prefixRootLikelihood
  rw [integral_prefix_factor q (fun i o => rootLikelihood (p i) (q i) o) n]
  exact Finset.prod_congr rfl fun i _ =>
    integral_rootLikelihood (hlocal i).1 (hlocal i).2

#print axioms integral_prefixRootLikelihood

omit [∀ i, Fintype (Output i)] in
private lemma setIntegral_prefixRootLikelihood_sq_pi [∀ i, Finite (Output i)]
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure)
    (s : Finset Nat) (t : (i : Nat) -> Set (Output i))
    (ht : ∀ i, MeasurableSet (t i)) (n : Nat)
    (hsub : ∀ i ∈ s, i < n) :
    ∫ x in ((s : Set Nat).pi t), prefixRootLikelihood p q n x ^ 2
      ∂productLaw q =
      ∏ i ∈ s, ((p i).toMeasure (t i)).toReal := by
  letI (i : Nat) : Fintype (Output i) := Fintype.ofFinite (Output i)
  classical
  have hpi : MeasurableSet ((s : Set Nat).pi t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [← integral_indicator hpi]
  let f : (i : Nat) -> Output i -> Real := fun i o =>
    if i ∈ s then (t i).indicator
      (fun y => rootLikelihood (p i) (q i) y ^ 2) o
    else rootLikelihood (p i) (q i) o ^ 2
  rw [show (fun x => ((s : Set Nat).pi t).indicator
      (fun y => prefixRootLikelihood p q n y ^ 2) x) =
      fun x => ∏ i ∈ Finset.range n, f i (x i) by
    funext x
    by_cases hx : x ∈ (s : Set Nat).pi t
    · rw [Set.indicator_of_mem hx]
      rw [prefixRootLikelihood, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases his : i ∈ s
      · simp [f, his, Set.indicator_of_mem (hx i his)]
      · simp [f, his]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi] at hx
      push Not at hx
      obtain ⟨i, his, hit⟩ := hx
      have his' : i ∈ s := his
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr (hsub i his))]
      simp [f, his', Set.indicator_of_notMem hit]]
  rw [integral_prefix_factor q f n]
  have hfactor : ∀ i ∈ Finset.range n,
      ∫ o, f i o ∂(q i).toMeasure =
        if i ∈ s then ((p i).toMeasure (t i)).toReal else 1 := by
    intro i hi
    by_cases his : i ∈ s
    · simp only [if_pos his]
      unfold f
      simp only [if_pos his]
      rw [integral_indicator (ht i)]
      exact setIntegral_rootLikelihood_sq
        (hlocal i).1 (hlocal i).2 (t i) (ht i)
    · simp only [if_neg his]
      unfold f
      simp only [if_neg his]
      exact integral_rootLikelihood_sq (hlocal i).1 (hlocal i).2
  calc
    (∏ i ∈ Finset.range n, ∫ o, f i o ∂(q i).toMeasure) =
        ∏ i ∈ Finset.range n,
          if i ∈ s then ((p i).toMeasure (t i)).toReal else 1 :=
      Finset.prod_congr rfl hfactor
    _ = ∏ i ∈ s, ((p i).toMeasure (t i)).toReal := by
      symm
      have hprod := Finset.prod_subset
        (f := fun i => if i ∈ s then ((p i).toMeasure (t i)).toReal else 1)
        (s₁ := s) (s₂ := Finset.range n)
        (fun i hi => Finset.mem_range.mpr (hsub i hi))
        (fun i _ his => if_neg his)
      simpa using hprod

omit [∀ i, MeasurableSpace (Output i)]
    [∀ i, MeasurableSingletonClass (Output i)] [∀ i, Fintype (Output i)] in
private lemma prefix_mul_prefix_eq
    (p q : (i : Nat) -> PMF (Output i)) {m n : Nat} (hmn : m ≤ n)
    (x : (i : Nat) -> Output i) :
    prefixRootLikelihood p q m x * prefixRootLikelihood p q n x =
      ∏ i ∈ Finset.range n,
        if i < m then rootLikelihood (p i) (q i) (x i) ^ 2
        else rootLikelihood (p i) (q i) (x i) := by
  unfold prefixRootLikelihood
  rw [← Finset.prod_range_mul_prod_Ico
    (fun i => rootLikelihood (p i) (q i) (x i)) hmn]
  rw [← mul_assoc]
  rw [← Finset.prod_range_mul_prod_Ico
    (fun i => if i < m then rootLikelihood (p i) (q i) (x i) ^ 2
      else rootLikelihood (p i) (q i) (x i)) hmn]
  congr 1
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [hi, pow_two]
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_Ico] at hi
    simp [not_lt.mpr hi.1]

private lemma integral_prefix_mul_prefix
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure)
    {m n : Nat} (hmn : m ≤ n) :
    ∫ x, prefixRootLikelihood p q m x * prefixRootLikelihood p q n x
      ∂productLaw q = tailAffinity p q m n := by
  rw [show (fun x => prefixRootLikelihood p q m x *
      prefixRootLikelihood p q n x) = fun x =>
      ∏ i ∈ Finset.range n,
        if i < m then rootLikelihood (p i) (q i) (x i) ^ 2
        else rootLikelihood (p i) (q i) (x i) by
    funext x
    exact prefix_mul_prefix_eq p q hmn x]
  rw [integral_prefix_factor q (fun i o =>
    if i < m then rootLikelihood (p i) (q i) o ^ 2
    else rootLikelihood (p i) (q i) o) n]
  unfold tailAffinity
  rw [← Finset.prod_range_mul_prod_Ico
    (fun i => ∫ o, if i < m then rootLikelihood (p i) (q i) o ^ 2
      else rootLikelihood (p i) (q i) o ∂(q i).toMeasure) hmn]
  have hrange : (∏ i ∈ Finset.range m,
      ∫ o, if i < m then rootLikelihood (p i) (q i) o ^ 2
        else rootLikelihood (p i) (q i) o ∂(q i).toMeasure) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [hi, integral_rootLikelihood_sq (hlocal i).1 (hlocal i).2]
  rw [hrange, one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.mem_Ico] at hi
  simp [not_lt.mpr hi.1,
    integral_rootLikelihood (hlocal i).1 (hlocal i).2]

private lemma one_sub_prod_le_sum_one_sub {A : Type*}
    (s : Finset A) (a : A -> Real)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      have hi0 : 0 ≤ a i := ha0 i (Finset.mem_insert_self i s)
      have hi1 : a i ≤ 1 := ha1 i (Finset.mem_insert_self i s)
      have hs0 : 0 ≤ ∏ j ∈ s, a j := Finset.prod_nonneg fun j hj =>
        ha0 j (Finset.mem_insert_of_mem hj)
      have hs1 : ∏ j ∈ s, a j ≤ 1 := Finset.prod_le_one
        (fun j hj => ha0 j (Finset.mem_insert_of_mem hj))
        (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
      have hih := ih
        (fun j hj => ha0 j (Finset.mem_insert_of_mem hj))
        (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
      nlinarith

private lemma integral_prefix_sub_sq
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure)
    {m n : Nat} (hmn : m ≤ n) :
    ∫ x, (prefixRootLikelihood p q m x -
      prefixRootLikelihood p q n x) ^ 2 ∂productLaw q =
      2 * (1 - tailAffinity p q m n) := by
  letI : IsProbabilityMeasure (productLaw q) := by
    unfold productLaw
    infer_instance
  let hm := prefixRootLikelihood_memLp_two p q m
  let hn := prefixRootLikelihood_memLp_two p q n
  have hmsq := hm.integrable_sq
  have hnsq := hn.integrable_sq
  have hcross : Integrable (fun x => prefixRootLikelihood p q m x *
      prefixRootLikelihood p q n x) (productLaw q) := by
    change Integrable
      (prefixRootLikelihood p q m * prefixRootLikelihood p q n)
      (productLaw q)
    exact hm.integrable_mul hn
  calc
    _ = ∫ x, prefixRootLikelihood p q m x ^ 2 +
        prefixRootLikelihood p q n x ^ 2 -
        2 * (prefixRootLikelihood p q m x *
          prefixRootLikelihood p q n x) ∂productLaw q := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = (∫ x, prefixRootLikelihood p q m x ^ 2 +
        prefixRootLikelihood p q n x ^ 2 ∂productLaw q) -
        (∫ x, 2 * (prefixRootLikelihood p q m x *
          prefixRootLikelihood p q n x) ∂productLaw q) := by
      exact integral_sub (hmsq.add hnsq) (hcross.const_mul 2)
    _ = (∫ x, prefixRootLikelihood p q m x ^ 2 ∂productLaw q) +
        (∫ x, prefixRootLikelihood p q n x ^ 2 ∂productLaw q) -
        2 * (∫ x, prefixRootLikelihood p q m x *
          prefixRootLikelihood p q n x ∂productLaw q) := by
      rw [integral_add hmsq hnsq, integral_const_mul]
    _ = 2 * (1 - tailAffinity p q m n) := by
      rw [integral_prefixRootLikelihood_sq hlocal m,
        integral_prefixRootLikelihood_sq hlocal n,
        integral_prefix_mul_prefix hlocal hmn]
      ring

private lemma integral_prefix_sub_sq_le_energy_tail
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure)
    {m n : Nat} (hmn : m ≤ n) :
    ∫ x, (prefixRootLikelihood p q m x -
      prefixRootLikelihood p q n x) ^ 2 ∂productLaw q ≤
      ∑ i ∈ Finset.Ico m n, energy (p i) (q i) := by
  rw [integral_prefix_sub_sq hlocal hmn]
  have hbound := one_sub_prod_le_sum_one_sub (Finset.Ico m n)
    (fun i => affinity (p i) (q i))
    (fun i _ => affinity_nonneg (p i) (q i))
    (fun i _ => affinity_le_one (p i) (q i))
  calc
    2 * (1 - ∏ i ∈ Finset.Ico m n, affinity (p i) (q i)) ≤
        2 * ∑ i ∈ Finset.Ico m n, (1 - affinity (p i) (q i)) := by
      linarith
    _ = ∑ i ∈ Finset.Ico m n, energy (p i) (q i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ =>
        (energy_eq_two_mul_one_sub_affinity (p i) (q i)).symm

private noncomputable def prefixRootLikelihoodLp
    (p q : (i : Nat) -> PMF (Output i)) (n : Nat) :
    Lp Real 2 (productLaw q) :=
  (prefixRootLikelihood_memLp_two p q n).toLp
    (prefixRootLikelihood p q n)

private noncomputable def squareLp {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (f : Lp Real 2 mu) : Lp Real 1 mu :=
  ((ContinuousLinearMap.mul Real Real).holderL mu 2 2 1 f) f

private lemma squareLp_coe {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (f : Lp Real 2 mu) :
    squareLp mu f =ᵐ[mu] fun x => f x ^ 2 := by
  simpa [squareLp, pow_two] using
    (ContinuousLinearMap.coeFn_holder
      (ContinuousLinearMap.mul Real Real) f f)

private lemma continuous_squareLp {A : Type*} [MeasurableSpace A]
    (mu : Measure A) : Continuous (squareLp mu) := by
  unfold squareLp
  fun_prop

private lemma prefixRootLikelihood_cauchy
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure)
    (hsum : Summable fun i => energy (p i) (q i)) :
    CauchySeq (fun n : Nat => prefixRootLikelihoodLp p q n) := by
  let partialSum : Nat -> Real := fun n =>
    ∑ i ∈ Finset.range n, energy (p i) (q i)
  have hpartial : Tendsto partialSum atTop
      (𝓝 (∑' i, energy (p i) (q i))) := by
    exact hsum.hasSum.tendsto_sum_nat
  have hcpartial : CauchySeq partialSum := hpartial.cauchySeq
  rw [Metric.cauchySeq_iff']
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.1 hcpartial)
    (epsilon ^ 2) (sq_pos_of_pos hepsilon)
  refine ⟨N, fun n hn => ?_⟩
  have htail : ∑ i ∈ Finset.Ico N n, energy (p i) (q i) < epsilon ^ 2 := by
    rw [Finset.sum_Ico_eq_sub _ hn]
    exact (le_abs_self _).trans_lt
      (by simpa [partialSum, Real.dist_eq] using hN n hn)
  rw [dist_comm, dist_eq_norm]
  let hNmem := prefixRootLikelihood_memLp_two p q N
  let hnmem := prefixRootLikelihood_memLp_two p q n
  change ‖hNmem.toLp (prefixRootLikelihood p q N) -
    hnmem.toLp (prefixRootLikelihood p q n)‖ < epsilon
  rw [← hNmem.toLp_sub hnmem]
  have hnormsq := norm_toLp_two_sq
    (fun x => prefixRootLikelihood p q N x - prefixRootLikelihood p q n x)
    (hNmem.sub hnmem)
  have hintegral := integral_prefix_sub_sq_le_energy_tail hlocal hn
  have hnorm_nonneg : 0 ≤ ‖(hNmem.sub hnmem).toLp
      (fun x => prefixRootLikelihood p q N x -
        prefixRootLikelihood p q n x)‖ := norm_nonneg _
  apply (sq_lt_sq₀ hnorm_nonneg hepsilon.le).1
  exact hnormsq.trans_lt (hintegral.trans_lt htail)

/-- Summable coordinate Hellinger energy gives absolute continuity of product laws. -/
theorem productLaw_ac_of_summable
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure)
    (hsum : Summable fun i => energy (p i) (q i)) :
    productLaw p ≪ productLaw q := by
  let Q := productLaw q
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete
    (prefixRootLikelihood_cauchy hlocal hsum)
  have hsquare : Tendsto
      (fun n => squareLp Q (prefixRootLikelihoodLp p q n)) atTop
      (𝓝 (squareLp Q G)) :=
    ((continuous_squareLp Q).tendsto G).comp hG
  have hsquare' : Tendsto
      (fun n => squareLp Q (prefixRootLikelihoodLp p q n)) atTop
      (𝓝 ((Lp.memLp (squareLp Q G)).toLp (squareLp Q G))) := by
    simpa only [Lp.toLp_coeFn] using hsquare
  have hnormCoe : Tendsto (fun n => eLpNorm
      (fun x => squareLp Q (prefixRootLikelihoodLp p q n) x -
        squareLp Q G x) 1 Q)
      atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm
      (fun n => squareLp Q (prefixRootLikelihoodLp p q n))
      (squareLp Q G) (Lp.memLp (squareLp Q G))).1 hsquare'
  let g2 : ((i : Nat) -> Output i) -> Real := fun x => G x ^ 2
  have hg2int : Integrable g2 Q := by
    exact (Lp.memLp G).integrable_sq
  have hnorm : Tendsto (fun n => eLpNorm
      (fun x => prefixRootLikelihood p q n x ^ 2 - g2 x) 1 Q)
      atTop (𝓝 0) := by
    apply hnormCoe.congr'
    filter_upwards [] with n
    apply eLpNorm_congr_ae
    filter_upwards [squareLp_coe Q (prefixRootLikelihoodLp p q n),
      squareLp_coe Q G,
      (prefixRootLikelihood_memLp_two p q n).coeFn_toLp] with x hsqn hsqG hprefix
    change prefixRootLikelihoodLp p q n x =
      prefixRootLikelihood p q n x at hprefix
    rw [hsqn, hsqG, hprefix]
  have hsetIntegral (s : Set ((i : Nat) -> Output i)) :
      Tendsto (fun n => ∫ x in s, prefixRootLikelihood p q n x ^ 2 ∂Q)
        atTop (𝓝 (∫ x in s, g2 x ∂Q)) := by
    exact tendsto_setIntegral_of_L1' g2 hg2int.1
      (.of_forall fun n => (prefixRootLikelihood_memLp_two p q n).integrable_sq)
      hnorm s
  let density : ((i : Nat) -> Output i) -> ENNReal := fun x => ENNReal.ofReal (g2 x)
  have hdensity : Q.withDensity density = productLaw p := by
    apply Measure.eq_infinitePi (fun i => (p i).toMeasure)
    intro s t ht
    have hpi : MeasurableSet ((s : Set Nat).pi t) :=
      MeasurableSet.pi s.countable_toSet fun i _ => ht i
    let n0 : Nat := ∑ i ∈ s, (i + 1)
    have hsub : ∀ i ∈ s, i < n0 := by
      intro i hi
      have hle : i + 1 ≤ n0 := by
        exact Finset.single_le_sum (fun j _ => Nat.zero_le (j + 1)) hi
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hle
    have heventual : ∀ n ≥ n0,
        ∫ x in ((s : Set Nat).pi t), prefixRootLikelihood p q n x ^ 2 ∂Q =
          ∏ i ∈ s, ((p i).toMeasure (t i)).toReal := by
      intro n hn
      exact setIntegral_prefixRootLikelihood_sq_pi hlocal s t ht n
        (fun i hi => lt_of_lt_of_le (hsub i hi) hn)
    have hlimit : ∫ x in ((s : Set Nat).pi t), g2 x ∂Q =
        ∏ i ∈ s, ((p i).toMeasure (t i)).toReal := by
      apply tendsto_nhds_unique (hsetIntegral ((s : Set Nat).pi t))
      exact tendsto_atTop_of_eventually_const heventual
    rw [withDensity_apply density hpi]
    change (∫⁻ x in ((s : Set Nat).pi t), ENNReal.ofReal (g2 x) ∂Q) = _
    rw [← ofReal_integral_eq_lintegral_ofReal
      (μ := Q.restrict ((s : Set Nat).pi t)) hg2int.integrableOn
      (.of_forall fun x => sq_nonneg (G x))]
    rw [hlimit, ← ENNReal.toReal_prod]
    exact ENNReal.ofReal_toReal <| ENNReal.prod_ne_top fun i _ =>
      measure_ne_top (p i).toMeasure (t i)
  rw [← hdensity]
  exact withDensity_absolutelyContinuous Q density

#print axioms productLaw_ac_of_summable


omit [∀ i, MeasurableSpace (Output i)]
    [∀ i, MeasurableSingletonClass (Output i)] [∀ i, Fintype (Output i)] in
private lemma prefixRootLikelihood_zero
    (p q : (i : Nat) -> PMF (Output i)) :
    prefixRootLikelihood p q 0 = 1 := by
  funext x
  simp [prefixRootLikelihood]


end D5.S3.Observer.ProductMeasures.FinitePmfLikelihood
