/- GID: D5/S3/Observer/ProductMeasures/FinitePmfDichotomy
   generality: I
   mirror-B: D5/B/S3/Observer/ProductMeasures/FinitePmfDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Locally equivalent finite PMFs satisfy the full product-law Kakutani dichotomy. -/
/- Library-search audit trail (2026-08-25): Mathlib name and type-shape searches found
   only Riesz--Markov--Kakutani results, not a Hellinger infinite-product dichotomy.
   The repository hit `SignalKakutaniDichotomy` packages the desired conclusion as a
   premise; this module proves that exact package for finite PMF coordinates. -/

import D5.S3.Observer.ProductMeasures.FinitePmfLikelihood
import D5.S3.Observer.MeasureSeparation.WeakPrimeSignalCompletionThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory Topology

noncomputable section

namespace D5.S3.Observer.ProductMeasures.FinitePmfDichotomy

open D5.S3.Observer.ProductMeasures.FinitePmfLikelihood

universe u

variable {Output : Nat -> Type u}
  [∀ i, MeasurableSpace (Output i)]
  [∀ i, MeasurableSingletonClass (Output i)]
  [∀ i, Fintype (Output i)]

variable {i : Nat}

omit [∀ i, MeasurableSpace (Output i)] [∀ i, MeasurableSingletonClass (Output i)] in
private lemma energy_nonneg (p q : PMF (Output i)) :
    0 <= energy p q := by
  rw [energy, D5.S3.TotalVariation.Hellinger.hellingerSq]
  exact Finset.sum_nonneg fun o _ => sq_nonneg _

omit [∀ i, MeasurableSpace (Output i)] [∀ i, MeasurableSingletonClass (Output i)] in
private lemma affinity_le_exp_neg_half_energy (p q : PMF (Output i)) :
    affinity p q <= Real.exp (-(energy p q / 2)) := by
  have hexp := Real.add_one_le_exp (-(energy p q / 2))
  calc
    affinity p q = -(energy p q / 2) + 1 := by
      rw [energy_eq_two_mul_one_sub_affinity p q]
      ring
    _ <= Real.exp (-(energy p q / 2)) := hexp

omit [∀ i, MeasurableSpace (Output i)] [∀ i, MeasurableSingletonClass (Output i)] in
private lemma prefix_affinity_le_exp_neg_half_sum
    (p q : (i : Nat) -> PMF (Output i)) (n : Nat) :
    (∏ i ∈ Finset.range n, affinity (p i) (q i)) <=
      Real.exp (-(1 / 2 : Real) *
        ∑ i ∈ Finset.range n, energy (p i) (q i)) := by
  calc
    (∏ i ∈ Finset.range n, affinity (p i) (q i)) <=
        ∏ i ∈ Finset.range n, Real.exp (-(energy (p i) (q i) / 2)) :=
      Finset.prod_le_prod
        (fun i _ => affinity_nonneg (p i) (q i))
        (fun i _ => affinity_le_exp_neg_half_energy (p i) (q i))
    _ = Real.exp (-(1 / 2 : Real) *
        ∑ i ∈ Finset.range n, energy (p i) (q i)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

omit [∀ i, MeasurableSpace (Output i)] [∀ i, MeasurableSingletonClass (Output i)] in
private lemma prefix_affinity_tendsto_zero
    {p q : (i : Nat) -> PMF (Output i)}
    (hdiv : ¬Summable fun i => energy (p i) (q i)) :
    Tendsto (fun n => ∏ i ∈ Finset.range n, affinity (p i) (q i))
      atTop (nhds 0) := by
  let partialSum : Nat -> Real := fun n =>
    ∑ i ∈ Finset.range n, energy (p i) (q i)
  have hpartial : Tendsto partialSum atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun i => energy_nonneg (p i) (q i))).mp hdiv
  have hhalf : Tendsto (fun n => (1 / 2 : Real) * partialSum n)
      atTop atTop := hpartial.const_mul_atTop (by norm_num)
  have hneg : Tendsto (fun n => -((1 / 2 : Real) * partialSum n))
      atTop atBot := tendsto_neg_atBot_iff.mpr hhalf
  have hexp : Tendsto
      (fun n => Real.exp (-((1 / 2 : Real) * partialSum n)))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hneg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hexp
  · exact .of_forall fun n => Finset.prod_nonneg fun i _ =>
      affinity_nonneg (p i) (q i)
  · exact .of_forall fun n => by
      simpa [partialSum] using prefix_affinity_le_exp_neg_half_sum p q n

omit [∀ i, MeasurableSpace (Output i)] [∀ i, MeasurableSingletonClass (Output i)] in
private lemma affinity_comm (p q : PMF (Output i)) :
    affinity p q = affinity q p := by
  rw [affinity, affinity,
    D5.S3.TotalVariation.Bhattacharyya.bhattacharyya,
    D5.S3.TotalVariation.Bhattacharyya.bhattacharyya]
  apply Finset.sum_congr rfl
  intro o ho
  rw [mul_comm]

omit [∀ i, MeasurableSpace (Output i)]
    [∀ i, MeasurableSingletonClass (Output i)] [∀ i, Fintype (Output i)] in
private lemma rootLikelihood_nonneg
    (p q : PMF (Output i)) (o : Output i) :
    0 <= rootLikelihood p q o := by
  exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

omit [∀ i, MeasurableSpace (Output i)]
    [∀ i, MeasurableSingletonClass (Output i)] [∀ i, Fintype (Output i)] in
private lemma prefixRootLikelihood_nonneg
    (p q : (i : Nat) -> PMF (Output i)) (n : Nat)
    (x : (i : Nat) -> Output i) :
    0 <= prefixRootLikelihood p q n x := by
  exact Finset.prod_nonneg fun i _ => rootLikelihood_nonneg (p i) (q i) (x i)

private def zeroCoordinateSet (q : (i : Nat) -> PMF (Output i)) :
    Set ((i : Nat) -> Output i) :=
  ⋃ i, {x | pmfRealMass (q i) (x i) = 0}

omit [∀ i, Fintype (Output i)] in
private lemma pmf_measure_zero_mass_set [Finite (Output i)] (q : PMF (Output i)) :
    q.toMeasure {o | pmfRealMass q o = 0} = 0 := by
  letI : Fintype (Output i) := Fintype.ofFinite (Output i)
  rw [PMF.toMeasure_apply_fintype]
  apply Finset.sum_eq_zero
  intro o ho
  by_cases hz : pmfRealMass q o = 0
  · have hq : q o = 0 := by
      rw [pmfRealMass, ENNReal.toReal_eq_zero_iff] at hz
      exact hz.resolve_right (PMF.apply_ne_top q o)
    simp [hz, hq]
  · simp [hz]

omit [∀ i, Fintype (Output i)] in
private lemma productLaw_zeroCoordinateSet [∀ i, Finite (Output i)]
    (q : (i : Nat) -> PMF (Output i)) :
    productLaw q (zeroCoordinateSet q) = 0 := by
  apply measure_iUnion_null
  intro i
  calc
    productLaw q {x | pmfRealMass (q i) (x i) = 0} =
        (productLaw q).map (fun x => x i)
          {o | pmfRealMass (q i) o = 0} := by
      rw [Measure.map_apply (measurable_pi_apply i)
        (Set.toFinite _).measurableSet]
      congr 1
    _ = (q i).toMeasure {o | pmfRealMass (q i) o = 0} := by
      rw [productLaw, Measure.infinitePi_map_eval]
    _ = 0 := pmf_measure_zero_mass_set (q i)

omit [∀ i, MeasurableSpace (Output i)]
    [∀ i, MeasurableSingletonClass (Output i)] [∀ i, Fintype (Output i)] in
private lemma rootLikelihood_mul_reverse
    (p q : PMF (Output i)) (o : Output i)
    (hp : pmfRealMass p o ≠ 0) (hq : pmfRealMass q o ≠ 0) :
    rootLikelihood p q o * rootLikelihood q p o = 1 := by
  have hsqrtp : Real.sqrt (pmfRealMass p o) ≠ 0 := by
    exact (Real.sqrt_pos.2
      (lt_of_le_of_ne (pmfRealMass_nonneg p o) (Ne.symm hp))).ne'
  have hsqrtq : Real.sqrt (pmfRealMass q o) ≠ 0 := by
    exact (Real.sqrt_pos.2
      (lt_of_le_of_ne (pmfRealMass_nonneg q o) (Ne.symm hq))).ne'
  unfold rootLikelihood
  field_simp

omit [∀ i, Fintype (Output i)] in
private lemma prefixRootLikelihood_mul_reverse
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure)
    (n : Nat) {x : (i : Nat) -> Output i}
    (hx : x ∉ zeroCoordinateSet q) :
    prefixRootLikelihood p q n x * prefixRootLikelihood q p n x = 1 := by
  rw [prefixRootLikelihood, prefixRootLikelihood, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  have hq : pmfRealMass (q i) (x i) ≠ 0 := by
    intro hzero
    apply hx
    exact Set.mem_iUnion_of_mem i hzero
  have hp : pmfRealMass (p i) (x i) ≠ 0 := by
    exact fun hzero => hq ((mass_zero_iff_of_ac
      (hlocal i).1 (hlocal i).2 (x i)).mp hzero)
  exact rootLikelihood_mul_reverse (p i) (q i) (x i) hp hq

private lemma measure_one_le_prefixRootLikelihood
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure) (n : Nat) :
    productLaw q {x | 1 <= prefixRootLikelihood p q n x} <=
      ENNReal.ofReal
        (∏ i ∈ Finset.range n, affinity (p i) (q i)) := by
  letI : IsProbabilityMeasure (productLaw q) := by
    unfold productLaw
    infer_instance
  have hintegrable : Integrable (prefixRootLikelihood p q n) (productLaw q) :=
    (prefixRootLikelihood_memLp_two p q n).integrable (by norm_num)
  calc
    productLaw q {x | 1 <= prefixRootLikelihood p q n x} <=
        ENNReal.ofReal
          (∫ x, prefixRootLikelihood p q n x ∂productLaw q) :=
      hintegrable.measure_le_integral
        (.of_forall fun x => prefixRootLikelihood_nonneg p q n x)
        (fun x hx => hx)
    _ = ENNReal.ofReal
        (∏ i ∈ Finset.range n, affinity (p i) (q i)) := by
      rw [integral_prefixRootLikelihood hlocal n]

private lemma measure_compl_bad_union_one_le_prefix
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure) (n : Nat) :
    productLaw p
        (zeroCoordinateSet q ∪
          {x | 1 <= prefixRootLikelihood p q n x})ᶜ <=
      ENNReal.ofReal
        (∏ i ∈ Finset.range n, affinity (p i) (q i)) := by
  calc
    productLaw p
        (zeroCoordinateSet q ∪
          {x | 1 <= prefixRootLikelihood p q n x})ᶜ <=
        productLaw p {x | 1 <= prefixRootLikelihood q p n x} := by
      apply measure_mono
      intro x hx
      have hxbad : x ∉ zeroCoordinateSet q := fun h => hx (Or.inl h)
      have hxnot : ¬1 <= prefixRootLikelihood p q n x :=
        fun h => hx (Or.inr h)
      have hxlt : prefixRootLikelihood p q n x < 1 := lt_of_not_ge hxnot
      have hmul := prefixRootLikelihood_mul_reverse hlocal n hxbad
      have hpnonneg := prefixRootLikelihood_nonneg p q n x
      by_contra hqnot
      have hqlt : prefixRootLikelihood q p n x < 1 := lt_of_not_ge hqnot
      have hprodlt := mul_lt_one_of_nonneg_of_lt_one_left
        hpnonneg hxlt hqlt.le
      rw [hmul] at hprodlt
      exact (lt_irrefl 1) hprodlt
    _ <= ENNReal.ofReal
        (∏ i ∈ Finset.range n, affinity (q i) (p i)) :=
      measure_one_le_prefixRootLikelihood
        (fun i => ⟨(hlocal i).2, (hlocal i).1⟩) n
    _ = ENNReal.ofReal
        (∏ i ∈ Finset.range n, affinity (p i) (q i)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact affinity_comm (q i) (p i)

private lemma exists_geometric_subsequence {a : Nat -> Real}
    (hzero : Tendsto a atTop (nhds 0)) :
    ∃ n : Nat -> Nat, ∀ k, a (n k) ≤ (1 / 2 : Real) ^ k := by
  have hchoice : ∀ k : Nat, ∃ n : Nat, a n ≤ (1 / 2 : Real) ^ k := by
    intro k
    have hpos : 0 < (1 / 2 : Real) ^ k := pow_pos (by norm_num) k
    have heventually : ∀ᶠ n in atTop, a n < (1 / 2 : Real) ^ k :=
      (tendsto_order.1 hzero).2 _ hpos
    exact heventually.exists.imp fun _ hn => hn.le
  choose n hn using hchoice
  exact ⟨n, hn⟩

private def separatingEvent (p q : (i : Nat) -> PMF (Output i))
    (n : Nat -> Nat) (k : Nat) : Set ((i : Nat) -> Output i) :=
  zeroCoordinateSet q ∪ {x | 1 <= prefixRootLikelihood p q (n k) x}

private lemma separatingEvent_measure_q
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure)
    (n : Nat -> Nat)
    (hn : ∀ k,
      (∏ i ∈ Finset.range (n k), affinity (p i) (q i)) ≤ (1 / 2 : Real) ^ k)
    (k : Nat) :
    productLaw q (separatingEvent p q n k) <=
      (((1 / 2 : NNReal) ^ k : NNReal) : ENNReal) := by
  calc
    productLaw q (separatingEvent p q n k) <=
        productLaw q (zeroCoordinateSet q) +
          productLaw q {x | 1 <= prefixRootLikelihood p q (n k) x} :=
      measure_union_le _ _
    _ = productLaw q {x | 1 <= prefixRootLikelihood p q (n k) x} := by
      rw [productLaw_zeroCoordinateSet q, zero_add]
    _ <= ENNReal.ofReal
        (∏ i ∈ Finset.range (n k), affinity (p i) (q i)) :=
      measure_one_le_prefixRootLikelihood hlocal (n k)
    _ <= ENNReal.ofReal ((1 / 2 : Real) ^ k) := ENNReal.ofReal_le_ofReal (hn k)
    _ = (((1 / 2 : NNReal) ^ k : NNReal) : ENNReal) := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num [ENNReal.ofReal_div_of_pos]

private lemma separatingEvent_compl_measure_p
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure)
    (n : Nat -> Nat)
    (hn : ∀ k,
      (∏ i ∈ Finset.range (n k), affinity (p i) (q i)) ≤ (1 / 2 : Real) ^ k)
    (k : Nat) :
    productLaw p (separatingEvent p q n k)ᶜ <=
      (((1 / 2 : NNReal) ^ k : NNReal) : ENNReal) := by
  calc
    productLaw p (separatingEvent p q n k)ᶜ <= ENNReal.ofReal
        (∏ i ∈ Finset.range (n k), affinity (p i) (q i)) :=
      measure_compl_bad_union_one_le_prefix hlocal (n k)
    _ <= ENNReal.ofReal ((1 / 2 : Real) ^ k) := ENNReal.ofReal_le_ofReal (hn k)
    _ = (((1 / 2 : NNReal) ^ k : NNReal) : ENNReal) := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num [ENNReal.ofReal_div_of_pos]

private lemma mutuallySingular_of_geometric_compl_bounds
    {A : Type*} [MeasurableSpace A] (mu nu : Measure A)
    (s : Nat -> Set A)
    (hmu : ∀ k, mu (s k)ᶜ <= (((1 / 2 : NNReal) ^ k : NNReal) : ENNReal))
    (hnu : ∀ k, nu (s k) <= (((1 / 2 : NNReal) ^ k : NNReal) : ENNReal)) :
    mu ⟂ₘ nu := by
  have hgeom : Summable (fun k : Nat => (1 / 2 : Real) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hgeom_top : (∑' k : Nat,
      (((1 / 2 : NNReal) ^ k : NNReal) : ENNReal)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr (by simpa using hgeom)
  have hnu_zero : nu (limsup s atTop) = 0 := by
    apply measure_limsup_atTop_eq_zero
    exact ne_top_of_le_ne_top hgeom_top (ENNReal.tsum_le_tsum hnu)
  have hmu_zero : mu (limsup (fun k => (s k)ᶜ) atTop) = 0 := by
    apply measure_limsup_atTop_eq_zero
    exact ne_top_of_le_ne_top hgeom_top (ENNReal.tsum_le_tsum hmu)
  apply Measure.MutuallySingular.mk hmu_zero hnu_zero
  intro x hx
  by_cases hfrequent : ∃ᶠ k in atTop, x ∈ s k
  · exact Or.inr ((mem_limsup_iff_frequently_mem).2 hfrequent)
  · have heventual : ∀ᶠ k in atTop, x ∈ (s k)ᶜ := by
      simpa only [Set.mem_compl_iff] using (not_frequently.mp hfrequent)
    exact Or.inl ((mem_limsup_iff_frequently_mem).2 heventual.frequently)

private theorem productLaw_mutuallySingular_of_not_summable
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure)
    (hdiv : ¬Summable fun i => energy (p i) (q i)) :
    productLaw p ⟂ₘ productLaw q := by
  obtain ⟨n, hn⟩ := exists_geometric_subsequence
    (prefix_affinity_tendsto_zero (p := p) (q := q) hdiv)
  exact mutuallySingular_of_geometric_compl_bounds
    (productLaw p) (productLaw q) (separatingEvent p q n)
    (separatingEvent_compl_measure_p hlocal n hn)
    (separatingEvent_measure_q hlocal n hn)

omit [∀ i, MeasurableSpace (Output i)] [∀ i, MeasurableSingletonClass (Output i)] in
private lemma energy_comm (p q : PMF (Output i)) : energy p q = energy q p := by
  rw [energy, energy, D5.S3.TotalVariation.Hellinger.hellingerSq,
    D5.S3.TotalVariation.Hellinger.hellingerSq]
  apply Finset.sum_congr rfl
  intro o ho
  ring

private lemma probability_not_mutuallySingular_of_ac_right
    {A : Type*} [MeasurableSpace A] {mu nu : Measure A}
    [IsProbabilityMeasure nu] (hnu : nu ≪ mu) : ¬mu ⟂ₘ nu := by
  intro hsingular
  have hnull : nu hsingular.nullSet = 0 := hnu hsingular.measure_nullSet
  have hle : nu Set.univ <=
      nu hsingular.nullSet + nu hsingular.nullSetᶜ := by
    rw [← Set.union_compl_self hsingular.nullSet]
    exact measure_union_le _ _
  rw [hnull, hsingular.measure_compl_nullSet, add_zero] at hle
  simp at hle

/-- Kakutani's dichotomy for countable products of locally equivalent finite PMFs. -/
theorem finite_pmf_kakutani_dichotomy
    {p q : (i : Nat) -> PMF (Output i)}
    (hlocal : ∀ i, (p i).toMeasure ≪ (q i).toMeasure ∧
      (q i).toMeasure ≪ (p i).toMeasure) :
    D5.S3.Observer.MeasureSeparation.WeakPrimeSignalCompletionThreshold.SignalKakutaniDichotomy
        (fun i => energy (p i) (q i)) (productLaw p) (productLaw q) := by
  letI : IsProbabilityMeasure (productLaw p) := by
    unfold productLaw
    infer_instance
  letI : IsProbabilityMeasure (productLaw q) := by
    unfold productLaw
    infer_instance
  have hswap : ∀ i, (q i).toMeasure ≪ (p i).toMeasure ∧
      (p i).toMeasure ≪ (q i).toMeasure := fun i => ⟨(hlocal i).2, (hlocal i).1⟩
  constructor
  · constructor
    · intro hsingular hsum
      have hsumrev : Summable fun i => energy (q i) (p i) := by
        rw [show (fun i => energy (q i) (p i)) =
          fun i => energy (p i) (q i) by
            funext i
            exact energy_comm (q i) (p i)]
        exact hsum
      exact probability_not_mutuallySingular_of_ac_right
        (productLaw_ac_of_summable hswap hsumrev) hsingular
    · exact productLaw_mutuallySingular_of_not_summable hlocal
  · constructor
    · intro hac
      by_contra hsum
      exact probability_not_mutuallySingular_of_ac_right hac.2
        (productLaw_mutuallySingular_of_not_summable hlocal hsum)
    · intro hsum
      have hsumrev : Summable fun i => energy (q i) (p i) := by
        rw [show (fun i => energy (q i) (p i)) =
          fun i => energy (p i) (q i) by
            funext i
            exact energy_comm (q i) (p i)]
        exact hsum
      exact ⟨productLaw_ac_of_summable hlocal hsum,
        productLaw_ac_of_summable hswap hsumrev⟩

#print axioms finite_pmf_kakutani_dichotomy


end D5.S3.Observer.ProductMeasures.FinitePmfDichotomy
