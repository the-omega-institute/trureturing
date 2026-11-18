/- GID: D5/S3/ConceptDynamics/Information/ConditionalGiniDefect
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Information/ConditionalGiniDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coarsening conditional logical impurity has exact mass-weighted squared posterior defect. -/

import D5.S3.ConceptDynamics.Information.RefinementImpurityMonotonicity
import D5.S3.ConceptDynamics.Prediction.ConditionalExpectationRefinementPythagoras
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Information.ConditionalGiniDefect

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Information.ConditionalLogicalImpurity
open D5.S3.ConceptDynamics.Information.RefinementImpurityMonotonicity

noncomputable section

private theorem pmf_lintegral_eq_tsum {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (p : PMF X) (g : X → ENNReal) :
    (∫⁻ x, g x ∂p.toMeasure) = ∑' x, p x * g x := by
  classical
  have hm : p.toMeasure = Measure.sum (fun x => p x • Measure.dirac x) := by
    ext s hs
    rw [p.toMeasure_apply_eq_tsum, Measure.sum_apply _ hs]
    apply tsum_congr
    intro x
    rw [Measure.smul_apply, Measure.dirac_apply' _ hs]
    by_cases hx : x ∈ s <;> simp [hx, smul_eq_mul]
  rw [hm, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

private theorem l2_sq_eq_lintegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (g : Lp ℝ 2 μ) :
    ENNReal.ofReal (‖g‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ := by
  have hi : Integrable (fun x => g x ^ 2) μ := by
    simpa [Real.inner_apply, pow_two, mul_comm] using
      (L2.integrable_inner (𝕜 := ℝ) g g)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [pow_two]


private theorem coordinate_risk_complement {j k m : ENNReal} (h : j + k = m)
    (hm : m ≠ ⊤) :
    j * ENNReal.ofReal ((1 - (j/m).toReal)^2) +
      k * ENNReal.ofReal (((j/m).toReal)^2) + j^2/m = j := by
  by_cases hm0 : m = 0
  · have hj : j = 0 := (add_eq_zero.mp (h.trans hm0)).1
    simp [hj, hm0]
  have hj : j ≠ ⊤ := ne_top_of_le_ne_top hm (by rw [← h]; exact self_le_add_right _ _)
  have hk : k ≠ ⊤ := ne_top_of_le_ne_top hm (by rw [← h]; exact self_le_add_left _ _)
  have hd : j^2/m ≠ ⊤ := ENNReal.div_ne_top (ENNReal.pow_ne_top hj) hm0
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hj ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top hk ENNReal.ofReal_ne_top⟩, hd⟩) hj).mp
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hj ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top hk ENNReal.ofReal_ne_top⟩) hd,
    ENNReal.toReal_add (ENNReal.mul_ne_top hj ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top hk ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_div, ENNReal.toReal_pow]
  have hreal : j.toReal + k.toReal = m.toReal := by rw [← ENNReal.toReal_add hj hk, h]
  have hmR : m.toReal ≠ 0 := (ENNReal.toReal_pos hm0 hm).ne'
  have hkR : k.toReal = m.toReal - j.toReal := by linarith
  rw [hkR]
  field_simp
  ring


private theorem pmf_coordinate_risk_complement {X B A : Type*} (p : PMF X)
    (r : X → B) (t : X → A) (b : B) (a : A) :
    letI := Classical.decEq B
    letI := Classical.decEq A
    let m := ∑' x, ({x | r x = b} : Set X).indicator p x
    let j := ∑' x, ({x | r x = b ∧ t x = a} : Set X).indicator p x
    (∑' x, if r x = b then p x * ENNReal.ofReal
      (((if t x = a then 1 else 0 : ℝ) - (j/m).toReal)^2) else 0) + j^2/m = j := by
  classical
  intro m j
  let j₀ : X → ENNReal := ({x | r x = b ∧ t x = a} : Set X).indicator p
  let k₀ : X → ENNReal := ({x | r x = b ∧ t x ≠ a} : Set X).indicator p
  let k := ∑' x, k₀ x
  have hjk : j + k = m := by
    change (∑' x, j₀ x) + ∑' x, k₀ x = _
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro x
    by_cases hr : r x = b <;> by_cases ht : t x = a <;>
      simp [j₀, k₀, hr, ht, Set.indicator]
  have hm : m ≠ ⊤ := p.tsum_coe_indicator_ne_top _
  let c₁ := ENNReal.ofReal ((1 - (j/m).toReal)^2)
  let c₀ := ENNReal.ofReal (((j/m).toReal)^2)
  have hrisk :
      (∑' x, if r x = b then p x * ENNReal.ofReal
        (((if t x = a then 1 else 0 : ℝ) - (j/m).toReal)^2) else 0)
        = j * c₁ + k * c₀ := by
    change _ = (∑' x, j₀ x) * c₁ + (∑' x, k₀ x) * c₀
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    apply tsum_congr
    intro x
    by_cases hr : r x = b <;> by_cases ht : t x = a <;>
      simp [j₀, k₀, c₁, c₀, hr, ht]
  rw [hrisk]
  exact coordinate_risk_complement hjk hm


variable {X B A : Type*}
local instance : MeasurableSpace X := ⊤
local instance : MeasurableSpace B := ⊤

private theorem pmf_posterior_eq_condExp (p : PMF X) (r : X → B) (t : X → A) (a : A) :
    p.toMeasure[({x | t x = a} : Set X).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap r (⊤ : MeasurableSpace B)] =ᵐ[p.toMeasure]
    fun x => ((∑' y, ({y | r y = r x ∧ t y = a} : Set X).indicator p y) /
      (∑' y, ({y | r y = r x} : Set X).indicator p y)).toReal := by
  classical
  let v := p.toMeasure
  let s : Set X := {x | t x = a}
  let e := v.restrict s
  let q := v.map r
  let h := e.map r
  have hr : Measurable r := measurable_from_top
  have hs : MeasurableSet s := trivial
  have he : e ≪ v := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hrn := toReal_rnDeriv_map he hr
  have hind : (fun x => (e.rnDeriv v x).toReal) =ᵐ[v]
      s.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [Measure.rnDeriv_restrict_self v hs] with x hx
    change e.rnDeriv v x = s.indicator (fun _ => (1 : ℝ≥0∞)) x at hx
    rw [hx]
    by_cases hxs : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxs]
  refine ((condExp_congr_ae (m := MeasurableSpace.comap r (⊤ : MeasurableSpace B))
    hind).symm.trans hrn.symm).trans ?_
  have hsupport : ∀ᵐ x ∂v, p x ≠ 0 := by
    rw [ae_iff]
    apply (p.toMeasure_apply_eq_zero_iff (by trivial)).2
    exact Set.disjoint_left.mpr fun _ hp hzero => hzero hp
  have hq (b : B) : q {b} = ∑' y, ({y | r y = b} : Set X).indicator p y := by
    rw [Measure.map_apply hr (measurableSet_singleton b), PMF.toMeasure_apply_eq_tsum]
    rfl
  have hh (b : B) : h {b} = ∑' y, ({y | r y = b ∧ t y = a} : Set X).indicator p y := by
    rw [Measure.map_apply hr (measurableSet_singleton b),
      Measure.restrict_apply (hr (measurableSet_singleton b)), PMF.toMeasure_apply_eq_tsum]
    rfl
  filter_upwards [hsupport] with x hx
  have hq0 : q {r x} ≠ 0 := by
    intro hz
    apply hx
    apply le_antisymm _ bot_le
    rw [hq] at hz
    have hb := ENNReal.le_tsum (f := fun y => ({y | r y = r x} : Set X).indicator p y) x
    simpa [Set.indicator_of_mem (by simp : x ∈ {y | r y = r x}), hz] using hb
  have hqt : q {r x} ≠ ⊤ := measure_ne_top q _
  have hmass := Measure.setLIntegral_rnDeriv (he.map hr) ({r x} : Set B)
  change (∫⁻ y, h.rnDeriv q y ∂q.restrict {r x}) = h {r x} at hmass
  rw [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac] at hmass
  change q {r x} * h.rnDeriv q (r x) = h {r x} at hmass
  change (h.rnDeriv q (r x)).toReal = _
  rw [← hh, ← hq, ← hmass, mul_comm, ENNReal.mul_div_cancel_right hq0 hqt]


private noncomputable def posteriorReal {X B A : Type*} (p : PMF X)
    (r : Concept X B) (t : Concept X A) (b : B) (a : A) : ℝ :=
  (targetFiberMass p r t b a / conceptFiberMass p r b).toReal

private noncomputable def indicatorReal {X A : Type*} (t : X → A) (a : A) (x : X) : ℝ := by
  classical
  exact if t x = a then 1 else 0

private theorem target_mass_indicator {X B A : Type*} (p : PMF X)
    (r : Concept X B) (t : Concept X A) (b : B) (a : A) :
    (∑' y, ({y | r y = b ∧ t y = a} : Set X).indicator p y)
      = targetFiberMass p r t b a := by
  classical
  unfold targetFiberMass
  apply tsum_congr
  intro y
  by_cases hy : r y = b ∧ t y = a <;> simp [Set.indicator, hy]

private theorem impurity_eq_weighted_indicator_risk {X B A : Type*} (p : PMF X)
    (r : Concept X B) (t : Concept X A) :
    conditionalLogicalImpurity p r t =
      ∑' a, ∑' x, p x * ENNReal.ofReal
        ((indicatorReal t a x - posteriorReal p r t (r x) a)^2) := by
  classical
  let risk : A → X → ENNReal := fun a x => p x * ENNReal.ofReal
    ((indicatorReal t a x - posteriorReal p r t (r x) a)^2)
  let F : B → A → ENNReal := fun b a => ∑' x, if r x = b then risk a x else 0
  have hcoord (b : B) (a : A) :
      F b a + targetFiberMass p r t b a ^ 2 / conceptFiberMass p r b =
        targetFiberMass p r t b a := by
    have h := pmf_coordinate_risk_complement p r t b a
    dsimp only at h
    rw [target_mass_indicator p r t b a] at h
    have hF : F b a = ∑' x, if r x = b then
        p x * ENNReal.ofReal (((if t x = a then 1 else 0 : ℝ) -
            (targetFiberMass p r t b a / conceptFiberMass p r b).toReal)^2)
        else 0 := by
      dsimp only [F, risk]
      apply tsum_congr
      intro x
      by_cases hx : r x = b <;> simp [hx, indicatorReal, posteriorReal]
    rw [hF]
    exact h
  have hsum : (∑' b, ∑' a, F b a) + collisionScore p r t = 1 := by
    unfold collisionScore
    rw [← ENNReal.tsum_add]
    calc
      _ = ∑' b, conceptFiberMass p r b := by
        apply tsum_congr
        intro b
        rw [← ENNReal.tsum_add]
        exact (tsum_congr (hcoord b)).trans (targetFiberMass_tsum p r t b)
      _ = 1 := conceptFiberMass_tsum_all p r
  have hc : collisionScore p r t ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      _ ≤ conditionalLogicalImpurity p r t + collisionScore p r t := self_le_add_left _ _
      _ = 1 := impurity_add_collision p r t
  have hsplit : (∑' b, ∑' a, F b a) = ∑' a, ∑' x, risk a x := by
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro a
    simp only [F]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro x
    rw [tsum_eq_single (r x)]
    · simp
    · intro b hb
      simp [Ne.symm hb]
  exact (ENNReal.add_left_inj hc).mp ((impurity_add_collision p r t).trans hsum.symm) |>.trans hsplit


private theorem lp_risk_of_ae {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) (g h : Lp ℝ 2 p.toMeasure) {u v : X → ℝ}
    (hu : (g : X → ℝ) =ᵐ[p.toMeasure] u)
    (hv : (h : X → ℝ) =ᵐ[p.toMeasure] v) :
    ENNReal.ofReal (‖g - h‖^2) = ∑' x, p x * ENNReal.ofReal ((u x - v x)^2) := by
  rw [l2_sq_eq_lintegral, ← pmf_lintegral_eq_tsum]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub g h, hu, hv] with x hs hx hy
  simp only [hs, Pi.sub_apply, hx, hy]

private theorem posterior_lp_ae {X B A : Type*} (p : PMF X)
    (r : Concept X B) (t : Concept X A) (a : A) :
    letI : MeasurableSpace X := ⊤
    let μ := p.toMeasure
    ∀ hu : MemLp (indicatorReal t a) 2 μ,
      let m := MeasurableSpace.comap r (⊤ : MeasurableSpace B)
      let hm : m ≤ (⊤ : MeasurableSpace X) := le_top
      ((↑(condExpL2 ℝ ℝ hm (hu.toLp (indicatorReal t a))) : Lp ℝ 2 μ) : X → ℝ)
        =ᵐ[μ] fun x => posteriorReal p r t (r x) a := by
  intro μ hu m hm
  have ha : indicatorReal t a =
      ({x | t x = a} : Set X).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases ht : t x = a <;> simp [indicatorReal, Set.indicator, ht]
  have hprob := pmf_posterior_eq_condExp p (fun x => r x) (fun x => t x) a
  refine (hu.condExpL2_ae_eq_condExp hm).trans ?_
  rw [ha]
  refine hprob.trans (Filter.Eventually.of_forall fun x => ?_)
  change (((∑' y, ({y | r y = r x ∧ t y = a} : Set X).indicator p y)
    / conceptFiberMass p r (r x)).toReal) = _
  rw [target_mass_indicator p r t (r x) a]
  rfl

private theorem coordinate_pythagoras {X C D A : Type*}
    (p : PMF X) (r : Concept X D) (t : Concept X A) (f : D → C) (a : A) :
    (∑' x, p x * ENNReal.ofReal
      ((indicatorReal t a x - posteriorReal p (f ∘ r) t (f (r x)) a)^2)) =
    (∑' x, p x * ENNReal.ofReal
      ((indicatorReal t a x - posteriorReal p r t (r x) a)^2)) +
    (∑' x, p x * ENNReal.ofReal
      ((posteriorReal p r t (r x) a - posteriorReal p (f ∘ r) t (f (r x)) a)^2)) := by
  classical
  let mX : MeasurableSpace X := ⊤
  let mx : MeasurableSingletonClass X := by infer_instance
  let μ := p.toMeasure
  let u := indicatorReal t a
  have hu : MemLp u 2 μ := by
    apply MemLp.of_bound (μ := μ) ((measurable_from_top : Measurable u).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall fun x => by
      by_cases ht : t x = a <;> simp [u, indicatorReal, ht]
  let U := hu.toLp u
  let mr := MeasurableSpace.comap r (⊤ : MeasurableSpace D)
  let mc := MeasurableSpace.comap (f ∘ r) (⊤ : MeasurableSpace C)
  have hmc : mc ≤ mr := by
    change MeasurableSpace.comap (f ∘ (fun x => r x)) ⊤ ≤ MeasurableSpace.comap (fun x => r x) ⊤
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  have hmr : mr ≤ (⊤ : MeasurableSpace X) := le_top
  let R : Lp ℝ 2 μ := ↑(condExpL2 ℝ ℝ hmr U)
  let C' : Lp ℝ 2 μ := ↑(condExpL2 ℝ ℝ (hmc.trans hmr) U)
  have hR : (R : X → ℝ) =ᵐ[μ] fun x => posteriorReal p r t (r x) a :=
    posterior_lp_ae p r t a hu
  have hC : (C' : X → ℝ) =ᵐ[μ] fun x => posteriorReal p (f ∘ r) t (f (r x)) a :=
    posterior_lp_ae p (f ∘ r) t a hu
  open D5.S3.ConceptDynamics.Prediction.ConditionalExpectationRefinementPythagoras in
  have hp : ‖U - C'‖^2 = ‖U - R‖^2 + ‖R - C'‖^2 :=
    (@conditional_expectation_refinement_pythagoras X mX μ mc mr hmc hmr U).1
  have hp' : ENNReal.ofReal (‖U - C'‖^2) =
      ENNReal.ofReal (‖U - R‖^2) + ENNReal.ofReal (‖R - C'‖^2) :=
    (congrArg ENNReal.ofReal hp).trans (ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _))
  exact ((@lp_risk_of_ae X mX mx) p U C' hu.coeFn_toLp hC).symm.trans
    (hp'.trans (congrArg₂ (· + ·) ((@lp_risk_of_ae X mX mx) p U R hu.coeFn_toLp hR)
      ((@lp_risk_of_ae X mX mx) p R C' hR hC)))


/-- The extra impurity from coarsening equals the weighted squared change in target posteriors. -/
theorem conditional_gini_exact_defect {X C D A : Type*}
    (p : PMF X) (r : Concept X D) (t : Concept X A) (f : D → C) :
    conditionalLogicalImpurity p (f ∘ r) t =
      conditionalLogicalImpurity p r t +
        ∑' d, ∑' a, conceptFiberMass p r d * ENNReal.ofReal
          (((targetFiberMass p r t d a / conceptFiberMass p r d).toReal -
             (targetFiberMass p (f ∘ r) t (f d) a /
               conceptFiberMass p (f ∘ r) (f d)).toReal)^2) := by
  change conditionalLogicalImpurity p (f ∘ r) t =
    conditionalLogicalImpurity p r t +
      ∑' d, ∑' a, conceptFiberMass p r d * ENNReal.ofReal
        ((posteriorReal p r t d a - posteriorReal p (f ∘ r) t (f d) a)^2)
  classical
  let delta : D → A → ENNReal := fun d a => ENNReal.ofReal
    ((posteriorReal p r t d a - posteriorReal p (f ∘ r) t (f d) a)^2)
  have hgroup (a : A) :
      (∑' x, p x * delta (r x) a) = ∑' d, conceptFiberMass p r d * delta d a := by
    calc
      _ = ∑' x, ∑' d, ({x | r x = d} : Set X).indicator p x * delta d a := by
        apply tsum_congr
        intro x
        rw [tsum_eq_single (r x)]
        · simp
        · intro d hd
          simp [Set.indicator, Ne.symm hd]
      _ = ∑' d, ∑' x, ({x | r x = d} : Set X).indicator p x * delta d a := ENNReal.tsum_comm
      _ = _ := by
        apply tsum_congr
        intro d
        rw [ENNReal.tsum_mul_right]
        rfl
  rw [impurity_eq_weighted_indicator_risk p (f ∘ r) t,
    impurity_eq_weighted_indicator_risk p r t]
  calc
    _ = ∑' a, ((∑' x, p x * ENNReal.ofReal
        ((indicatorReal t a x - posteriorReal p r t (r x) a)^2)) +
          (∑' d, conceptFiberMass p r d * delta d a)) := by
      apply tsum_congr
      intro a
      exact (coordinate_pythagoras p r t f a).trans (congrArg (_ + ·) (hgroup a))
    _ = _ := by
      rw [ENNReal.tsum_add]
      congr 1
      exact ENNReal.tsum_comm

#print axioms conditional_gini_exact_defect

end
end D5.S3.ConceptDynamics.Information.ConditionalGiniDefect
