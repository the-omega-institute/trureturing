/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Probability.ProductMeasure]
   utility: none
   digest: Path sums on the fixed golden biased binary boundary and their Hardy extension. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! The actual golden biased boundary and its real path-sum extension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (Edge H P)
open FiniteSourceMass (a)
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

private theorem a_pos : 0 < a := inv_pos.mpr Real.goldenRatio_pos
private theorem a_lt_one : a < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

/-- The right-child probability, with false denoting L and true denoting R. -/
abbrev b : ℝ := a ^ 2

private theorem sum_weights : a + b = 1 := by
  change Real.goldenRatio⁻¹ + (Real.goldenRatio⁻¹)^2 = 1
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

/-- Infinite rays in the original address orientation. -/
abbrev Omega := ℕ → Bool

/-- The biased letter distribution, with mass a at false. -/
def bit : Measure Bool := ProbabilityTheory.bernoulliMeasure false true
  ⟨a, a_pos.le, a_lt_one.le⟩

instance : IsProbabilityMeasure bit := by unfold bit; infer_instance

/-- The fixed infinite product law on rays. -/
def M : Measure Omega := Measure.infinitePi (fun _ : ℕ => bit)

instance : IsProbabilityMeasure M := by unfold M; infer_instance

/-- The boundary Hilbert space; all approximations have this same codomain. -/
abbrev G := Lp ℝ 2 M

/-- Actual prefix cylinder, expressed through the original coordinates. -/
def cylinder (p : Address) : Set Omega :=
  Set.pi (Finset.range p.length) (fun i => {p.getD i false})

private theorem cylinder_measurable (p : Address) : MeasurableSet (cylinder p) :=
  MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)

/-- The product of the actual biased letter masses. -/
def mass (p : Address) : ℝ :=
  (p.map (fun c => if c then b else a)).prod

private theorem mass_bound (p : Address) : mass p ≤ a ^ p.length := by
  have hb : b ≤ a := by change a^2 ≤ a; nlinarith [a_pos, a_lt_one]
  induction p with
  | nil => simp only [mass, List.map_nil, List.prod_nil, List.length_nil, pow_zero, le_refl]
  | cons c p ih =>
    have hc : (if c then b else a) ≤ a := by
      cases c
      · exact le_rfl
      · exact hb
    have hc0 : 0 ≤ (if c then b else a) := by
      cases c
      · exact a_pos.le
      · exact sq_nonneg a
    change (if c then b else a) * mass p ≤ a^(p.length+1)
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_left ih hc0).trans
      (by nlinarith [pow_nonneg a_pos.le p.length])

private theorem bit_singleton (c : Bool) :
    (bit {c}).toReal = if c then b else a := by
  change bit.real {c} = _
  cases c
  · exact ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_notMem _
      (measurableSet_singleton false) (by simp) (by simp)
  · have he := ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_mem
      (x := false) (y := true) (⟨a, a_pos.le, a_lt_one.le⟩ : unitInterval)
      (measurableSet_singleton true) (by simp) (by simp)
    change bit.real {true} = b
    change bit.real {true} = 1-a at he
    linarith [sum_weights]

private theorem cylinder_mass (p : Address) : (M (cylinder p)).toReal = mass p := by
  rw [M, cylinder, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _),
    ENNReal.toReal_prod]
  simp only [bit_singleton]
  induction p using List.reverseRecOn with
  | nil => simp [mass]
  | append_singleton p c ih =>
    simp only [List.length_append, List.length_singleton, Finset.prod_range_succ]
    have hp : ∀ i ∈ Finset.range p.length,
        (p ++ [c]).getD i false = p.getD i false := by
      intro i hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_append,
        Finset.mem_range.mp hi]
    rw [Finset.prod_congr rfl (fun i hi => by rw [hp i hi]), ih]
    simp only [mass, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, List.getD_eq_getElem?_getD, List.getElem?_concat_length,
      Option.getD_some]

/-- The finite path inside an arbitrary finite set of nonempty edges. -/
private def path (s : Finset Edge) (h : ℕ) (ω : Omega) : Finset Edge :=
  by classical exact s.filter (fun p => h < p.val.length ∧ ω ∈ cylinder p.val)

/-- The actual finite increment sum along a ray. -/
private def value (s : Finset Edge) (h : ℕ) (z : H) (ω : Omega) : ℝ :=
  ∑ p ∈ path s h ω, z p

private theorem value_memLp (s : Finset Edge) (h : ℕ) (z : H) :
    MemLp (value s h z) 2 M := by
  classical
  have hi : ∀ p : Edge, MemLp (fun ω : Omega =>
      if h < p.val.length ∧ ω ∈ cylinder p.val then z p else 0) 2 M := by
    intro p
    by_cases hh : h < p.val.length
    · convert (memLp_const (z p) : MemLp (fun _ : Omega => z p) 2 M).indicator
        (cylinder_measurable p.val).nullMeasurableSet using 1
      funext ω
      simp only [hh, true_and, Set.indicator]
    · simp only [hh, false_and, ite_false]
      exact MemLp.zero
  apply (memLp_congr_ae (Filter.Eventually.of_forall fun ω =>
    show (∑ p ∈ s, if h < p.val.length ∧ ω ∈ cylinder p.val then z p else 0) =
      value s h z ω from by simp only [value, path, Finset.sum_filter])).mp
  exact memLp_finsetSum s (fun p _ => hi p)

/-- A finite path sum in the fixed boundary L2 space. -/
private def trace (s : Finset Edge) (h : ℕ) (z : H) : G :=
  (value_memLp s h z).toLp (value s h z)

private theorem same_length (ω : Omega) (p q : Address)
    (hp : ω ∈ cylinder p) (hq : ω ∈ cylinder q) (hl : p.length = q.length) : p = q := by
  apply List.ext_getElem hl
  intro i hi hj
  have hp' := hp i (Finset.mem_range.mpr hi)
  have hq' := hq i (Finset.mem_range.mpr hj)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj] using hp'.symm.trans hq'

private theorem path_weights (s : Finset Edge) (h : ℕ) (ω : Omega) :
    (∑ p ∈ path s h ω, a ^ p.val.length) ≤ a^(h+1)/(1-a) := by
  classical
  let f : Edge → ℕ := fun p => p.val.length - (h+1)
  have inj : ∀ p ∈ path s h ω, ∀ q ∈ path s h ω, f p = f q → p = q := by
    intro p hp q hq he
    obtain ⟨_, hpL, hpP⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hqL, hqP⟩ := Finset.mem_filter.mp hq
    apply Subtype.ext
    apply same_length ω _ _ hpP hqP
    dsimp [f] at he
    omega
  calc
    _ = a^(h+1) * ∑ k ∈ (path s h ω).image f, a^k := by
      rw [Finset.sum_image inj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← pow_add]
      congr 1
      have := (Finset.mem_filter.mp hp).2.1
      dsimp [f]
      omega
    _ ≤ a^(h+1) * ∑' k : ℕ, a^k := mul_le_mul_of_nonneg_left
      ((summable_geometric_of_lt_one a_pos.le a_lt_one).sum_le_tsum _
        (fun _ _ => pow_nonneg a_pos.le _)) (pow_nonneg a_pos.le _)
    _ = _ := by rw [tsum_geometric_of_lt_one a_pos.le a_lt_one]; ring

private theorem pointwise_bound (s : Finset Edge) (h : ℕ) (z : H) (ω : Omega) :
    value s h z ω ^ 2 ≤ a^(h+1)/(1-a) *
      ∑ p ∈ path s h ω, (z p)^2/a^p.val.length := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (path s h ω)
    (r := fun p => z p) (f := fun p => a^p.val.length)
    (g := fun p => (z p)^2/a^p.val.length)
    (fun p _ => (pow_pos a_pos _).le)
    (fun p _ => div_nonneg (sq_nonneg _) (pow_pos a_pos _).le)
    (fun p _ => by rw [mul_div_cancel₀ _ (pow_pos a_pos _).ne'])
  exact hc.trans (mul_le_mul_of_nonneg_right (path_weights s h ω)
    (Finset.sum_nonneg fun p _ => div_nonneg (sq_nonneg _) (pow_pos a_pos _).le))

private theorem trace_sq (s : Finset Edge) (h : ℕ) (z : H) :
    ‖trace s h z‖^2 = ∫ ω, (value s h z ω)^2 ∂M := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(value_memLp s h z).coeFn_toLp] with ω hω
  change (trace s h z ω) * (trace s h z ω) = _
  rw [show trace s h z ω = value s h z ω from hω]
  ring

private theorem integral_path (s : Finset Edge) (h : ℕ) (z : H) :
    (∫ ω, ∑ p ∈ path s h ω, (z p)^2/a^p.val.length ∂M) =
      ∑ p ∈ s, if h < p.val.length then
        mass p.val * ((z p)^2/a^p.val.length) else 0 := by
  classical
  simp only [path, Finset.sum_filter]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p hp
    by_cases hh : h < p.val.length
    · simp only [hh, true_and, ite_true]
      change (∫ ω, (cylinder p.val).indicator
        (fun _ => (z p)^2/a^p.val.length) ω ∂M) = _
      rw [integral_indicator_const _ (cylinder_measurable p.val)]
      change (M (cylinder p.val)).toReal * _ = mass p.val * _
      rw [cylinder_mass]
    · simp [hh]
  · intro p hp
    by_cases hh : h < p.val.length
    · simp only [hh, true_and]
      change Integrable ((cylinder p.val).indicator
        (fun _ : Omega => (z p)^2/a^p.val.length)) M
      exact (integrable_const _).indicator (cylinder_measurable p.val)
    · simpa [hh] using (integrable_zero Omega ℝ M)

private theorem trace_bound_sq (s : Finset Edge) (h : ℕ) (z : H) :
    ‖trace s h z‖^2 ≤ (a^(h+1)/(1-a))*‖z‖^2 := by
  classical
  have hden : 0 < 1-a := sub_pos.mpr a_lt_one
  have hC : 0 ≤ a^(h+1)/(1-a) := div_nonneg (pow_pos a_pos _).le hden.le
  have hi : Integrable (fun ω => ∑ p ∈ path s h ω, (z p)^2/a^p.val.length) M := by
    simp only [path, Finset.sum_filter]
    apply integrable_finsetSum
    intro p hp
    by_cases hh : h < p.val.length
    · simp only [hh, true_and]
      change Integrable ((cylinder p.val).indicator
        (fun _ : Omega => (z p)^2/a^p.val.length)) M
      exact (integrable_const _).indicator (cylinder_measurable p.val)
    · simpa [hh] using (integrable_zero Omega ℝ M)
  have hb := integral_mono (value_memLp s h z).integrable_sq
    (hi.const_mul _) (pointwise_bound s h z)
  rw [integral_const_mul, integral_path] at hb
  have he : (∑ p ∈ s, if h < p.val.length then
        mass p.val * ((z p)^2/a^p.val.length) else 0) ≤ ∑ p ∈ s, (z p)^2 := by
    apply Finset.sum_le_sum
    intro p hp
    split_ifs
    · calc
        _ ≤ a^p.val.length * ((z p)^2/a^p.val.length) :=
          mul_le_mul_of_nonneg_right (mass_bound _) (by positivity)
        _ = _ := by field_simp
    · positivity
  have hz : (∑ p ∈ s, (z p)^2) ≤ ‖z‖^2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      lp.sum_rpow_le_norm_rpow (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) z s
  rw [trace_sq]
  exact hb.trans (mul_le_mul_of_nonneg_left (he.trans hz) hC)

private theorem trace_bound (s : Finset Edge) (h : ℕ) (z : H) :
    ‖trace s h z‖ ≤ Real.sqrt (a^(h+1)/(1-a))*‖z‖ := by
  have hden : 0 < 1-a := sub_pos.mpr a_lt_one
  have hC : 0 ≤ a^(h+1)/(1-a) := div_nonneg (pow_pos a_pos _).le hden.le
  have hb := Real.sqrt_le_sqrt (trace_bound_sq s h z)
  simpa only [Real.sqrt_mul hC, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hb

/-- A unit increment has its actual cylinder indicator as trace. -/
def indicator (p : Edge) : G :=
  indicatorConstLp 2 (cylinder_measurable p.val) (measure_ne_top _ _) 1

/-- Finitely supported increments finiteInclusiond in the original real edge space. -/
private def finiteInclusion : (Edge →₀ ℝ) →ₗ[ℝ] H :=
  Finsupp.linearCombination ℝ (fun p => lp.single 2 p (1 : ℝ))

private theorem finiteInclusion_apply (f : Edge →₀ ℝ) (p : Edge) : finiteInclusion f p = f p := by
  classical
  simp only [finiteInclusion, Finsupp.linearCombination_apply, Finsupp.sum,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.coeFn_single, Pi.single_apply, smul_eq_mul]
  by_cases hp : p ∈ f.support
  · simp [mul_ite, hp]
  · simp [mul_ite, hp, Finsupp.notMem_support_iff.mp hp]

/-- The finite path-sum linear map, before completion. -/
private def finiteJ : (Edge →₀ ℝ) →ₗ[ℝ] G :=
  Finsupp.linearCombination ℝ indicator

private theorem finiteJ_trace (f : Edge →₀ ℝ) :
    finiteJ f = trace f.support 0 (finiteInclusion f) := by
  classical
  apply Lp.ext
  have hi : ∀ᵐ ω ∂M, ∀ p : Edge,
      indicator p ω = (cylinder p.val).indicator (fun _ => (1 : ℝ)) ω :=
    ae_all_iff.mpr (fun p => indicatorConstLp_coeFn)
  filter_upwards [Lp.coeFn_linearCombination f indicator, hi,
    (value_memLp f.support 0 (finiteInclusion f)).coeFn_toLp] with ω hf hi ht
  change ((Finsupp.linearCombination ℝ indicator) f) ω =
    ((value_memLp f.support 0 (finiteInclusion f)).toLp _) ω
  rw [hf, ht]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, value, path, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpL : 0 < p.val.length := List.length_pos_of_ne_nil p.property
  rw [hi p, finiteInclusion_apply]
  by_cases h : ω ∈ cylinder p.val <;> simp [h, hpL]

private theorem finiteInclusion_dense : DenseRange finiteInclusion := by
  intro z
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z)
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ p ∈ s, Finsupp.single p (z p), ?_⟩
  simp [finiteInclusion, Finsupp.linearCombination_single, ← lp.single_smul]

private theorem finiteJ_bound (f : Edge →₀ ℝ) :
    ‖finiteJ f‖ ≤ Real.sqrt (a/(1-a)) * ‖finiteInclusion f‖ := by
  rw [finiteJ_trace]
  simpa using trace_bound f.support 0 (finiteInclusion f)

/-- The bounded path-sum extension on all real square-summable increments. -/
def J : H →L[ℝ] G := finiteJ.extendOfNorm finiteInclusion

private theorem J_finiteInclusion (f : Edge →₀ ℝ) : J (finiteInclusion f) = finiteJ f :=
  LinearMap.extendOfNorm_eq finiteInclusion_dense ⟨_, finiteJ_bound⟩ f

private theorem J_single (p : Edge) (c : ℝ) : J (lp.single 2 p c) = c • indicator p := by
  have he : finiteInclusion (Finsupp.single p c) = lp.single 2 p c := by
    simp [finiteInclusion, Finsupp.linearCombination_single, ← lp.single_smul]
  rw [← he, J_finiteInclusion]
  simp [finiteJ, Finsupp.linearCombination_single]

private theorem finite_sum_trace (s : Finset Edge) (h : ℕ) (z : H) :
    (∑ p ∈ s, (if h < p.val.length then z p else 0) • indicator p) = trace s h z := by
  classical
  apply Lp.ext
  have hi : ∀ᵐ ω ∂M, ∀ p : Edge,
      indicator p ω = (cylinder p.val).indicator (fun _ => (1 : ℝ)) ω :=
    ae_all_iff.mpr (fun p => indicatorConstLp_coeFn)
  have hc := Lp.coeFn_finsetSum s (fun p =>
    (if h < p.val.length then z p else 0) • indicator p)
  have hm : ∀ᵐ ω ∂M, ∀ p : Edge,
      ((if h < p.val.length then z p else 0) • indicator p : G) ω =
        (if h < p.val.length then z p else 0) * indicator p ω := by
    apply ae_all_iff.mpr
    intro p
    exact Lp.coeFn_smul _ _
  filter_upwards [hc, hm, hi, (value_memLp s h z).coeFn_toLp] with ω hc hm hi ht
  change (∑ p ∈ s, (if h < p.val.length then z p else 0) • indicator p : G) ω =
    ((value_memLp s h z).toLp _) ω
  rw [hc, ht]
  simp only [Finset.sum_apply, value, path, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hm p, hi p]
  by_cases hh : h < p.val.length <;> by_cases hp : ω ∈ cylinder p.val <;>
    simp [hh, hp]

private theorem J_tail_sum (h : ℕ) (z : H) :
    HasSum (fun p : Edge => (if h < p.val.length then z p else 0) • indicator p)
      (J (z-P h z)) := by
  have hs := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (z-P h z)).map
    J J.continuous
  have he : (J ∘ fun p : Edge => lp.single 2 p ((z-P h z) p)) =
      (fun p : Edge => (if h < p.val.length then z p else 0) • indicator p) := by
    funext p
    change J (lp.single 2 p ((z-P h z) p)) = _
    rw [J_single]
    congr 1
    change z p - (if p.val.length ≤ h then z p else 0) = _
    by_cases hp : h < p.val.length
    · simp [hp, Nat.not_le.mpr hp]
    · simp [hp, Nat.le_of_not_gt hp]
  rw [he] at hs
  exact hs

/-- The actual boundary trace is the L2 sum of cylinder increments. Its Hardy
estimate holds for every depth and every vector in the original edge ell2. -/
theorem boundary_trace_hardy :
    (∀ z : H, HasSum (fun p : Edge => z p • indicator p) (J z)) ∧
    (∀ (h : ℕ) (z : H), ‖J (z-P h z)‖^2 ≤ (a^(h+1)/(1-a))*‖z‖^2) := by
  constructor
  · intro z
    simpa only [Function.comp_def, J_single] using
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z).map J J.continuous
  · intro h z
    apply le_of_tendsto ((J_tail_sum h z).norm.pow 2)
    exact Filter.Eventually.of_forall (fun s => by
      rw [finite_sum_trace]
      exact trace_bound_sq s h z)

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace
