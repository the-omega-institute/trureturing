/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Lp.lpSpace]
   utility: none
   digest: Uniform Hardy tails on the common real edge ell2 and actual node L2 spaces. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceMass
open MeasureTheory
open scoped BigOperators ENNReal

/-- Only nonempty original addresses are edge coordinates. -/
abbrev Edge := {p : Address // p ≠ []}

/-- One common real Hilbert space for all separately supplied finite sources. -/
abbrev H := lp (fun _ : Edge => ℝ) 2

/-- Each source has its own actual uniformly weighted node space. -/
abbrev NodeL2 (n : ℕ) := Lp ℝ 2 (μ n)

/-- Actual edges of one native source. -/
def edges (n : ℕ) : Finset Edge := (vertices n).subtype (· ≠ [])

/-- Actual prefixes beyond a depth cutoff, omitting the root. -/
def path (n h : ℕ) (x : Node n) : Finset Edge :=
  (edges n).filter fun p => h < p.val.length ∧ p.val.IsPrefix x.val

/-- Root-path increments; missing addresses have no term. -/
def value (n h : ℕ) (z : H) (x : Node n) : ℝ := ∑ p ∈ path n h x, z p

/-- The actual path function as a node L2 element. -/
def trace (n h : ℕ) (z : H) : NodeL2 n :=
  (MemLp.of_discrete : MemLp (value n h z) 2 (μ n)).toLp (value n h z)

private theorem a_pos : 0 < a := inv_pos.mpr Real.goldenRatio_pos
private theorem a_lt_one : a < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

private theorem path_weights (n h : ℕ) (x : Node n) :
    (∑ p ∈ path n h x, a^p.val.length) ≤ a^(h+1)/(1-a) := by
  classical
  let f : Edge → ℕ := fun p => p.val.length-(h+1)
  have inj : ∀ p ∈ path n h x, ∀ q ∈ path n h x, f p = f q → p = q := by
    intro p hp q hq he
    obtain ⟨_, hpL, hpP⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hqL, hqP⟩ := Finset.mem_filter.mp hq
    have hl : p.val.length = q.val.length := by dsimp [f] at he; omega
    apply Subtype.ext
    rw [List.prefix_iff_eq_take.mp hpP, List.prefix_iff_eq_take.mp hqP, hl]
  have summableA := summable_geometric_of_lt_one a_pos.le a_lt_one
  have geom := tsum_geometric_of_lt_one a_pos.le a_lt_one
  calc
    (∑ p ∈ path n h x, a^p.val.length) =
        a^(h+1) * ∑ k ∈ (path n h x).image f, a^k := by
      rw [Finset.sum_image inj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hL := (Finset.mem_filter.mp hp).2.1
      rw [← pow_add]
      congr 1
      dsimp [f]
      omega
    _ ≤ a^(h+1) * ∑' k : ℕ, a^k :=
      mul_le_mul_of_nonneg_left
        (summableA.sum_le_tsum _ (fun _ _ => (pow_nonneg a_pos.le _)))
        (pow_nonneg a_pos.le _)
    _ = a^(h+1)/(1-a) := by rw [geom]; ring

private theorem pointwise_bound (n h : ℕ) (z : H) (x : Node n) :
    value n h z x ^ 2 ≤ a^(h+1)/(1-a) *
      ∑ p ∈ path n h x, (z p)^2/a^p.val.length := by
  have cauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (path n h x)
    (r := fun p => z p) (f := fun p => a^p.val.length)
    (g := fun p => (z p)^2/a^p.val.length)
    (fun p _ => (pow_pos a_pos _).le)
    (fun p _ => div_nonneg (sq_nonneg _) (pow_pos a_pos _).le)
    (fun p _ => by rw [mul_div_cancel₀ _ (pow_pos a_pos _).ne'])
  exact cauchy.trans (mul_le_mul_of_nonneg_right (path_weights n h x)
    (Finset.sum_nonneg fun p _ => div_nonneg (sq_nonneg _) (pow_pos a_pos _).le))

private theorem trace_sq (n h : ℕ) (z : H) :
    ‖trace n h z‖^2 = ∫ x, (value n h z x)^2 ∂μ n := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(MemLp.of_discrete : MemLp (value n h z) 2 (μ n)).coeFn_toLp]
    with x hx
  change (trace n h z x)*(trace n h z x) = (value n h z x)^2
  rw [show trace n h z x = value n h z x from hx]
  ring

private theorem integral_path (n h : ℕ) (z : H) :
    (∫ x, ∑ p ∈ path n h x, (z p)^2/a^p.val.length ∂μ n) =
      ∑ p ∈ edges n, if h < p.val.length then
        mass n p.val * ((z p)^2/a^p.val.length) else 0 := by
  classical
  simp only [path, Finset.sum_filter]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hL : h < p.val.length
  · simp only [hL, true_and, if_true]
    calc
      (∫ x : Node n, if p.val.IsPrefix x.val then (z p)^2/a^p.val.length else 0 ∂μ n) =
          ∫ x, Set.indicator {x : Node n | p.val.IsPrefix x.val}
            (fun _ => (z p)^2/a^p.val.length) x ∂μ n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by simp [Set.indicator]
      _ = (μ n {x | p.val.IsPrefix x.val}).toReal * ((z p)^2/a^p.val.length) := by
        exact integral_indicator_const ((z p)^2/a^p.val.length) (by trivial)
      _ = _ := by rw [finite_source_masses.2.2.2.2.1]
  · simp [hL]

private theorem trace_bound_sq (n h : ℕ) (z : H) :
    ‖trace n h z‖^2 ≤
      (2*Real.goldenRatio*a^(h+1)/(1-a))*‖z‖^2 := by
  classical
  have hden : 0 < 1-a := sub_pos.mpr a_lt_one
  have hC : 0 ≤ a^(h+1)/(1-a) := div_nonneg (pow_pos a_pos _).le hden.le
  have integral_le : (∫ x, (value n h z x)^2 ∂μ n) ≤
      ∫ x, a^(h+1)/(1-a) *
        (∑ p ∈ path n h x, (z p)^2/a^p.val.length) ∂μ n :=
    integral_mono Integrable.of_finite Integrable.of_finite (pointwise_bound n h z)
  rw [integral_const_mul, integral_path] at integral_le
  have sum_le : (∑ p ∈ edges n, if h < p.val.length then
        mass n p.val * ((z p)^2/a^p.val.length) else 0) ≤
      2*Real.goldenRatio * ∑ p ∈ edges n, (z p)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    split_ifs
    · have hm := finite_source_masses.2.2.2.1 n p.val
      have hw := pow_pos a_pos p.val.length
      apply (mul_le_mul_of_nonneg_right hm (div_nonneg (sq_nonneg _) hw.le)).trans_eq
      field_simp
    · positivity
  have energy := lp.sum_rpow_le_norm_rpow (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
    z (edges n)
  have energy' : (∑ p ∈ edges n, (z p)^2) ≤ ‖z‖^2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using energy
  rw [trace_sq]
  calc
    _ ≤ _ := integral_le
    _ ≤ (a^(h+1)/(1-a)) * (2*Real.goldenRatio * ‖z‖^2) :=
      mul_le_mul_of_nonneg_left (sum_le.trans
        (mul_le_mul_of_nonneg_left energy' (by positivity))) hC
    _ = _ := by ring

/-- Coordinate projection onto nonempty addresses of length at most h. -/
def projectionLinear (h : ℕ) : H →ₗ[ℝ] H where
  toFun z := ⟨fun p => if p.val.length ≤ h then z p else 0,
    (lp.memℓp z).mono' (fun p => by split_ifs <;> simp)⟩
  map_add' z w := by ext p; simp only [lp.coeFn_add, Pi.add_apply]; split_ifs <;> simp
  map_smul' c z := by
    ext p
    simp only [lp.coeFn_smul, Pi.smul_apply]
    split_ifs <;> simp

/-- The bounded depth projection on the common edge space. -/
def P (h : ℕ) : H →L[ℝ] H :=
  (projectionLinear h).mkContinuous 1 fun z => by
    simpa only [one_mul] using
      (lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
        (x := projectionLinear h z) (y := z) fun p => by
          change ‖if p.val.length ≤ h then z p else 0‖ ≤ ‖z p‖
          split_ifs <;> simp)

private theorem trace_tail (n h : ℕ) (z : H) :
    trace n 0 (z-P h z) = trace n h z := by
  classical
  apply MemLp.toLp_congr
  apply Filter.Eventually.of_forall
  intro x
  simp only [value, path, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpL : 0 < p.val.length :=
    Nat.pos_of_ne_zero (fun h => p.property (List.length_eq_zero_iff.mp h))
  change (if 0 < p.val.length ∧ p.val.IsPrefix x.val then
      z p - (if p.val.length ≤ h then z p else 0) else 0) = _
  by_cases hL : h < p.val.length
  · simp [hpL, hL, Nat.not_le.mpr hL]
  · simp [hpL, hL, Nat.le_of_not_gt hL]

private theorem trace_norm_bound (n h : ℕ) (z : H) :
    ‖trace n h z‖ ≤ Real.sqrt (2*Real.goldenRatio*a^(h+1)/(1-a))*‖z‖ := by
  have hden : 0 < 1-a := sub_pos.mpr a_lt_one
  have hC : 0 ≤ 2*Real.goldenRatio*a^(h+1)/(1-a) := by positivity
  have hb := Real.sqrt_le_sqrt (trace_bound_sq n h z)
  simpa only [Real.sqrt_mul hC, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hb

private def traceLinear (n : ℕ) : H →ₗ[ℝ] NodeL2 n where
  toFun := trace n 0
  map_add' z w := by
    unfold trace
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    apply Filter.Eventually.of_forall
    intro x
    simp only [value, lp.coeFn_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c z := by
    change trace n 0 (c • z) = c • trace n 0 z
    unfold trace
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    apply Filter.Eventually.of_forall
    intro x
    simp [value, Finset.mul_sum]

/-- The native root-path map into this source's own actual node L2 space. -/
def J (n : ℕ) : H →L[ℝ] NodeL2 n :=
  (traceLinear n).mkContinuous (Real.sqrt (2*Real.goldenRatio*a/(1-a)))
    fun z => by
      change ‖trace n 0 z‖ ≤ _
      simpa only [zero_add, pow_one] using trace_norm_bound n 0 z

set_option maxHeartbeats 1000000 in
-- The dependent finite node spaces and continuous-map coercions share this elaboration budget.
/-- The uniform coefficient envelope, squared trace bound and operator-norm Hardy tail. -/
theorem finite_source_hardy :
    (∀ (n : ℕ) (p : Address), mass n p ≤ 2*Real.goldenRatio*a^p.length) ∧
    (∀ (n h : ℕ) (z : H), ‖J n (z-P h z)‖^2 ≤
      (2*Real.goldenRatio*a^(h+1)/(1-a))*‖z‖^2) ∧
    (∀ (n h : ℕ), ‖(J n).comp (ContinuousLinearMap.id ℝ H-P h)‖ ≤
      Real.sqrt (2*Real.goldenRatio*a^(h+1)/(1-a))) := by
  refine ⟨finite_source_masses.2.2.2.1, ?_, ?_⟩
  · intro n h z
    change ‖trace n 0 (z-P h z)‖^2 ≤ _
    rw [trace_tail]
    exact trace_bound_sq n h z
  · intro n h
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro z
    change ‖trace n 0 (z-P h z)‖ ≤ _
    rw [trace_tail]
    exact trace_norm_bound n h z


end D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy
