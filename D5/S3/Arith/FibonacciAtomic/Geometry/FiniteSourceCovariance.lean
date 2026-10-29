/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Fibonacci]
   utility: none
   digest: Actual finite-source mean, Gram and covariance norm limits. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Data.Set.Finite.List

/-! Actual all-occurrence operators on the common edge Hilbert space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (H Edge P NodeL2)
open FiniteSourceMass (N a)
open Observer.NativeRankedNavigationCompiler (pathCost)
open MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators ENNReal

/-- The constant one in the actual uniformly weighted node space. -/
def one (n : ℕ) : NodeL2 n := (memLp_const (1 : ℝ)).toLp (fun _ => 1)

/-- The actual finite-source mean increment vector. -/
def v (n : ℕ) : H := (FiniteSourceHardy.J n).adjoint (one n)

/-- The actual finite-source Gram operator on the common edge space. -/
def B (n : ℕ) : H →L[ℝ] H := (FiniteSourceHardy.J n).adjoint.comp (FiniteSourceHardy.J n)

/-- Centering subtracts the actual mean rank-one operator. -/
def Sigma (n : ℕ) : H →L[ℝ] H := B n - rankOne ℝ (v n) (v n)

private theorem normalized_count :
    Tendsto (fun n : ℕ => (N n : ℝ) / Real.goldenRatio^n) atTop
      (𝓝 (2*Real.goldenRatio/Real.sqrt 5)) := by
  have hq : |Real.goldenConj / Real.goldenRatio| < 1 := by
    rw [abs_div, div_lt_one (by positivity), abs_of_pos Real.goldenRatio_pos, abs_lt]
    ring_nf
    bound
  have ht := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
  have ha := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr Real.goldenRatio_pos.le)
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  have hl := (((tendsto_const_nhds (x := (1 : ℝ))).sub (ht.comp (tendsto_add_atTop_nat 1))).const_mul
    (2*Real.goldenRatio/Real.sqrt 5)).sub ha
  have he (n : ℕ) : (N n : ℝ) / Real.goldenRatio^n =
      (2*Real.goldenRatio/Real.sqrt 5) *
        (1-(Real.goldenConj/Real.goldenRatio)^(n+1)) - (Real.goldenRatio⁻¹)^n := by
    rw [FiniteSourceMass.cardinality, Nat.cast_sub (by
      have : 0 < Nat.fib (n+1) := Nat.fib_pos.mpr (by omega)
      omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Real.coe_fib_eq]
    rw [div_pow, inv_pow, pow_succ, pow_succ]
    field_simp
    <;> ring
  simpa only [Function.comp_def, sub_zero, mul_one] using hl.congr' (Eventually.of_forall
    (fun n => (he n).symm))

private theorem count_ratio_limit (k : ℕ) :
    Tendsto (fun n : ℕ => (N (n-k) : ℝ)/(N n : ℝ)) atTop (𝓝 (a^k)) := by
  have h := ((normalized_count.comp (tendsto_sub_atTop_nat k)).div normalized_count
    (by positivity : 2*Real.goldenRatio/Real.sqrt 5 ≠ 0)).mul_const (a^k)
  have he : (fun n : ℕ => (N (n-k) : ℝ)/(N n : ℝ)) =ᶠ[atTop]
      (fun n => ((N (n-k) : ℝ)/Real.goldenRatio^(n-k) /
        ((N n : ℝ)/Real.goldenRatio^n)) * a^k) := by
    filter_upwards [eventually_ge_atTop k] with n hn
    have hp : Real.goldenRatio^n = Real.goldenRatio^(n-k)*Real.goldenRatio^k := by
      rw [← pow_add, Nat.sub_add_cancel hn]
    rw [hp]
    simp only [a, inv_pow]
    field_simp
  simpa only [div_self (by positivity : 2*Real.goldenRatio/Real.sqrt 5 ≠ 0), one_mul]
    using h.congr' he.symm

private theorem boundary_mass_power (p : Address) : BiasedBoundaryTrace.mass p = a^(pathCost p) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    change (if c then a^2 else a) * BiasedBoundaryTrace.mass p = _
    rw [ih]
    cases c <;> simp only [Bool.false_eq_true, if_false, if_true,
      Observer.NativeRankedNavigationCompiler.pathCost, pow_add] <;> ring

private theorem mass_limit (p : Address) :
    Tendsto (fun n => FiniteSourceMass.mass n p) atTop (𝓝 (BiasedBoundaryTrace.mass p)) := by
  by_cases hp : p = []
  · subst p
    have he (n : ℕ) : FiniteSourceMass.mass n [] = 1 :=
      (FiniteSourceMass.finite_source_masses.2.2.2.2.2.2.2.2 n).1
    simpa only [he, BiasedBoundaryTrace.mass, List.map_nil, List.prod_nil] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · rw [boundary_mass_power]
    apply (count_ratio_limit (pathCost p)).congr'
    filter_upwards [eventually_ge_atTop (max (pathCost p) (pathCost p.dropLast+2))]
      with n hn
    exact (FiniteSourceMass.finite_source_masses.2.1 n p hp
      ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)).2.symm

private def e (p : Edge) : H := lp.single 2 p 1

private theorem inner_e (p : Edge) (z : H) : inner ℝ (e p) z = z p := by
  classical
  simp [e, lp.inner_single_left]

private def block (h : ℕ) : Finset Edge :=
  ((List.finite_length_le Bool h).toFinset).subtype (· ≠ [])

private theorem mem_block (h : ℕ) (p : Edge) : p ∈ block h ↔ p.val.length ≤ h := by
  classical
  simp [block]

private theorem P_expand (h : ℕ) (z : H) : P h z = ∑ p ∈ block h, z p • e p := by
  classical
  ext q
  change (if q.val.length ≤ h then z q else 0) = _
  simp [e, lp.coeFn_sum, lp.coeFn_smul, lp.coeFn_single, Pi.single_apply,
    mul_ite, mem_block, eq_comm]

private theorem P_norm (h : ℕ) : ‖P h‖ ≤ 1 := by
  apply LinearMap.mkContinuous_norm_le
  norm_num

private theorem P_zero : P 0 = 0 := by
  ext z p
  have hp := List.length_pos_of_ne_nil p.property
  change (if p.val.length ≤ 0 then z p else 0) = 0
  simp [Nat.not_le.mpr hp]

private theorem prefix_vertex (n : ℕ) (p : Address) (x : FiniteSourceMass.Node n)
    (hp : p.IsPrefix x.val) : p ∈ FiniteSourceMass.vertices n := by
  obtain ⟨r, hr⟩ := hp
  obtain ⟨U, hU⟩ := (FiniteSourceMass.node_iff _ _).mp
    (List.mem_toFinset.mp x.property)
  have ha := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p r
    (AncestorAreaInstability.T n)
  rw [← hr, hU] at ha
  cases hs : ActualLeafHistoryRigidity.subtree p (AncestorAreaInstability.T n) with
  | none => simp [hs] at ha
  | some U => exact List.mem_toFinset.mpr ((FiniteSourceMass.node_iff _ _).mpr ⟨U, hs⟩)

private def nodeIndicator (n : ℕ) (p : Edge) : NodeL2 n :=
  indicatorConstLp 2 (show MeasurableSet {x : FiniteSourceMass.Node n | p.val.IsPrefix x.val}
    from by measurability) (measure_ne_top _ _) 1

private theorem finite_column (n : ℕ) (p : Edge) :
    FiniteSourceHardy.J n (e p) = nodeIndicator n p := by
  classical
  apply Lp.ext
  have ht := (MemLp.of_discrete : MemLp (FiniteSourceHardy.value n 0 (e p)) 2
    (FiniteSourceMass.μ n)).coeFn_toLp
  have hi : ∀ᵐ x ∂FiniteSourceMass.μ n,
      nodeIndicator n p x = Set.indicator {x : FiniteSourceMass.Node n | p.val.IsPrefix x.val}
        (fun _ => (1 : ℝ)) x := indicatorConstLp_coeFn
  filter_upwards [ht, hi] with x hx hi
  change FiniteSourceHardy.trace n 0 (e p) x = nodeIndicator n p x
  rw [show FiniteSourceHardy.trace n 0 (e p) x = FiniteSourceHardy.value n 0 (e p) x from hx, hi]
  have hpL := List.length_pos_of_ne_nil p.property
  by_cases hp : p.val.IsPrefix x.val
  · have hm : p ∈ FiniteSourceHardy.path n 0 x := by
      simp [FiniteSourceHardy.path, FiniteSourceHardy.edges, hp, hpL,
        prefix_vertex n p.val x hp]
    simp [FiniteSourceHardy.value, e, lp.coeFn_single, Pi.single_apply, eq_comm, hm,
      Set.indicator_of_mem hp]
  · have hm : p ∉ FiniteSourceHardy.path n 0 x := by
      simp [FiniteSourceHardy.path, hp]
    simp [FiniteSourceHardy.value, e, lp.coeFn_single, Pi.single_apply, eq_comm, hm,
      Set.indicator_of_notMem hp]

private def kernel (m : Address → ℝ) (p q : Edge) : ℝ :=
  if p.val.IsPrefix q.val then m q.val else if q.val.IsPrefix p.val then m p.val else 0

private theorem prefix_inter (p q : Address) :
    {x : Address | p.IsPrefix x} ∩ {x | q.IsPrefix x} =
      if p.IsPrefix q then {x | q.IsPrefix x}
      else if q.IsPrefix p then {x | p.IsPrefix x} else ∅ := by
  classical
  split_ifs with hp hq
  · ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨hp.trans hx, hx⟩⟩
  · ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hq.trans hx⟩⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (List.prefix_or_prefix_of_prefix hx.1 hx.2).elim hp hq

private theorem cylinder_subset (p q : Address) (hp : p.IsPrefix q) :
    BiasedBoundaryTrace.cylinder q ⊆ BiasedBoundaryTrace.cylinder p := by
  intro ω hω i hi
  have hip := Finset.mem_range.mp hi
  have hiq := hip.trans_le hp.length_le
  have he := hω i (Finset.mem_range.mpr hiq)
  change ω i = p.getD i false
  change ω i = q.getD i false at he
  rw [he]
  simpa [List.getD_eq_getElem?_getD, hip, hiq] using (hp.getElem hip).symm

private theorem cylinder_common (p q : Address) (ω : BiasedBoundaryTrace.Omega)
    (hp : ω ∈ BiasedBoundaryTrace.cylinder p) (hq : ω ∈ BiasedBoundaryTrace.cylinder q) :
    p.IsPrefix q ∨ q.IsPrefix p := by
  have aux (p q : Address) (hp : ω ∈ BiasedBoundaryTrace.cylinder p)
      (hq : ω ∈ BiasedBoundaryTrace.cylinder q) (hl : p.length ≤ q.length) : p.IsPrefix q := by
    apply List.prefix_iff_getElem.mpr
    refine ⟨hl, ?_⟩
    intro i hi
    have hj := hi.trans_le hl
    have hi' := hp i (Finset.mem_range.mpr hi)
    have hj' := hq i (Finset.mem_range.mpr hj)
    simpa [List.getD_eq_getElem?_getD, hi, hj] using hi'.symm.trans hj'
  exact (le_total p.length q.length).elim
    (fun hl => Or.inl (aux p q hp hq hl)) (fun hl => Or.inr (aux q p hq hp hl))

private theorem boundary_inter (p q : Address) :
    BiasedBoundaryTrace.cylinder p ∩ BiasedBoundaryTrace.cylinder q =
      if p.IsPrefix q then BiasedBoundaryTrace.cylinder q
      else if q.IsPrefix p then BiasedBoundaryTrace.cylinder p else ∅ := by
  classical
  split_ifs with hp hq
  · exact Set.inter_eq_right.mpr (cylinder_subset p q hp)
  · exact Set.inter_eq_left.mpr (cylinder_subset q p hq)
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact (cylinder_common p q ω hω.1 hω.2).elim hp hq

private theorem mean_entry (n : ℕ) (p : Edge) : inner ℝ (e p) (v n) = FiniteSourceMass.mass n p.val := by
  rw [v, ContinuousLinearMap.adjoint_inner_right, finite_column]
  have he : inner ℝ (nodeIndicator n p) (one n) =
      (FiniteSourceMass.μ n {x | p.val.IsPrefix x.val}).toReal := by
    rw [nodeIndicator, L2.inner_indicatorConstLp_one]
    have hc : (one n : NodeL2 n) =ᵐ[FiniteSourceMass.μ n] (fun _ => (1 : ℝ)) :=
      (memLp_const (1 : ℝ)).coeFn_toLp
    rw [integral_congr_ae (hc.filter_mono (ae_mono Measure.restrict_le_self)), integral_const]
    simp [measureReal_def]
  exact he.trans (FiniteSourceMass.finite_source_masses.2.2.2.2.1 n p.val)

private theorem boundary_mean_entry (p : Edge) :
    inner ℝ (e p) BiasedBoundaryFreeRootForm.v = BiasedBoundaryTrace.mass p.val := by
  rw [BiasedBoundaryFreeRootForm.v, ContinuousLinearMap.adjoint_inner_right,
    BiasedBoundaryTrace.J_single, one_smul, real_inner_comm]
  change BiasedBoundaryCentering.mean (BiasedBoundaryTrace.indicator p) = _
  rw [BiasedBoundaryCentering.centered_suffix_residual.1]
  rw [BiasedBoundaryTrace.indicator, integral_indicatorConstLp]
  simpa using BiasedBoundaryTrace.cylinder_mass p.val

private theorem gram_entry (n : ℕ) (p q : Edge) :
    inner ℝ (e p) (B n (e q)) = kernel (FiniteSourceMass.mass n) p q := by
  rw [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    finite_column, finite_column, nodeIndicator, nodeIndicator,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
  have he := congrArg (fun s : Set Address => (Subtype.val : FiniteSourceMass.Node n → Address) ⁻¹' s)
    (prefix_inter p.val q.val)
  simp only [Set.preimage_inter, Set.preimage_setOf_eq, Set.preimage_ite, Set.preimage_empty] at he
  rw [he]
  unfold kernel
  split_ifs <;> simp [FiniteSourceMass.finite_source_masses.2.2.2.2.1, measureReal_def]

private theorem boundary_gram_entry (p q : Edge) :
    inner ℝ (e p) (BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J (e q)) =
      kernel BiasedBoundaryTrace.mass p q := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    BiasedBoundaryTrace.J_single, BiasedBoundaryTrace.J_single, one_smul, one_smul,
    BiasedBoundaryTrace.indicator, BiasedBoundaryTrace.indicator,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one, boundary_inter]
  unfold kernel
  split_ifs <;> simp [measureReal_def, BiasedBoundaryTrace.cylinder_mass]

private theorem kernel_limit (p q : Edge) :
    Tendsto (fun n => kernel (FiniteSourceMass.mass n) p q) atTop
      (𝓝 (kernel BiasedBoundaryTrace.mass p q)) := by
  classical
  unfold kernel
  split_ifs
  · exact mass_limit q.val
  · exact mass_limit p.val
  · exact tendsto_const_nhds

end D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance
