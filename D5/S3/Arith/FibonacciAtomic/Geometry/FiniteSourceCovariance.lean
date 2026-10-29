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
    simp only [div_pow, inv_pow, pow_succ]
    generalize hx : Real.goldenRatio = x
    generalize hy : Real.goldenConj = y
    have hx0 : x ≠ 0 := hx ▸ Real.goldenRatio_ne_zero
    have hs0 : Real.sqrt 5 ≠ 0 := by positivity
    field_simp [hx0, hs0]
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
    cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true,
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

private theorem inner_e_right (z : H) (p : Edge) : inner ℝ z (e p) = z p := by
  rw [real_inner_comm]
  exact inner_e p z

private def block (h : ℕ) : Finset Edge :=
  ((List.finite_length_le Bool h).toFinset).subtype (· ≠ [])

private theorem mem_block (h : ℕ) (p : Edge) : p ∈ block h ↔ p.val.length ≤ h := by
  classical
  simp [block]

theorem P_expand (h : ℕ) (z : H) : P h z = ∑ p ∈ block h, z p • e p := by
  classical
  ext q
  change (if q.val.length ≤ h then z q else 0) =
    (lp.evalCLM ℝ (fun _ : Edge => ℝ) 2 q) (∑ p ∈ block h, z p • e p)
  rw [map_sum]
  change (if q.val.length ≤ h then z q else 0) =
    ∑ p ∈ block h, z p * (e p) q
  simp [e, lp.coeFn_single, Pi.single_apply, mul_ite, mem_block, eq_comm]

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
  rw [hr, hU] at ha
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
      Set.indicator, hp]
  · have hm : p ∉ FiniteSourceHardy.path n 0 x := by
      simp [FiniteSourceHardy.path, hp]
    simp [FiniteSourceHardy.value, e, lp.coeFn_single, Pi.single_apply, eq_comm, hm,
      Set.indicator, hp]

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
  unfold e
  rw [BiasedBoundaryFreeRootForm.v, ContinuousLinearMap.adjoint_inner_right,
    BiasedBoundaryTrace.J_single, one_smul, real_inner_comm]
  change BiasedBoundaryCentering.mean (BiasedBoundaryTrace.indicator p) = _
  rw [BiasedBoundaryFreeRootForm.mean_indicator]
  simpa only [measureReal_def] using BiasedBoundaryTrace.cylinder_mass p.val

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
  unfold e
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

private def dK (h : ℕ) : ℝ := Real.sqrt (2*Real.goldenRatio*a^(h+1)/(1-a))
private def d1 (h : ℕ) : ℝ := Real.sqrt (a^(h+1)/(1-a))

private theorem finite_tail (n h : ℕ) :
    ‖(FiniteSourceHardy.J n).comp (ContinuousLinearMap.id ℝ H-P h)‖ ≤ dK h :=
  FiniteSourceHardy.finite_source_hardy.2.2 n h

private theorem boundary_tail (h : ℕ) :
    ‖BiasedBoundaryTrace.J.comp (ContinuousLinearMap.id ℝ H-P h)‖ ≤ d1 h := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro z
  have hc : 0 ≤ a^(h+1)/(1-a) := by
    exact div_nonneg (pow_nonneg BiasedBoundaryTrace.a_pos.le _) (sub_pos.mpr BiasedBoundaryTrace.a_lt_one).le
  have hs := Real.sqrt_le_sqrt (BiasedBoundaryTrace.boundary_trace_hardy.2 h z)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, Real.sqrt_mul hc, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), d1] using hs

private theorem finite_bound (n : ℕ) : ‖FiniteSourceHardy.J n‖ ≤ dK 0 := by
  simpa [P_zero] using finite_tail n 0

private theorem boundary_bound : ‖BiasedBoundaryTrace.J‖ ≤ d1 0 := by
  simpa [P_zero] using boundary_tail 0

private theorem one_norm (n : ℕ) : ‖one n‖ = 1 := by
  change ‖Lp.const 2 (FiniteSourceMass.μ n) (1 : ℝ)‖ = 1
  simpa using Lp.norm_const (μ := FiniteSourceMass.μ n) (p := 2) (c := (1 : ℝ)) (by norm_num)

private theorem tail_difference {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [CompleteSpace G] (A : H →L[ℝ] G) (h : ℕ) :
    A - A.comp (P h) = A.comp (ContinuousLinearMap.id ℝ H-P h) := by
  ext z
  simp

private theorem mean_expansion {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [CompleteSpace G] (A : H →L[ℝ] G) (g : G) (h : ℕ) :
    (A.comp (P h)).adjoint g = ∑ p ∈ block h, inner ℝ (A (e p)) g • e p := by
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [P_expand, map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, real_inner_comm, inner_e, inner_e_right, mul_comm]

private theorem gram_expansion {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [CompleteSpace G] (A : H →L[ℝ] G) (h : ℕ) :
    (A.comp (P h)).adjoint.comp (A.comp (P h)) =
      ∑ p ∈ block h, ∑ q ∈ block h,
        inner ℝ (A (e p)) (A (e q)) • rankOne ℝ (e p) (e q) := by
  classical
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  simp only [ContinuousLinearMap.comp_apply, P_expand, map_sum, map_smul,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right, rankOne_apply,
    inner_e, inner_e_right, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    Finset.mul_sum, Finset.sum_mul]
  simp only [RCLike.conj_to_real, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ring

private theorem mean_cutoff_bound {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [CompleteSpace G] (A : H →L[ℝ] G) (g : G) (h : ℕ) :
    ‖A.adjoint g-(A.comp (P h)).adjoint g‖ ≤
      ‖A.comp (ContinuousLinearMap.id ℝ H-P h)‖*‖g‖ := by
  calc
    _ = ‖(A-A.comp (P h)).adjoint g‖ := by simp
    _ ≤ ‖(A-A.comp (P h)).adjoint‖*‖g‖ := ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [LinearIsometryEquiv.norm_map, tail_difference]

private theorem gram_cutoff_bound {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [CompleteSpace G] (A : H →L[ℝ] G) (h : ℕ) :
    ‖A.adjoint.comp A-(A.comp (P h)).adjoint.comp (A.comp (P h))‖ ≤
      2*‖A‖*‖A.comp (ContinuousLinearMap.id ℝ H-P h)‖ := by
  have hid : A.adjoint.comp A-(A.comp (P h)).adjoint.comp (A.comp (P h)) =
      A.adjoint.comp (A-A.comp (P h)) +
      (A-A.comp (P h)).adjoint.comp (A.comp (P h)) := by
    ext z
    simp
  have hb : ‖A.comp (P h)‖ ≤ ‖A‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (P_norm h) (norm_nonneg A)).trans_eq (mul_one _))
  rw [hid]
  calc
    _ ≤ ‖A.adjoint.comp (A-A.comp (P h))‖ +
        ‖(A-A.comp (P h)).adjoint.comp (A.comp (P h))‖ := norm_add_le _ _
    _ ≤ ‖A‖*‖A-A.comp (P h)‖+‖A-A.comp (P h)‖*‖A.comp (P h)‖ := by
      simpa only [LinearIsometryEquiv.norm_map] using add_le_add
        (ContinuousLinearMap.opNorm_comp_le A.adjoint (A-A.comp (P h)))
        (ContinuousLinearMap.opNorm_comp_le (A-A.comp (P h)).adjoint (A.comp (P h)))
    _ ≤ ‖A‖*‖A-A.comp (P h)‖+‖A-A.comp (P h)‖*‖A‖ := by gcongr
    _ = _ := by rw [tail_difference]; ring

private def meanBlock (m : Address → ℝ) (h : ℕ) : H := ∑ p ∈ block h, m p.val • e p
private def gramBlock (m : Address → ℝ) (h : ℕ) : H →L[ℝ] H :=
  ∑ p ∈ block h, ∑ q ∈ block h, kernel m p q • rankOne ℝ (e p) (e q)

private theorem finite_mean_block (n h : ℕ) :
    ((FiniteSourceHardy.J n).comp (P h)).adjoint (one n) = meanBlock (FiniteSourceMass.mass n) h := by
  have hm (p : Edge) : inner ℝ (FiniteSourceHardy.J n (e p)) (one n) =
      FiniteSourceMass.mass n p.val := by
    simpa only [v, ContinuousLinearMap.adjoint_inner_right] using mean_entry n p
  simpa only [meanBlock, hm] using mean_expansion (FiniteSourceHardy.J n) (one n) h

private theorem boundary_mean_block (h : ℕ) :
    (BiasedBoundaryTrace.J.comp (P h)).adjoint (BiasedBoundaryPathSplit.constG 1) =
      meanBlock BiasedBoundaryTrace.mass h := by
  have hm (p : Edge) : inner ℝ (BiasedBoundaryTrace.J (e p)) (BiasedBoundaryPathSplit.constG 1) =
      BiasedBoundaryTrace.mass p.val := by
    simpa only [BiasedBoundaryFreeRootForm.v, ContinuousLinearMap.adjoint_inner_right]
      using boundary_mean_entry p
  simpa only [meanBlock, hm] using
    mean_expansion BiasedBoundaryTrace.J (BiasedBoundaryPathSplit.constG 1) h

private theorem finite_gram_block (n h : ℕ) :
    ((FiniteSourceHardy.J n).comp (P h)).adjoint.comp ((FiniteSourceHardy.J n).comp (P h)) =
      gramBlock (FiniteSourceMass.mass n) h := by
  have hg (p q : Edge) : inner ℝ (FiniteSourceHardy.J n (e p)) (FiniteSourceHardy.J n (e q)) =
      kernel (FiniteSourceMass.mass n) p q := by
    simpa only [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
      using gram_entry n p q
  simpa only [gramBlock, hg] using gram_expansion (FiniteSourceHardy.J n) h

private theorem boundary_gram_block (h : ℕ) :
    (BiasedBoundaryTrace.J.comp (P h)).adjoint.comp (BiasedBoundaryTrace.J.comp (P h)) =
      gramBlock BiasedBoundaryTrace.mass h := by
  have hg (p q : Edge) : inner ℝ (BiasedBoundaryTrace.J (e p)) (BiasedBoundaryTrace.J (e q)) =
      kernel BiasedBoundaryTrace.mass p q := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
      using boundary_gram_entry p q
  simpa only [gramBlock, hg] using gram_expansion BiasedBoundaryTrace.J h

private theorem mean_block_limit (h : ℕ) :
    Tendsto (fun n => meanBlock (FiniteSourceMass.mass n) h) atTop
      (𝓝 (meanBlock BiasedBoundaryTrace.mass h)) := by
  exact tendsto_finsetSum _ (fun p _ => (mass_limit p.val).smul_const (e p))

private theorem gram_block_limit (h : ℕ) :
    Tendsto (fun n => gramBlock (FiniteSourceMass.mass n) h) atTop
      (𝓝 (gramBlock BiasedBoundaryTrace.mass h)) := by
  exact tendsto_finsetSum _ (fun p _ => tendsto_finsetSum _
    (fun q _ => (kernel_limit p q).smul_const (rankOne ℝ (e p) (e q))))

private theorem actual_cutoff_error (n h : ℕ) :
    ‖v n-BiasedBoundaryFreeRootForm.v‖ ≤ dK h+d1 h+
      ‖meanBlock (FiniteSourceMass.mass n) h-meanBlock BiasedBoundaryTrace.mass h‖ ∧
    ‖B n-BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J‖ ≤
      2*dK 0*dK h+2*d1 0*d1 h+
      ‖gramBlock (FiniteSourceMass.mass n) h-gramBlock BiasedBoundaryTrace.mass h‖ := by
  have hmn : ‖v n-meanBlock (FiniteSourceMass.mass n) h‖ ≤ dK h := by
    rw [← finite_mean_block]
    exact (mean_cutoff_bound (FiniteSourceHardy.J n) (one n) h).trans
      (by rw [one_norm, mul_one]; exact finite_tail n h)
  have hmb : ‖BiasedBoundaryFreeRootForm.v-meanBlock BiasedBoundaryTrace.mass h‖ ≤ d1 h := by
    rw [← boundary_mean_block]
    exact (mean_cutoff_bound BiasedBoundaryTrace.J (BiasedBoundaryPathSplit.constG 1) h).trans
      (by rw [BiasedBoundaryCentering.constG_norm_one, mul_one]; exact boundary_tail h)
  have hgn : ‖B n-gramBlock (FiniteSourceMass.mass n) h‖ ≤ 2*dK 0*dK h := by
    rw [← finite_gram_block]
    exact (gram_cutoff_bound (FiniteSourceHardy.J n) h).trans (by
      have := finite_bound n
      have := finite_tail n h
      dsimp [dK] at *
      gcongr)
  have hgb : ‖BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J-
      gramBlock BiasedBoundaryTrace.mass h‖ ≤ 2*d1 0*d1 h := by
    rw [← boundary_gram_block]
    exact (gram_cutoff_bound BiasedBoundaryTrace.J h).trans (by
      have := boundary_bound
      have := boundary_tail h
      dsimp [d1] at *
      gcongr)
  constructor
  · have ht := norm_add₃_le (a := v n-meanBlock (FiniteSourceMass.mass n) h)
      (b := meanBlock (FiniteSourceMass.mass n) h-meanBlock BiasedBoundaryTrace.mass h)
      (c := meanBlock BiasedBoundaryTrace.mass h-BiasedBoundaryFreeRootForm.v)
    rw [show v n-meanBlock (FiniteSourceMass.mass n) h+
      (meanBlock (FiniteSourceMass.mass n) h-meanBlock BiasedBoundaryTrace.mass h)+
      (meanBlock BiasedBoundaryTrace.mass h-BiasedBoundaryFreeRootForm.v) =
      v n-BiasedBoundaryFreeRootForm.v by abel, norm_sub_rev (meanBlock BiasedBoundaryTrace.mass h) BiasedBoundaryFreeRootForm.v] at ht
    linarith
  · have ht := norm_add₃_le (a := B n-gramBlock (FiniteSourceMass.mass n) h)
      (b := gramBlock (FiniteSourceMass.mass n) h-gramBlock BiasedBoundaryTrace.mass h)
      (c := gramBlock BiasedBoundaryTrace.mass h-BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J)
    rw [show B n-gramBlock (FiniteSourceMass.mass n) h+
      (gramBlock (FiniteSourceMass.mass n) h-gramBlock BiasedBoundaryTrace.mass h)+
      (gramBlock BiasedBoundaryTrace.mass h-BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J) =
      B n-BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J by abel, norm_sub_rev (gramBlock BiasedBoundaryTrace.mass h)
      (BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J)] at ht
    linarith

private theorem tails_limit :
    Tendsto dK atTop (𝓝 0) ∧ Tendsto d1 atTop (𝓝 0) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one BiasedBoundaryTrace.a_pos.le
    BiasedBoundaryTrace.a_lt_one).comp (tendsto_add_atTop_nat 1)
  constructor
  · change Tendsto (fun h => Real.sqrt (2*Real.goldenRatio*a^(h+1)/(1-a))) atTop (𝓝 0)
    simpa only [Function.comp_def, mul_zero, zero_div, Real.sqrt_zero] using
      ((hp.const_mul (2*Real.goldenRatio)).div_const (1-a)).sqrt
  · change Tendsto (fun h => Real.sqrt (a^(h+1)/(1-a))) atTop (𝓝 0)
    simpa only [Function.comp_def, zero_div, Real.sqrt_zero] using (hp.div_const (1-a)).sqrt

private theorem first_two_limits :
    Tendsto v atTop (𝓝 BiasedBoundaryFreeRootForm.v) ∧
    Tendsto B atTop (𝓝 (BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J)) := by
  have hvm := tails_limit.1.add tails_limit.2
  have hbg := (tails_limit.1.const_mul (2*dK 0)).add (tails_limit.2.const_mul (2*d1 0))
  constructor
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hv := (Metric.tendsto_atTop.mp hvm) (ε/2) (by positivity)
    obtain ⟨h, hh⟩ := hv
    have hh' : dK h+d1 h < ε/2 := by
      have ht : |dK h+d1 h| < ε/2 := by
        simpa only [zero_add, dist_zero_right, Real.norm_eq_abs] using hh h le_rfl
      exact (le_abs_self _).trans_lt ht
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (mean_block_limit h)) (ε/2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hc := (actual_cutoff_error n h).1
    have hm := hN n hn
    rw [dist_eq_norm] at hm ⊢
    linarith
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨h, hh⟩ := (Metric.tendsto_atTop.mp hbg) (ε/2) (by positivity)
    have hh' : 2*dK 0*dK h+2*d1 0*d1 h < ε/2 := by
      have ht : |2*dK 0*dK h+2*d1 0*d1 h| < ε/2 := by
        simpa only [mul_zero, zero_add, dist_zero_right, Real.norm_eq_abs] using hh h le_rfl
      exact (le_abs_self _).trans_lt ht
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (gram_block_limit h)) (ε/2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hc := (actual_cutoff_error n h).2
    have hm := hN n hn
    rw [dist_eq_norm] at hm ⊢
    linarith

set_option maxHeartbeats 1000000 in
-- The actual lp operators and the simultaneous dependent source family share this budget.
/-- The three actual source objects converge simultaneously on the common H.
The node L2 codomains of the maps J(n) retain their dependence on n. -/
theorem finite_source_covariance_convergence :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ‖v n-BiasedBoundaryFreeRootForm.v‖ < ε ∧
      ‖B n-BiasedBoundaryTrace.J.adjoint.comp BiasedBoundaryTrace.J‖ < ε ∧
      ‖Sigma n-BiasedBoundaryFreeRootForm.Sigma‖ < ε := by
  have hv := first_two_limits.1
  have hB := first_two_limits.2
  have hr : Tendsto (fun n => rankOne ℝ (v n) (v n)) atTop
      (𝓝 (rankOne ℝ BiasedBoundaryFreeRootForm.v BiasedBoundaryFreeRootForm.v)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hd : Tendsto (fun n => ‖v n-BiasedBoundaryFreeRootForm.v‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using (hv.sub_const BiasedBoundaryFreeRootForm.v).norm
    have hb := (hd.mul hv.norm).add (hd.const_mul ‖BiasedBoundaryFreeRootForm.v‖)
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using hb)
    intro n
    have he : rankOne ℝ (v n) (v n)-
        rankOne ℝ BiasedBoundaryFreeRootForm.v BiasedBoundaryFreeRootForm.v =
        rankOne ℝ (v n-BiasedBoundaryFreeRootForm.v) (v n)+
        rankOne ℝ BiasedBoundaryFreeRootForm.v (v n-BiasedBoundaryFreeRootForm.v) := by
      simp
    rw [he]
    simpa only [norm_rankOne] using norm_add_le
      (rankOne ℝ (v n-BiasedBoundaryFreeRootForm.v) (v n))
      (rankOne ℝ BiasedBoundaryFreeRootForm.v (v n-BiasedBoundaryFreeRootForm.v))

  have hs : Tendsto Sigma atTop (𝓝 BiasedBoundaryFreeRootForm.Sigma) := by
    rw [BiasedBoundaryFreeRootForm.actual_compact_covariance.2.2.2.1]
    exact hB.sub hr
  intro ε hε
  obtain ⟨Nv, hNv⟩ := Metric.tendsto_atTop.mp hv ε hε
  obtain ⟨NB, hNB⟩ := Metric.tendsto_atTop.mp hB ε hε
  obtain ⟨NS, hNS⟩ := Metric.tendsto_atTop.mp hs ε hε
  refine ⟨max Nv (max NB NS), fun n hn => ?_⟩
  exact ⟨by simpa only [dist_eq_norm] using hNv n ((le_max_left _ _).trans hn),
    by simpa only [dist_eq_norm] using hNB n ((le_max_left NB NS).trans ((le_max_right _ _).trans hn)),
    by simpa only [dist_eq_norm] using hNS n ((le_max_right NB NS).trans ((le_max_right _ _).trans hn))⟩

end D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance
