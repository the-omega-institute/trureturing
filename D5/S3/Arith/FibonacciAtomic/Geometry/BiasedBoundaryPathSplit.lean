/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Lp.lpSpace]
   utility: none
   digest: Strict suffix increments and the all-ell2 conditional path-sum identity. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw
import Mathlib.Data.List.Infix

/-! Splitting the original infinite path sum at an arbitrary finite prefix. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (Edge H)
open BiasedBoundaryTrace (Omega M cylinder G J indicator)
open BiasedBoundaryConditionalLaw (prepend pullback conditional_pullback_law)
open MeasureTheory Filter
open scoped BigOperators ENNReal

/-- Append a nonempty suffix, retaining the original edge coordinates. -/
def descendant (p : Address) (u : Edge) : Edge :=
  ⟨p ++ u.val, by simp [u.property]⟩

private theorem descendant_injective (p : Address) : Function.Injective (descendant p) := by
  intro u v h
  apply Subtype.ext
  exact List.append_cancel_left (congrArg Subtype.val h)

private def suffixLinear (p : Address) : H →ₗ[ℝ] H where
  toFun z := ⟨fun u => z (descendant p u), memℓp_gen
    (((lp.memℓp z).summable (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)).comp_injective
      (descendant_injective p))⟩
  map_add' z w := by ext u; rfl
  map_smul' c z := by ext u; rfl

private theorem suffix_norm (p : Address) (z : H) : ‖suffixLinear p z‖ ≤ ‖z‖ := by
  classical
  apply lp.norm_le_of_forall_sum_le (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
    (norm_nonneg z)
  intro s
  calc
    _ = ∑ q ∈ s.image (descendant p), ‖z q‖^(2:ℝ≥0∞).toReal := by
      rw [Finset.sum_image]
      · rfl
      · exact fun _ _ _ _ h => descendant_injective p h
    _ ≤ _ := lp.sum_rpow_le_norm_rpow (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) z _

/-- Restrict to strict descendants and remove their common prefix. -/
def S (p : Address) : H →L[ℝ] H :=
  (suffixLinear p).mkContinuous 1 (fun z => by simpa using suffix_norm p z)

/-- The nonempty original prefixes of p, including p when it is nonempty. -/
def prefixes (p : Address) : Finset Edge :=
  p.inits.toFinset.subtype (· ≠ [])

private theorem mem_prefixes (p : Address) (q : Edge) :
    q ∈ prefixes p ↔ q.val.IsPrefix p := by
  simp [prefixes, List.mem_inits]

/-- The finite prefix sum, as a bounded functional on the original H. -/
def prefixSum (p : Address) : H →L[ℝ] ℝ :=
  ∑ q ∈ prefixes p, lp.evalCLM ℝ (fun _ : Edge => ℝ) 2 q

/-- The actual constant function in the same L2(M) as J. -/
def constG : ℝ →L[ℝ] G :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (Lp.const 2 M (1 : ℝ))

private theorem constG_ae (c : ℝ) : constG c =ᵐ[M] (fun _ : Omega => c) := by
  filter_upwards [Lp.coeFn_smul c (Lp.const 2 M (1 : ℝ)),
    Lp.coeFn_const (μ := M) (p := 2) (1 : ℝ)] with ω hs hc
  change (c • Lp.const 2 M (1 : ℝ) : G) ω = c
  rw [hs]
  change c * (Lp.const 2 M (1 : ℝ)) ω = c
  rw [hc]
  simp

private theorem cylinder_prefix (q p : Address) (h : q.IsPrefix p) (ω : Omega) :
    prepend p ω ∈ cylinder q := by
  intro i hi
  have hiq := Finset.mem_range.mp hi
  have hip := hiq.trans_le h.length_le
  change (if i < p.length then p.getD i false else ω (i-p.length)) = q.getD i false
  simp only [hip, ite_true, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hip, List.getElem?_eq_getElem hiq, Option.getD_some]
  exact (h.getElem hiq).symm

private theorem prefix_of_cylinder (p q : Address) (ω : Omega)
    (h : prepend p ω ∈ cylinder q) (hl : q.length ≤ p.length) : q.IsPrefix p := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨hl, ?_⟩
  intro i hi
  have hip := hi.trans_le hl
  have he := h i (Finset.mem_range.mpr hi)
  change (if i < p.length then p.getD i false else ω (i-p.length)) = q.getD i false at he
  simpa only [hip, ite_true, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hip, List.getElem?_eq_getElem hi, Option.getD_some] using he.symm

private theorem cylinder_prepend_append (p u : Address) (ω : Omega) :
    prepend p ω ∈ cylinder (p++u) ↔ ω ∈ cylinder u := by
  constructor
  · intro h i hi
    have hiu := Finset.mem_range.mp hi
    have he := h (p.length+i) (Finset.mem_range.mpr (by simp; omega))
    have hh : ¬ p.length+i < p.length := by omega
    simpa [prepend, hh, List.getD_eq_getElem?_getD, List.getElem?_append] using he
  · intro h i hi
    have hi' := Finset.mem_range.mp hi
    by_cases hip : i < p.length
    · simp [prepend, hip, List.getD_eq_getElem?_getD, List.getElem?_append]
    · have hiu : i-p.length < u.length := by simp only [List.length_append] at hi'; omega
      have he := h (i-p.length) (Finset.mem_range.mpr hiu)
      simpa [prepend, hip, List.getD_eq_getElem?_getD, List.getElem?_append] using he

private theorem prepend_cylinder_long (p : Address) (q : Edge) (ω : Omega)
    (hl : p.length < q.val.length) (h : prepend p ω ∈ cylinder q.val) :
    p.IsPrefix q.val := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨hl.le, ?_⟩
  intro i hi
  have hiq := hi.trans hl
  have he := h i (Finset.mem_range.mpr hiq)
  change (if i < p.length then p.getD i false else ω (i-p.length)) = q.val.getD i false at he
  simpa only [prepend, hi, ite_true, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiq, Option.getD_some] using he

private theorem indicator_pullback_ae (p : Address) (q : Edge) :
    pullback p (indicator q) =ᵐ[M]
      (fun ω => (cylinder q.val).indicator (fun _ : Omega => (1 : ℝ)) (prepend p ω)) := by
  have hb : (indicator q : Omega → ℝ) =ᵐ[M]
      (cylinder q.val).indicator (fun _ : Omega => (1 : ℝ)) := indicatorConstLp_coeFn
  have hc : (indicator q : Omega → ℝ) =ᵐ[BiasedBoundaryConditionalLaw.conditional p]
      (cylinder q.val).indicator (fun _ : Omega => (1 : ℝ)) :=
    ae_smul_measure (ae_restrict_of_ae hb) _
  exact (conditional_pullback_law.2.2.2.2.1 p (indicator q)).trans
    ((conditional_pullback_law.2.2.1 p).quasiMeasurePreserving.ae_eq_comp hc)

private theorem pullback_indicator_prefix (p : Address) (q : Edge) (h : q.val.IsPrefix p) :
    pullback p (indicator q) = constG 1 := by
  apply Lp.ext
  filter_upwards [indicator_pullback_ae p q, constG_ae 1] with ω hi hc
  rw [hi, hc, Set.indicator_of_mem (cylinder_prefix q.val p h ω)]

private theorem pullback_indicator_descendant (p : Address) (u : Edge) :
    pullback p (indicator (descendant p u)) = indicator u := by
  apply Lp.ext
  have hu : (indicator u : Omega → ℝ) =ᵐ[M]
      (cylinder u.val).indicator (fun _ : Omega => (1 : ℝ)) := indicatorConstLp_coeFn
  filter_upwards [indicator_pullback_ae p (descendant p u), hu] with ω hi hj
  rw [hi, hj]
  simp only [descendant, Set.indicator, cylinder_prepend_append]

private theorem pullback_indicator_incomparable (p : Address) (q : Edge)
    (hqp : ¬ q.val.IsPrefix p) (hpq : ¬ p.IsPrefix q.val) :
    pullback p (indicator q) = 0 := by
  apply Lp.ext
  filter_upwards [indicator_pullback_ae p q, Lp.coeFn_zero ℝ 2 M] with ω hi hz
  rw [hi, hz]
  apply Set.indicator_of_notMem
  intro h
  by_cases hl : q.val.length ≤ p.length
  · exact hqp (prefix_of_cylinder p q.val ω h hl)
  · exact hpq (prepend_cylinder_long p q ω (Nat.lt_of_not_ge hl) h)

private theorem J_single (q : Edge) (c : ℝ) : J (lp.single 2 q c) = c • indicator q := by
  have hs := BiasedBoundaryTrace.boundary_trace_hardy.1 (lp.single 2 q c)
  rw [← hs.tsum_eq]
  simp only [lp.coeFn_single, Pi.single_apply, ite_smul, zero_smul]
  simp

private theorem prefixSum_single (p : Address) (q : Edge) (c : ℝ) :
    prefixSum p (lp.single 2 q c) = if q.val.IsPrefix p then c else 0 := by
  classical
  change (∑ u ∈ prefixes p, (lp.single 2 q c : H) u) = _
  simp [lp.coeFn_single, Pi.single_apply, mem_prefixes]

private theorem suffix_single_descendant (p : Address) (q : Edge) (c : ℝ) :
    S p (lp.single 2 (descendant p q) c) = lp.single 2 q c := by
  ext u
  change (lp.single 2 (descendant p q) c : H) (descendant p u) =
    (lp.single 2 q c : H) u
  simp [lp.coeFn_single, Pi.single_apply, (descendant_injective p).eq_iff]

private theorem suffix_single_of_not_prefix (p : Address) (q : Edge) (c : ℝ)
    (h : ¬ p.IsPrefix q.val) : S p (lp.single 2 q c) = 0 := by
  ext u
  change (lp.single 2 q c : H) (descendant p u) = 0
  apply lp.single_apply_ne
  intro he
  apply h
  have he' := congrArg Subtype.val he
  change p++u.val = q.val at he'
  rw [← he']
  exact List.prefix_append _ _

private theorem suffix_single_prefix (p : Address) (q : Edge) (c : ℝ)
    (h : q.val.IsPrefix p) : S p (lp.single 2 q c) = 0 := by
  ext u
  change (lp.single 2 q c : H) (descendant p u) = 0
  apply lp.single_apply_ne
  intro he
  have he' := congrArg (fun r : Edge => r.val.length) he
  have hu : 0 < u.val.length := List.length_pos_of_ne_nil u.property
  have hq := h.length_le
  simp only [descendant, List.length_append] at he'
  omega

/-- Every original ell2 increment vector splits into its finite prefix value and
the trace of its strict descendants, in the same suffix L2(M), including p=[]. -/
theorem boundary_path_split :
    (∀ (p : Address) (z : H) (u : Edge), S p z u = z (descendant p u)) ∧
    (∀ (p : Address) (z : H), ‖S p z‖ ≤ ‖z‖) ∧
    (∀ (p : Address) (z : H),
      prefixSum p z = ∑ u ∈ prefixes p, z u) ∧
    (∀ c : ℝ, constG c =ᵐ[M] (fun _ : Omega => c)) ∧
    (∀ (p : Address) (z : H),
      pullback p (J z) = constG (prefixSum p z) + J (S p z)) := by
  refine ⟨fun _ _ _ => rfl, suffix_norm, (fun _ _ => rfl), constG_ae, ?_⟩
  intro p z
  have he : (pullback p).comp J = constG.comp (prefixSum p) + J.comp (S p) := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro q
    ext c
    change pullback p (J (lp.single 2 q c)) =
      constG (prefixSum p (lp.single 2 q c)) + J (S p (lp.single 2 q c))
    rw [J_single, map_smul, prefixSum_single]
    by_cases hqp : q.val.IsPrefix p
    · rw [if_pos hqp, suffix_single_prefix p q c hqp, map_zero, add_zero,
        pullback_indicator_prefix p q hqp]
      simp [constG]
    · rw [if_neg hqp, map_zero, zero_add]
      by_cases hpq : p.IsPrefix q.val
      · obtain ⟨u, hu⟩ := hpq
        have hun : u ≠ [] := by
          intro hh
          apply hqp
          rw [← hu, hh, List.append_nil]
        let v : Edge := ⟨u, hun⟩
        have heq : q = descendant p v := Subtype.ext hu.symm
        rw [heq, suffix_single_descendant, J_single, pullback_indicator_descendant]
      · rw [suffix_single_of_not_prefix p q c hpq, map_zero,
          pullback_indicator_incomparable p q hqp hpq, smul_zero]
  exact DFunLike.congr_fun he z

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit
