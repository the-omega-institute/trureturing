/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Self-adjoint realization of the actual infinite biased free-root form. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import D5.S3.Quantum.Analysis.CompactEigenbasis
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Order.SuccPred.LinearLocallyFinite
import Mathlib.Order.Interval.Finset.Basic

/-! The original form is realized on the actual infinite biased boundary. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (H Edge)
open BiasedBoundaryTrace (G Omega M J cylinder indicator J_single cylinder_measurable)
open BiasedBoundaryPathSplit (constG)
open BiasedBoundaryStopping (G0 Threshold A Vt Vt0 actual_stopping_partition actual_stopping_residual)
open BiasedBoundaryCentering (mean Pi C centered_suffix_residual)
open BiasedBoundaryFreeRootForm
  (D form weakGraph free_root_variational_graph mean_Pi Pi_idem inner_centered
    Sigma K adjoint_mem_K)
open MeasureTheory hiding cylinder
open Filter
open scoped Topology ENNReal

private theorem cylinder_subset_of_common (p q : Address) (ω : Omega)
    (hp : ω ∈ cylinder p) (hq : ω ∈ cylinder q) (hl : p.length ≤ q.length) :
    cylinder q ⊆ cylinder p := by
  intro x hx i hi
  have hiq : i ∈ Finset.range q.length :=
    Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hl)
  exact (hx i hiq).trans ((hq i hiq).symm.trans (hp i hi))

private theorem cylinders_pi : IsPiSystem (Set.range cylinder) := by
  rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩ hne
  obtain ⟨ω,hp,hq⟩ := hne
  rcases le_total p.length q.length with hl | hl
  · exact ⟨q, (Set.inter_eq_right.mpr (cylinder_subset_of_common p q ω hp hq hl)).symm⟩
  · exact ⟨p, (Set.inter_eq_left.mpr (cylinder_subset_of_common q p ω hq hp hl)).symm⟩

private theorem ofFn_getD {n : ℕ} (w : Fin n → Bool) (j : ℕ) (hj : j < n) :
    (List.ofFn w).getD j false = w ⟨j,hj⟩ := by
  have hh : j < (List.ofFn w).length := by simpa only [List.length_ofFn] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh,
    Option.getD_some, List.getElem_ofFn]

private theorem cylinders_generate :
    (inferInstance : MeasurableSpace Omega) =
      MeasurableSpace.generateFrom (Set.range cylinder) := by
  apply le_antisymm
  · change MeasurableSpace.pi ≤ _
    apply iSup_le
    intro i
    letI : MeasurableSpace Omega := MeasurableSpace.generateFrom (Set.range cylinder)
    apply Measurable.comap_le
    apply measurable_to_countable'
    intro c
    have hs : (fun ω : Omega => ω i) ⁻¹' {c} =
        ⋃ (w : Fin (i+1) → Bool) (_ : w ⟨i, Nat.lt_succ_self i⟩ = c),
          cylinder (List.ofFn w) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
      constructor
      · intro h
        refine ⟨(fun j => ω j),h,?_⟩
        intro j hj
        have hj' : j < i+1 := by simpa using hj
        change ω j = (List.ofFn (fun k : Fin (i+1) => ω k)).getD j false
        rw [ofFn_getD _ j hj']
      · rintro ⟨w,hw,hω⟩
        have hh := hω i (Finset.mem_range.mpr (by simp))
        change ω i = (List.ofFn w).getD i false at hh
        rw [ofFn_getD w i (Nat.lt_succ_self i)] at hh
        exact hh.trans hw
    rw [hs]
    apply MeasurableSet.iUnion
    intro w
    apply MeasurableSet.iUnion
    intro hw
    exact MeasurableSpace.measurableSet_generateFrom ⟨List.ofFn w,rfl⟩
  · exact MeasurableSpace.generateFrom_le (by rintro _ ⟨p,rfl⟩; exact cylinder_measurable p)

private theorem integral_cylinder_of_adjoint_zero (h : G) (hh : J.adjoint h = 0)
    (p : Edge) : (∫ ω in cylinder p.val, h ω ∂M) = 0 := by
  rw [← L2.inner_indicatorConstLp_one (cylinder_measurable p.val) (measure_ne_top _ _) h]
  change inner ℝ (indicator p) h = 0
  have he := J.adjoint_inner_right (lp.single 2 p (1:ℝ)) h
  rw [hh, inner_zero_right, J_single, one_smul] at he
  exact he.symm

private theorem J_adjoint_injective : Function.Injective J.adjoint := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm ?_ bot_le
  intro h hh
  change h = 0
  change J.adjoint h = 0 at hh
  have hfi : Integrable h M := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      integrableOn_Lp_of_measure_ne_top (s := Set.univ) h (by norm_num) (measure_ne_top _ _)
  have hi : ∀ p : Edge, (∫ ω in cylinder p.val, h ω ∂M) = 0 :=
    integral_cylinder_of_adjoint_zero h hh
  have hu : (∫ ω, h ω ∂M) = 0 := by
    have he : cylinder [false] ∪ cylinder [true] = Set.univ := by
      ext ω
      simp [cylinder, Set.mem_pi, Finset.mem_range, Nat.lt_one_iff, Bool.eq_false_or_eq_true (ω 0)]
    have hd : Disjoint (cylinder [false]) (cylinder [true]) := by
      apply Set.disjoint_left.mpr
      intro ω hf ht
      have hf' := hf 0 (by simp)
      have ht' := ht 0 (by simp)
      simp at hf' ht'
      exact Bool.false_ne_true (hf'.symm.trans ht')
    have hs := setIntegral_union hd (cylinder_measurable [true])
      hfi.integrableOn hfi.integrableOn
    rw [he, setIntegral_univ, hi ⟨[false],by simp⟩, hi ⟨[true],by simp⟩, add_zero] at hs
    exact hs
  have hc : ∀ p : Address, (∫ ω in cylinder p, h ω ∂M) = 0 := by
    intro p
    by_cases hp : p = []
    · subst p
      simpa [cylinder] using hu
    · exact hi ⟨p,hp⟩
  have hv : M.withDensityᵥ h = 0 := by
    apply VectorMeasure.ext_of_generateFrom (Set.range cylinder)
    · rintro _ ⟨p,rfl⟩
      rw [withDensityᵥ_apply hfi (cylinder_measurable p), hc]
      rfl
    · exact cylinders_generate
    · exact cylinders_pi
    · rw [withDensityᵥ_apply hfi MeasurableSet.univ, setIntegral_univ, hu]
      rfl
  have hz : h =ᵐ[M] (0 : Omega → ℝ) := by
    apply hfi.ae_eq_zero_of_forall_setIntegral_eq_zero
    intro s hs hμ
    have he := congrArg (fun v : VectorMeasure Omega ℝ => v s) hv
    rw [withDensityᵥ_apply hfi hs] at he
    exact he
  exact Lp.ext (hz.trans (Lp.coeFn_zero ℝ 2 M).symm)

private theorem J_dense : DenseRange J := by
  have hk : J.adjoint.ker = ⊥ := LinearMap.ker_eq_bot.mpr J_adjoint_injective
  have ht : J.range.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, J.orthogonal_range, hk,
      Submodule.bot_orthogonal_eq_top]
  change ∀ F : G, F ∈ closure (Set.range J)
  have he : (J.range : Set G) = Set.range J := rfl
  rw [← he, ← Submodule.topologicalClosure_coe, ht]
  exact fun _ => Set.mem_univ _

private def Pi0 : G →L[ℝ] G0 := Pi.codRestrict G0 mean_Pi

/-- The original centered trace with its specified mean-zero codomain. -/
def centeredTrace : H →L[ℝ] G0 := Pi0.comp J

private theorem centeredTrace_dense : DenseRange centeredTrace := by
  have hp : Function.Surjective Pi0 := by
    intro F
    refine ⟨F.val,?_⟩
    apply Subtype.ext
    change Pi F.val = F.val
    rw [centered_suffix_residual.2.2.1,show mean F.val = 0 from F.property,map_zero,sub_zero]
  exact hp.denseRange.comp J_dense Pi0.continuous

private theorem G0_infinite : ¬ FiniteDimensional ℝ G0 := by
  intro hfd
  letI := hfd
  let d := Module.finrank ℝ G0
  let t : Threshold := ⟨1/((d:ℝ)+2),by positivity,by
    apply (div_lt_one (by positivity : 0 < (d:ℝ)+2)).mpr
    have hd : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith⟩
  rcases actual_stopping_partition t with ⟨_,_,_,_,_,_,_,hl,_⟩
  have hcR : (d:ℝ)+2 ≤ ((A t).card:ℝ) := by simpa only [t,one_div_one_div] using hl
  have hcN : d+2 ≤ (A t).card := by exact_mod_cast hcR
  let f : Vt0 t →ₗ[ℝ] G0 := {
    toFun := fun F => ⟨F.val.val,F.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro F T he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : G0 => x.val) he))
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  have hr := (actual_stopping_residual t).2.2.2.2.2.2.2.2.2.2.1
  change Module.finrank ℝ (Vt0 t) = (A t).card-1 at hr
  rw [hr] at hd
  change (A t).card-1 ≤ d at hd
  omega

private theorem Pi_adjoint : Pi.adjoint = Pi :=
  (isSelfAdjoint_starProjection (ℝ ∙ constG 1)ᗮ).adjoint_eq

private theorem C_adjoint (h : G) : C.adjoint h = J.adjoint (Pi h) := by
  rw [C, ContinuousLinearMap.adjoint_comp, Pi_adjoint]
  rfl

private theorem C_adjoint_zero {h : G} (hh : mean h = 0)
    (hz : C.adjoint h = 0) : h = 0 := by
  have he : Pi h = h := by
    rw [centered_suffix_residual.2.2.1,hh,map_zero,sub_zero]
  rw [C_adjoint, he] at hz
  exact J_adjoint_injective (hz.trans (map_zero J.adjoint).symm)

/-- The actual boundary covariance CC*, on the fixed biased L2 space. -/
def boundaryCovariance : G →L[ℝ] G := C.comp C.adjoint

private theorem covariance_centered (h : G) : mean (boundaryCovariance h) = 0 :=
  mean_Pi (J (C.adjoint h))

private theorem covariance_Pi (h : G) : boundaryCovariance (Pi h) = boundaryCovariance h := by
  change C (C.adjoint (Pi h)) = C (C.adjoint h)
  rw [C_adjoint, C_adjoint, Pi_idem]

private theorem covariance_inner (h k : G) :
    inner ℝ (boundaryCovariance h) k = inner ℝ (C.adjoint h) (C.adjoint k) :=
  (C.adjoint_inner_right (C.adjoint h) k).symm

private theorem covariance_symmetric (h k : G) :
    inner ℝ (boundaryCovariance h) k = inner ℝ h (boundaryCovariance k) := by
  calc
    _ = inner ℝ (C.adjoint h) (C.adjoint k) := covariance_inner h k
    _ = inner ℝ (C.adjoint k) (C.adjoint h) := real_inner_comm _ _
    _ = inner ℝ (boundaryCovariance k) h := (covariance_inner k h).symm
    _ = _ := real_inner_comm _ _

private theorem covariance_injective_centered {h : G} (hh : mean h = 0)
    (hz : boundaryCovariance h = 0) : h = 0 := by
  apply C_adjoint_zero hh
  have he := covariance_inner h h
  rw [hz,inner_zero_left] at he
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp he.symm

private def operatorGraph : Submodule ℝ (G × G) where
  carrier := {x | mean x.2 = 0 ∧ Pi x.1 = boundaryCovariance x.2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change mean (x.2+y.2) = 0 ∧ Pi (x.1+y.1) = boundaryCovariance (x.2+y.2)
    simp only [map_add,hx.1,hy.1,add_zero,hx.2,hy.2,and_self]
  smul_mem' := by
    intro c x hx
    change mean (c • x.2) = 0 ∧ Pi (c • x.1) = boundaryCovariance (c • x.2)
    simp only [map_smul,hx.1,hx.2,smul_zero,and_self]

private theorem graph_single : ∀ x : G × G, x ∈ operatorGraph → x.1 = 0 → x.2 = 0 := by
  intro x hx hx0
  apply covariance_injective_centered hx.1
  rw [← hx.2, hx0, map_zero]

/-- The operator whose graph is the entire original free-root variational graph. -/
def boundaryOperator : G →ₗ.[ℝ] G := operatorGraph.toLinearPMap

private theorem operator_graph : boundaryOperator.graph = operatorGraph :=
  operatorGraph.toLinearPMap_graph_eq graph_single

private theorem graph_weak (u h : G) : (u,h) ∈ operatorGraph ↔ weakGraph u h := by
  rw [free_root_variational_graph.2.2.2.2.2 u h]
  change (mean h = 0 ∧ Pi u = boundaryCovariance h) ↔ _
  constructor
  · rintro ⟨hh,hu⟩
    refine ⟨hh,?_⟩
    change u = constG (mean u)+boundaryCovariance h
    rw [← hu,centered_suffix_residual.2.2.1]
    abel
  · rintro ⟨hh,hu⟩
    refine ⟨hh,?_⟩
    rw [hu,map_add,BiasedBoundaryCentering.Pi_const,zero_add]
    change Pi (Pi (J (C.adjoint h))) = Pi (J (C.adjoint h))
    exact Pi_idem _

private theorem graph_constant (c : ℝ) : (constG c,0) ∈ operatorGraph := by
  change mean 0 = 0 ∧ Pi (constG c) = boundaryCovariance 0
  rw [map_zero, BiasedBoundaryCentering.Pi_const, map_zero]
  exact ⟨rfl,rfl⟩

private theorem graph_covariance (h : G) : (boundaryCovariance h,Pi h) ∈ operatorGraph := by
  change mean (Pi h) = 0 ∧ Pi (boundaryCovariance h) = boundaryCovariance (Pi h)
  constructor
  · exact mean_Pi h
  · rw [covariance_Pi,centered_suffix_residual.2.2.1,covariance_centered,map_zero,sub_zero]

private theorem operator_domain_dense : Dense (boundaryOperator.domain : Set G) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hk : boundaryOperator.domainᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro h hh
    change h = 0
    have hh' : ∀ x : G, x ∈ boundaryOperator.domain → inner ℝ x h = 0 := hh
    have hc : constG 1 ∈ boundaryOperator.domain := by
      apply LinearPMap.mem_domain_of_mem_graph
      rw [operator_graph]
      exact graph_constant 1
    have hm : mean h = 0 := by
      change inner ℝ (constG 1) h = 0
      exact hh' (constG 1) hc
    apply covariance_injective_centered hm
    apply ext_inner_left ℝ
    intro k
    have hd : boundaryCovariance k ∈ boundaryOperator.domain := by
      apply LinearPMap.mem_domain_of_mem_graph
      rw [operator_graph]
      exact graph_covariance k
    rw [inner_zero_right,← covariance_symmetric]
    exact hh' _ hd
  rw [← Submodule.orthogonal_orthogonal_eq_closure,hk,Submodule.bot_orthogonal_eq_top]

private theorem operator_graph_adjoint : operatorGraph.adjoint = operatorGraph := by
  apply Submodule.ext
  rintro ⟨u,h⟩
  rw [Submodule.mem_adjoint_iff]
  change (∀ a b : G, (a,b) ∈ operatorGraph → inner ℝ b u-inner ℝ a h = 0) ↔
    (mean h = 0 ∧ Pi u = boundaryCovariance h)
  constructor
  · intro hw
    have hm : mean h = 0 := by
      have he := hw (constG 1) 0 (graph_constant 1)
      change inner ℝ (constG 1) h = 0
      simpa only [inner_zero_left,zero_sub,neg_eq_zero] using he
    refine ⟨hm,?_⟩
    apply ext_inner_left ℝ
    intro k
    have he := sub_eq_zero.mp (hw (boundaryCovariance k) (Pi k) (graph_covariance k))
    have hp : inner ℝ (Pi k) u = inner ℝ k (Pi u) := by
      exact (Pi.adjoint_inner_right k u).symm.trans
        (congrArg (fun T : G →L[ℝ] G => inner ℝ k (T u)) Pi_adjoint)
    rw [hp,covariance_symmetric] at he
    exact he
  · rintro ⟨hm,hu⟩ a b hab
    have hb : mean b = 0 := hab.1
    have ha : Pi a = boundaryCovariance b := hab.2
    have hu' : inner ℝ b u = inner ℝ b (boundaryCovariance h) := by
      rw [← hu, inner_centered b u hb]
    rw [hu', ← covariance_symmetric, ← ha]
    have he : inner ℝ (Pi a) h = inner ℝ a h := by
      rw [real_inner_comm,inner_centered h a hm,real_inner_comm]
    rw [he,sub_self]

private theorem operator_self_adjoint : IsSelfAdjoint boundaryOperator := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint operator_domain_dense,
    operator_graph, operator_graph_adjoint]

/-- The self-adjoint realization is constructed from the exact original weak
form, with dense domain and precisely the constant zero modes. -/
theorem actual_self_adjoint_realization :
    DenseRange J ∧ DenseRange centeredTrace ∧ ¬ FiniteDimensional ℝ G0 ∧
    Dense (D : Set G) ∧
    Dense (boundaryOperator.domain : Set G) ∧ IsSelfAdjoint boundaryOperator ∧
    (∀ u h : G, (u,h) ∈ boundaryOperator.graph ↔ weakGraph u h) ∧
    (∀ u : G, (u,0) ∈ boundaryOperator.graph ↔ ∃ c : ℝ, u = constG c) := by
  refine ⟨J_dense, centeredTrace_dense, G0_infinite, ?_, operator_domain_dense, operator_self_adjoint, ?_, ?_⟩
  · apply J_dense.mono
    rintro _ ⟨z,rfl⟩
    exact ⟨0,z,by simp⟩
  · intro u h
    rw [operator_graph]
    exact graph_weak u h
  · intro u
    rw [operator_graph]
    constructor
    · intro hu
      refine ⟨mean u,?_⟩
      have he := hu.2
      rw [map_zero,centered_suffix_residual.2.2.1,sub_eq_zero] at he
      exact he
    · rintro ⟨c,rfl⟩
      exact graph_constant c

private def shift : G →L[ℝ] G := 1 + boundaryCovariance

private theorem shift_unit : IsUnit shift := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map shift (c := 1) (by norm_num)
  intro x
  change ‖x‖^2 * (1 : ℝ) ≤ ‖inner ℝ (x + boundaryCovariance x) x‖
  rw [inner_add_left,covariance_inner,real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg ‖C.adjoint x‖]

private theorem shift_bijective : Function.Bijective shift :=
  ContinuousLinearMap.isUnit_iff_bijective.mp shift_unit

private def shiftEquiv : G ≃L[ℝ] G :=
  ContinuousLinearEquiv.ofBijective shift
    (LinearMap.ker_eq_bot.mpr shift_bijective.1)
    (LinearMap.range_eq_top.mpr shift_bijective.2)

private def inverseShift : G →L[ℝ] G := shiftEquiv.symm.toContinuousLinearMap

private theorem shift_inverse (f : G) : shift (inverseShift f) = f :=
  shiftEquiv.apply_symm_apply f

/-- The bounded inverse of I+H, constructed from the actual boundary covariance. -/
def boundaryResolvent : G →L[ℝ] G :=
  constG.comp mean + boundaryCovariance.comp inverseShift

private theorem covariance_const (c : ℝ) : boundaryCovariance (constG c) = 0 := by
  rw [← covariance_Pi,BiasedBoundaryCentering.Pi_const,map_zero]

private theorem shift_resolvent (f : G) :
    shift (boundaryResolvent f) = constG (mean f) + boundaryCovariance f := by
  have ht : inverseShift f + boundaryCovariance (inverseShift f) = f := shift_inverse f
  have ha : boundaryCovariance (inverseShift f) +
      boundaryCovariance (boundaryCovariance (inverseShift f)) = boundaryCovariance f := by
    rw [← map_add,ht]
  change (constG (mean f)+boundaryCovariance (inverseShift f)) +
    boundaryCovariance (constG (mean f)+boundaryCovariance (inverseShift f)) = _
  rw [map_add,covariance_const,zero_add,← ha]
  abel

private theorem graph_shift (u h : G) (hh : (u,h) ∈ operatorGraph) :
    shift u = constG (mean (u+h)) + boundaryCovariance (u+h) := by
  have hm : mean h = 0 := hh.1
  have hu : Pi u = boundaryCovariance h := hh.2
  change u + boundaryCovariance u = _
  rw [map_add,hm,add_zero,map_add,← hu,centered_suffix_residual.2.2.1]
  abel

private theorem graph_of_shift {u f : G}
    (he : shift u = constG (mean f)+boundaryCovariance f) :
    (u,f-u) ∈ operatorGraph := by
  have hm := congrArg mean he
  change mean (u+boundaryCovariance u) = mean (constG (mean f)+boundaryCovariance f) at hm
  rw [map_add,covariance_centered,add_zero,map_add,
    centered_suffix_residual.2.1,covariance_centered,add_zero] at hm
  change mean (f-u) = 0 ∧ Pi u = boundaryCovariance (f-u)
  constructor
  · rw [map_sub,hm,sub_self]
  · rw [map_sub,centered_suffix_residual.2.2.1,hm]
    apply sub_eq_sub_iff_add_eq_add.mpr
    change u+boundaryCovariance u = boundaryCovariance f+constG (mean f)
    exact he.trans (add_comm _ _)

private theorem resolvent_inverse (u h : G) :
    (u,h) ∈ boundaryOperator.graph ↔ boundaryResolvent (u+h) = u := by
  rw [operator_graph]
  constructor
  · intro hh
    apply shift_bijective.1
    rw [shift_resolvent]
    exact (graph_shift u h hh).symm
  · intro he
    have hg := graph_of_shift (shift_resolvent (u+h))
    simpa only [he,add_sub_cancel_left] using hg

private theorem resolvent_compact : IsCompactOperator boundaryResolvent := by
  have hp : IsCompactOperator (constG.comp mean) :=
    (isCompactOperator_of_locallyCompactSpace_rng constG).comp_clm mean
  have ha : IsCompactOperator boundaryCovariance :=
    BiasedBoundaryFreeRootForm.actual_compact_covariance.2.1.comp_clm C.adjoint
  exact hp.add (ha.comp_clm inverseShift)

private theorem inverse_eigenvalue (lam : ℝ) (hlam : 0 < lam) (u : G) :
    (u,lam • u) ∈ boundaryOperator.graph ↔
      mean u = 0 ∧ boundaryCovariance u = lam⁻¹ • u := by
  rw [operator_graph]
  change (mean (lam • u) = 0 ∧ Pi u = boundaryCovariance (lam • u)) ↔ _
  constructor
  · rintro ⟨hm,he⟩
    have hm' : mean u = 0 := by
      rw [map_smul,smul_eq_mul] at hm
      exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt hlam)
    refine ⟨hm',?_⟩
    have he' : u = lam • boundaryCovariance u := by
      simpa only [centered_suffix_residual.2.2.1,hm',map_zero,sub_zero,map_smul] using he
    have hs := congrArg (fun x : G => lam⁻¹ • x) he'
    simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt hlam),one_smul] using hs.symm
  · rintro ⟨hm,he⟩
    constructor
    · rw [map_smul,hm,smul_zero]
    · rw [centered_suffix_residual.2.2.1,hm,map_zero,sub_zero,
        map_smul,he,smul_smul,mul_inv_cancel₀ (ne_of_gt hlam),one_smul]

/-- Compact resolvent and exact inverse eigenvalue equation for the original
operator; this does not assume a polar realization or a spectral counting field. -/
theorem actual_compact_resolvent :
    IsCompactOperator boundaryResolvent ∧
    (∀ u h : G, (u,h) ∈ boundaryOperator.graph ↔ boundaryResolvent (u+h) = u) ∧
    (∀ (lam : ℝ), 0 < lam → ∀ u : G,
      (u,lam • u) ∈ boundaryOperator.graph ↔
        mean u = 0 ∧ boundaryCovariance u = lam⁻¹ • u) :=
  ⟨resolvent_compact,resolvent_inverse,inverse_eigenvalue⟩

/-- The genuine eigenspace of the partially defined original boundary operator. -/
def boundaryEigenspace (lam : ℝ) : Submodule ℝ G :=
  boundaryOperator.graph.comap ((LinearMap.id : G →ₗ[ℝ] G).prod (lam • LinearMap.id))

private theorem eigen_covariance (mu : ℝ) (hmu : 0 < mu)
    (u : boundaryEigenspace mu⁻¹) : boundaryCovariance u.val = mu • u.val := by
  have hu : (u.val,mu⁻¹ • u.val) ∈ boundaryOperator.graph := u.property
  simpa only [inv_inv] using
    ((inverse_eigenvalue mu⁻¹ (inv_pos.mpr hmu) u.val).mp hu).2

private theorem eigen_forward (mu : ℝ) (hmu : 0 < mu)
    (z : Module.End.eigenspace Sigma.toLinearMap mu) :
    C z.val ∈ boundaryEigenspace mu⁻¹ := by
  change (C z.val,mu⁻¹ • C z.val) ∈ boundaryOperator.graph
  apply (inverse_eigenvalue mu⁻¹ (inv_pos.mpr hmu) (C z.val)).mpr
  refine ⟨mean_Pi _,?_⟩
  have hz : Sigma z.val = mu • z.val := Module.End.mem_eigenspace_iff.mp z.property
  change C (Sigma z.val) = (mu⁻¹)⁻¹ • C z.val
  rw [hz,map_smul,inv_inv]

private theorem eigen_backward (mu : ℝ) (hmu : 0 < mu)
    (u : boundaryEigenspace mu⁻¹) :
    mu⁻¹ • C.adjoint u.val ∈ Module.End.eigenspace Sigma.toLinearMap mu := by
  apply Module.End.mem_eigenspace_iff.mpr
  change Sigma (mu⁻¹ • C.adjoint u.val) = mu • (mu⁻¹ • C.adjoint u.val)
  rw [map_smul]
  change mu⁻¹ • C.adjoint (boundaryCovariance u.val) = _
  rw [eigen_covariance mu hmu u,map_smul,smul_smul,smul_smul,
    inv_mul_cancel₀ (ne_of_gt hmu),mul_inv_cancel₀ (ne_of_gt hmu)]

/-- The original trace identifies the complete positive edge and boundary
operator eigenspaces, with an explicit inverse and no simplicity assumption. -/
def covarianceEigenEquiv (mu : ℝ) (hmu : 0 < mu) :
    Module.End.eigenspace Sigma.toLinearMap mu ≃ₗ[ℝ] boundaryEigenspace mu⁻¹ where
  toFun z := ⟨C z.val,eigen_forward mu hmu z⟩
  invFun u := ⟨mu⁻¹ • C.adjoint u.val,eigen_backward mu hmu u⟩
  left_inv z := by
    apply Subtype.ext
    have hz : Sigma z.val = mu • z.val := Module.End.mem_eigenspace_iff.mp z.property
    change mu⁻¹ • Sigma z.val = z.val
    rw [hz,smul_smul,
      inv_mul_cancel₀ (ne_of_gt hmu),one_smul]
  right_inv u := by
    apply Subtype.ext
    change C (mu⁻¹ • C.adjoint u.val) = u.val
    rw [map_smul]
    change mu⁻¹ • boundaryCovariance u.val = u.val
    rw [eigen_covariance mu hmu u,smul_smul,inv_mul_cancel₀ (ne_of_gt hmu),one_smul]
  map_add' z w := by apply Subtype.ext; exact map_add C z.val w.val
  map_smul' c z := by apply Subtype.ext; exact map_smul C c z.val

private theorem edge_eigen_bound (mu : ℝ)
    (z : Module.End.eigenspace Sigma.toLinearMap mu) (hz : z.val ≠ 0) :
    mu ≤ Real.goldenRatio := by
  have hs : BiasedBoundaryPathSplit.S [] z.val = z.val := by ext p; rfl
  have hb := centered_suffix_residual.2.2.2.2.2 [] z.val
  rw [centered_suffix_residual.2.2.2.2.1,hs] at hb
  have hze : Sigma z.val = mu • z.val := Module.End.mem_eigenspace_iff.mp z.property
  have he := BiasedBoundaryFreeRootForm.actual_compact_covariance.2.2.2.2.2.1 z.val
  rw [hze,inner_smul_right,real_inner_self_eq_norm_sq] at he
  rw [← he] at hb
  have hn : 0 < ‖z.val‖^2 := pow_pos (norm_pos_iff.mpr hz) 2
  exact (mul_le_mul_iff_left₀ hn).mp (by simpa only [mul_comm] using hb)

private theorem operator_eigen_gap (mu : ℝ) (hmu : 0 < mu)
    (u : boundaryEigenspace mu⁻¹) (hu : u.val ≠ 0) :
    Real.goldenRatio⁻¹ ≤ mu⁻¹ := by
  have hz : ((covarianceEigenEquiv mu hmu).symm u).val ≠ 0 := by
    intro h0
    have he : (covarianceEigenEquiv mu hmu).symm u = 0 := Subtype.ext h0
    have hu0 : u = 0 := by
      simpa only [LinearEquiv.apply_symm_apply,map_zero] using
        congrArg (covarianceEigenEquiv mu hmu) he
    exact hu (congrArg Subtype.val hu0)
  have hb := edge_eigen_bound mu ((covarianceEigenEquiv mu hmu).symm u) hz
  simpa only [one_div] using one_div_le_one_div_of_le hmu hb

/-- Positive original covariance eigenvectors lie in K. The actual trace gives
inverse eigenvalues and preserves the full finite eigenspace multiplicities. -/
theorem actual_covariance_eigenspaces (mu : ℝ) (hmu : 0 < mu) :
    (∀ z : Module.End.eigenspace Sigma.toLinearMap mu, z.val ∈ K) ∧
    (∀ z : Module.End.eigenspace Sigma.toLinearMap mu,
      (covarianceEigenEquiv mu hmu z).val = C z.val) ∧
    (∀ u : boundaryEigenspace mu⁻¹,
      ((covarianceEigenEquiv mu hmu).symm u).val = mu⁻¹ • C.adjoint u.val) ∧
    FiniteDimensional ℝ (boundaryEigenspace mu⁻¹) ∧
    (∀ z : Module.End.eigenspace Sigma.toLinearMap mu, z.val ≠ 0 → mu ≤ Real.goldenRatio) ∧
    (∀ u : boundaryEigenspace mu⁻¹, u.val ≠ 0 → Real.goldenRatio⁻¹ ≤ mu⁻¹) := by
  refine ⟨?_,fun _ => rfl,fun _ => rfl,?_,edge_eigen_bound mu,operator_eigen_gap mu hmu⟩
  · intro z
    have hz : Sigma z.val = mu • z.val := Module.End.mem_eigenspace_iff.mp z.property
    have he : z.val = mu⁻¹ • C.adjoint (C z.val) := by
      change z.val = mu⁻¹ • Sigma z.val
      rw [hz,smul_smul,inv_mul_cancel₀ (ne_of_gt hmu),one_smul]
    rw [he]
    exact K.smul_mem _ (adjoint_mem_K _)
  · letI : FiniteDimensional ℝ (Module.End.eigenspace Sigma.toLinearMap mu) :=
      ContinuousLinearMap.finite_dimensional_eigenspace
        BiasedBoundaryFreeRootForm.actual_compact_covariance.2.2.1 mu (ne_of_gt hmu)
    exact (covarianceEigenEquiv mu hmu).finiteDimensional

private instance : CompleteSpace G0 :=
  (ContinuousLinearMap.isClosed_ker mean).completeSpace_coe

private instance : CompleteSpace K :=
  (Submodule.isClosed_orthogonal Sigma.ker).completeSpace_coe

private def covariance0 : G0 →L[ℝ] G0 :=
  (boundaryCovariance.comp G0.subtypeL).codRestrict G0 (fun u => covariance_centered u)

private theorem covariance0_coe (u : G0) : (covariance0 u).val = boundaryCovariance u.val := rfl

private theorem covariance0_compact : IsCompactOperator covariance0 := by
  exact (BiasedBoundaryFreeRootForm.actual_compact_covariance.2.1.comp_clm C.adjoint
    |>.comp_clm G0.subtypeL).codRestrict (fun u => covariance_centered u)
      (ContinuousLinearMap.isClosed_ker mean)

private theorem covariance0_symmetric : covariance0.IsSymmetric := by
  intro u v
  exact covariance_symmetric u.val v.val

private theorem covariance0_positive (u : G0) (hu : u ≠ 0) :
    0 < inner ℝ u (covariance0 u) := by
  have hn : C.adjoint u.val ≠ 0 := by
    intro he
    exact hu (Subtype.ext (C_adjoint_zero u.property he))
  change 0 < inner ℝ u.val (boundaryCovariance u.val)
  rw [real_inner_comm, covariance_inner, real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr hn) 2

private theorem covariance0_basis :
    ∃ (w : Set G0) (b : HilbertBasis w ℝ G0) (mu : w → ℝ),
      (∀ i, 0 < mu i) ∧ (∀ i, covariance0 (b i) = mu i • b i) := by
  obtain ⟨w,b,mu,he⟩ :=
    D5.S3.Quantum.Analysis.CompactEigenbasis.exists_setIndex_real_eigenbasis_rclike
      covariance0_compact covariance0_symmetric
  refine ⟨w,b,mu,?_,he⟩
  intro i
  exact eigenvalue_pos_of_pos
    (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (he i),b.orthonormal.ne_zero i⟩)
    covariance0_positive

private theorem covariance_basis_finite_above {ι : Type} (b : HilbertBasis ι ℝ G0)
    (mu : ι → ℝ) (he : ∀ i, covariance0 (b i) = mu i • b i)
    (eps : ℝ) (heps : 0 < eps) : {i | eps ≤ mu i}.Finite := by
  classical
  by_contra hf
  letI : Infinite {i // eps ≤ mu i} := Set.infinite_coe_iff.mpr hf
  let k := Infinite.natEmbedding {i // eps ≤ mu i}
  let f : ℕ → G0 := fun n => covariance0 (b (k n).val)
  obtain ⟨L,hL,hsub⟩ := covariance0_compact.image_closedBall_subset_compact 1
  have hfL (n : ℕ) : f n ∈ L := by
    apply hsub
    exact ⟨b (k n).val,by simp [Metric.mem_closedBall,b.orthonormal.1],rfl⟩
  obtain ⟨x,_,phi,hphi,hlim⟩ := hL.tendsto_subseq hfL
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq eps heps
  have hd := hN N le_rfl (N+1) (Nat.le_succ N)
  have hne : (k (phi N)).val ≠ (k (phi (N+1))).val := by
    intro heq
    have hh := k.injective (Subtype.ext heq)
    exact (ne_of_lt (hphi (Nat.lt_succ_self N))) hh
  have hn : ‖f (phi N)-f (phi (N+1))‖^2 =
      (mu (k (phi N)).val)^2 + (mu (k (phi (N+1))).val)^2 := by
    dsimp only [f]
    rw [he,he,norm_sub_sq_real,norm_smul,norm_smul,
      real_inner_smul_left,real_inner_smul_right,b.orthonormal.2 hne,
      b.orthonormal.1,b.orthonormal.1]
    simp [Real.norm_eq_abs,sq_abs]
  have ha := (k (phi N)).property
  have hb := (k (phi (N+1))).property
  change dist (f (phi N)) (f (phi (N+1))) < eps at hd
  rw [dist_eq_norm] at hd
  nlinarith [norm_nonneg (f (phi N)-f (phi (N+1)))]

private theorem ordered_covariance_indices {ι : Type} [Infinite ι]
    (b : HilbertBasis ι ℝ G0) (mu : ι → ℝ) (hp : ∀ i, 0 < mu i)
    (he : ∀ i, covariance0 (b i) = mu i • b i) :
    ∃ e : ℕ ≃ ι, Antitone (mu ∘ e) ∧ Tendsto (mu ∘ e) atTop (nhds 0) := by
  classical
  let baseOrder : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  letI : LinearOrder ι := baseOrder
  let key : ι → ℝᵒᵈ ×ₗ ι := fun i => toLex (mu i,i)
  have hkey : Function.Injective key := by
    intro i j h
    exact congrArg (fun x : ℝᵒᵈ ×ₗ ι => (ofLex x).2) h
  letI : LinearOrder ι := LinearOrder.lift' key hkey
  have hm (i j : ι) (hij : i ≤ j) : mu j ≤ mu i :=
    @Prod.Lex.monotone_fst ℝᵒᵈ ι inferInstance baseOrder.toLE (key i) (key j) hij
  have hf (i : ι) : (Set.Iic i).Finite := by
    apply (covariance_basis_finite_above b mu he (mu i) (hp i)).subset
    intro j hj
    exact hm j i hj
  letI : LocallyFiniteOrderBot ι := LocallyFiniteOrderBot.ofIic ι
    (fun i => (hf i).toFinset) (fun i j => by simp)
  letI : OrderBot ι := WellFoundedLT.toOrderBot ι
  letI : LocallyFiniteOrder ι := LocallyFiniteOrder.ofFiniteIcc
    (fun _ j => (hf j).subset (fun _ h => h.2))
  letI : SuccOrder ι := LinearLocallyFiniteOrder.succOrder ι
  letI : PredOrder ι := LinearLocallyFiniteOrder.predOrder ι
  letI : NoMaxOrder ι := ⟨fun i => by
    by_contra h
    push_neg at h
    have hall : (Set.univ : Set ι).Finite := (hf i).subset (fun j _ => h j)
    exact Set.infinite_univ hall⟩
  let e : ℕ ≃o ι := (orderIsoNatOfLinearSuccPredArch).symm
  refine ⟨e.toEquiv,fun i j hij => hm _ _ (e.monotone hij),?_⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans (hp (e n)))
  · intro eps heps
    have hfin := (covariance_basis_finite_above b mu he eps heps).preimage
      e.injective.injOn
    have hco : ∀ᶠ n : ℕ in cofinite, ¬ eps ≤ mu (e n) :=
      Filter.eventually_cofinite.mpr (by simpa only [not_not,Set.preimage_setOf_eq] using hfin)
    change ∀ᶠ n : ℕ in atTop, mu (e n) < eps
    simpa only [Nat.cofinite_eq_atTop,not_le] using hco

private theorem ordered_boundary_basis :
    ∃ (b : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ),
      (∀ i, 0 < mu i) ∧ Antitone mu ∧ Tendsto mu atTop (nhds 0) ∧
      (∀ i, covariance0 (b i) = mu i • b i) := by
  classical
  obtain ⟨w,b,mu,hp,he⟩ := covariance0_basis
  haveI : Infinite w := by
    by_contra h
    haveI : Finite w := not_infinite_iff_finite.mp h
    letI := Fintype.ofFinite w
    exact G0_infinite b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  obtain ⟨e,hm,ht⟩ := ordered_covariance_indices b mu hp he
  let f : ℕ → G0 := fun i => b (e i)
  have ho : Orthonormal ℝ f := b.orthonormal.comp e e.injective
  have hd : ⊤ ≤ (Submodule.span ℝ (Set.range f)).topologicalClosure := by
    rw [show Set.range f = Set.range b from e.surjective.range_comp b]
    exact b.dense_span.ge
  let B := HilbertBasis.mk ho hd
  have hB (i : ℕ) : B i = b (e i) := congrFun (HilbertBasis.coe_mk ho hd) i
  refine ⟨B,mu ∘ e,fun i => hp (e i),hm,ht,?_⟩
  intro i
  simpa only [hB,Function.comp_apply] using he (e i)

private theorem covariance0_eigenspace_span (b : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (he : ∀ i, covariance0 (b i) = mu i • b i) (a : ℝ) (ha : 0 < a) :
    Module.End.eigenspace covariance0.toLinearMap a =
      Submodule.span ℝ (b '' {i | mu i = a}) := by
  classical
  let S : Set ℕ := {i | mu i = a}
  have hS : S.Finite := (covariance_basis_finite_above b mu he a ha).subset
    (fun i hi => le_of_eq hi.symm)
  let V := Submodule.span ℝ (b '' S)
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (hS.image b)
  apply le_antisymm
  · intro u hu
    have hu' : covariance0 u = a • u := Module.End.mem_eigenspace_iff.mp hu
    have hcoeff (i : ℕ) (hi : mu i ≠ a) : b.repr u i = 0 := by
      have hh := covariance0_symmetric (b i) u
      change inner ℝ (covariance0 (b i)) u = inner ℝ (b i) (covariance0 u) at hh
      rw [he,hu',real_inner_smul_left,real_inner_smul_right] at hh
      rw [← b.repr_apply_apply] at hh
      exact (mul_eq_zero.mp (by nlinarith [hh] : (mu i-a)*b.repr u i = 0)).resolve_left
        (sub_ne_zero.mpr hi)
    apply V.closed_of_finiteDimensional.mem_of_tendsto (b.hasSum_repr u)
    apply Eventually.of_forall
    intro t
    apply Submodule.sum_mem
    intro i hi
    by_cases hm : mu i = a
    · exact V.smul_mem _ (Submodule.subset_span ⟨i,hm,rfl⟩)
    · rw [hcoeff i hm,zero_smul]
      exact V.zero_mem
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change covariance0 (b i) = a • b i
    rw [he,hi]

private def covariance0EigenEquiv (a : ℝ) (ha : 0 < a) :
    Module.End.eigenspace covariance0.toLinearMap a ≃ₗ[ℝ] boundaryEigenspace a⁻¹ where
  toFun u := ⟨u.val.val,by
    apply (inverse_eigenvalue a⁻¹ (inv_pos.mpr ha) u.val.val).mpr
    refine ⟨u.val.property,?_⟩
    have hh : covariance0 u.val = a • u.val := Module.End.mem_eigenspace_iff.mp u.property
    simpa only [inv_inv,covariance0_coe,Submodule.coe_smul] using congrArg Subtype.val hh⟩
  invFun v := ⟨⟨v.val,((inverse_eigenvalue a⁻¹ (inv_pos.mpr ha) v.val).mp v.property).1⟩,by
    apply Module.End.mem_eigenspace_iff.mpr
    apply Subtype.ext
    change boundaryCovariance v.val = a • v.val
    simpa only [inv_inv] using
      ((inverse_eigenvalue a⁻¹ (inv_pos.mpr ha) v.val).mp v.property).2⟩
  left_inv _ := by rfl
  right_inv _ := by rfl
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

private theorem spectral_multiplicity (b : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (he : ∀ i, covariance0 (b i) = mu i • b i) (a : ℝ) (ha : 0 < a) :
    Module.finrank ℝ (boundaryEigenspace a⁻¹) = Nat.card {i // mu i = a} := by
  classical
  let S : Set ℕ := {i | mu i = a}
  have hS : S.Finite := (covariance_basis_finite_above b mu he a ha).subset
    (fun i hi => le_of_eq hi.symm)
  letI := hS.fintype
  have hr : Set.range (fun i : S => b i.val) = b '' S := by
    ext u
    simp only [Set.mem_range,Set.mem_image]
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
  rw [← (covariance0EigenEquiv a ha).finrank_eq,covariance0_eigenspace_span b mu he a ha,← hr]
  calc
    _ = Fintype.card S := by
      simpa only [Function.comp_def] using
        (finrank_span_eq_card (b.orthonormal.linearIndependent.comp
          (fun i : S => i.val) Subtype.val_injective))
    _ = Nat.card {i // mu i = a} := Nat.card_eq_fintype_card.symm

private theorem paired_edge_basis (b : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (he : ∀ i, covariance0 (b i) = mu i • b i) :
    ∃ k : HilbertBasis ℕ ℝ K,
      (∀ i, Sigma (k i).val = mu i • (k i).val) ∧
      (∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) := by
  classical
  let z : ℕ → K := fun i =>
    ⟨(Real.sqrt (mu i))⁻¹ • C.adjoint (b i).val,
      K.smul_mem _ (adjoint_mem_K _)⟩
  have hs (i : ℕ) : Real.sqrt (mu i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hp i))
  have hev (i : ℕ) : boundaryCovariance (b i).val = mu i • (b i).val :=
    congrArg Subtype.val (he i)
  have hC (i : ℕ) : C (z i).val = Real.sqrt (mu i) • (b i).val := by
    change C ((Real.sqrt (mu i))⁻¹ • C.adjoint (b i).val) = _
    rw [map_smul]
    change (Real.sqrt (mu i))⁻¹ • boundaryCovariance (b i).val = _
    rw [hev,smul_smul]
    congr 1
    apply (inv_mul_eq_iff_eq_mul₀ (hs i)).mpr
    exact (Real.sq_sqrt (hp i).le).symm.trans (pow_two _)
  have ho : Orthonormal ℝ z := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℝ ((Real.sqrt (mu i))⁻¹ • C.adjoint (b i).val)
      ((Real.sqrt (mu j))⁻¹ • C.adjoint (b j).val) = _
    rw [real_inner_smul_left,real_inner_smul_right,← covariance_inner,hev,
      real_inner_smul_left]
    by_cases hij : i = j
    · subst j
      have hnorm : inner ℝ (b i).val (b i).val = 1 := by
        change inner ℝ (b i) (b i) = 1
        rw [real_inner_self_eq_norm_sq,b.orthonormal.1]
        norm_num
      simp only [hnorm,ite_true,mul_one]
      have hsq := Real.sq_sqrt (hp i).le
      field_simp [hs i] <;> nlinarith [hsq]
    · have hz : inner ℝ (b i).val (b j).val = 0 := b.orthonormal.2 hij
      simp only [hz,mul_zero,ite_false,hij]
  have htotal : (Submodule.span ℝ (Set.range z))ᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hz (i : ℕ) : inner ℝ x.val (C.adjoint (b i).val) = 0 := by
      have hi := (Submodule.mem_orthogonal' _ x).mp hx (z i)
        (Submodule.subset_span (Set.mem_range_self i))
      change inner ℝ x.val ((Real.sqrt (mu i))⁻¹ • C.adjoint (b i).val) = 0 at hi
      rw [real_inner_smul_right,mul_eq_zero] at hi
      exact hi.resolve_left (inv_ne_zero (hs i))
    have hzero : centeredTrace x.val = 0 := by
      apply b.repr.injective
      ext i
      rw [map_zero,lp.coeFn_zero,Pi.zero_apply,b.repr_apply_apply]
      change inner ℝ (b i).val (C x.val) = 0
      rw [real_inner_comm,← C.adjoint_inner_right]
      exact hz i
    have hc : C x.val = 0 := congrArg Subtype.val hzero
    have hk : x.val ∈ Sigma.ker := by
      change C.adjoint (C x.val) = 0
      rw [hc,map_zero]
    have hxzero : x.val = 0 :=
      (inner_self_eq_zero (𝕜 := ℝ)).mp (x.property x.val hk)
    exact Subtype.ext hxzero
  let B := HilbertBasis.mkOfOrthogonalEqBot ho htotal
  have hB (i : ℕ) : B i = z i := congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot ho htotal) i
  refine ⟨B,?_,fun i => by rw [hB]; exact hC i⟩
  intro i
  rw [hB]
  change C.adjoint (C (z i).val) = mu i • (z i).val
  rw [hC,map_smul]
  change Real.sqrt (mu i) • C.adjoint (b i).val =
    mu i • ((Real.sqrt (mu i))⁻¹ • C.adjoint (b i).val)
  rw [smul_smul]
  congr 1
  apply (eq_mul_inv_iff_mul_eq₀ (hs i)).mpr
  exact (pow_two _).symm.trans (Real.sq_sqrt (hp i).le)

/-- Complete ordered positive modes of the original free-root boundary operator.
The Hilbert basis is constructed on the actual mean-zero space, and the graph
condition includes the original, unaltered operator domain. -/
theorem actual_positive_spectral_exhaustion :
    ∃ (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ),
      (∀ i, 0 < mu i) ∧ Antitone mu ∧ Tendsto mu atTop (nhds 0) ∧
      Monotone (fun i => (mu i)⁻¹) ∧
      Tendsto (fun i => (mu i)⁻¹) atTop atTop ∧
      (∀ i, boundaryCovariance (b i).val = mu i • (b i).val) ∧
      (∀ i, ((b i).val,(mu i)⁻¹ • (b i).val) ∈ boundaryOperator.graph) ∧
      (∀ i, Sigma (k i).val = mu i • (k i).val) ∧
      (∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) ∧
      (∀ a : ℝ, 0 < a → FiniteDimensional ℝ (boundaryEigenspace a⁻¹)) ∧
      (∀ a : ℝ, 0 < a → Module.finrank ℝ (boundaryEigenspace a⁻¹) =
        Nat.card {i // mu i = a}) ∧
      (∀ eps : ℝ, 0 < eps → {i | eps ≤ mu i}.Finite) := by
  obtain ⟨b,mu,hp,hm,ht,he⟩ := ordered_boundary_basis
  obtain ⟨k,hk,hC⟩ := paired_edge_basis b mu hp he
  refine ⟨b,k,mu,hp,hm,ht,?_,?_,?_,?_,hk,hC,?_,spectral_multiplicity b mu he,?_⟩
  · intro i j hij
    exact inv_anti₀ (hp j) (hm hij)
  · exact tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall hp⟩)
  · intro i
    simpa only [covariance0_coe,Submodule.coe_smul] using congrArg Subtype.val (he i)
  · intro i
    apply (inverse_eigenvalue (mu i)⁻¹ (inv_pos.mpr (hp i)) (b i).val).mpr
    refine ⟨(b i).property,?_⟩
    simpa only [inv_inv,covariance0_coe,Submodule.coe_smul] using congrArg Subtype.val (he i)
  · intro a ha
    exact (actual_covariance_eigenspaces a ha).2.2.2.1
  · exact covariance_basis_finite_above b mu he

#print axioms actual_self_adjoint_realization
#print axioms actual_compact_resolvent
#print axioms actual_covariance_eigenspaces
#print axioms actual_positive_spectral_exhaustion

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator
