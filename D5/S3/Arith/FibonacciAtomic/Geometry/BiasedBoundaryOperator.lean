/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm]
   utility: none
   digest: Self-adjoint realization of the actual infinite biased free-root form. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-! The original form is realized on the actual infinite biased boundary. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (H Edge)
open BiasedBoundaryTrace (G Omega M J cylinder indicator J_single cylinder_measurable)
open BiasedBoundaryPathSplit (constG)
open BiasedBoundaryStopping (G0 Threshold A Vt Vt0 actual_stopping_partition actual_stopping_residual)
open BiasedBoundaryCentering (mean Pi C centered_suffix_residual)
open BiasedBoundaryFreeRootForm (D form weakGraph free_root_variational_graph mean_Pi Pi_const Pi_idem inner_centered)
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
    rw [hu,map_add,Pi_const,zero_add]
    change Pi (Pi (J (C.adjoint h))) = Pi (J (C.adjoint h))
    exact Pi_idem _

private theorem graph_constant (c : ℝ) : (constG c,0) ∈ operatorGraph := by
  change mean 0 = 0 ∧ Pi (constG c) = boundaryCovariance 0
  rw [map_zero, Pi_const, map_zero]
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

#print axioms actual_self_adjoint_realization

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator
