/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Compact actual covariance and the attained original free-root energy. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The actual infinite trace, its covariance, and the least-energy free-root form. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm

open FiniteSourceHardy (H Edge)
open BiasedBoundaryTrace (G J M cylinder indicator J_single)
open BiasedBoundaryPathSplit (constG)
open BiasedBoundaryCentering (mean Pi C centered_suffix_residual)
open BiasedBoundaryStopping (Threshold Qt Vt actual_stopping_residual)
open InnerProductSpace Filter MeasureTheory
open scoped Topology

/-- The actual adjoint trace of the constant one. -/
def v : H := J.adjoint (constG 1)

/-- The covariance on the original infinite square-summable edge space. -/
def Sigma : H →L[ℝ] H := C.adjoint.comp C

/-- The effective increment space, without treating edge-kernel vectors as boundary modes. -/
def K : Submodule ℝ H := Sigma.kerᗮ

instance : K.HasOrthogonalProjection := by unfold K; infer_instance

private theorem compact_C : IsCompactOperator C := by
  have hmem : C ∈ closure {f : H →L[ℝ] G | IsCompactOperator f} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let t : Threshold := ⟨min (1/2) (ε^2/(4*Real.goldenRatio)),
      lt_min (by norm_num) (div_pos (sq_pos_of_pos hε) (by positivity)),
      (min_le_left _ _).trans_lt (by norm_num)⟩
    have ht : Real.goldenRatio*t.val ≤ (ε/2)^2 := by
      have h := min_le_right (1/2 : ℝ) (ε^2/(4*Real.goldenRatio))
      change t.val ≤ _ at h
      have hp := Real.goldenRatio_pos
      have hh := (le_div_iff₀ (by positivity : 0 < 4*Real.goldenRatio)).mp h
      nlinarith
    have hb : ‖C-(Qt t).comp C‖ ≤ ε/2 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro z
      have hz := (actual_stopping_residual t).2.2.2.2.2.2.1 z
      change ‖C z-Qt t (C z)‖ ≤ _
      have hh : ‖C z-Qt t (C z)‖^2 ≤ (ε/2*‖z‖)^2 := by
        calc
          _ ≤ Real.goldenRatio*t.val*‖z‖^2 := hz
          _ ≤ (ε/2)^2*‖z‖^2 := mul_le_mul_of_nonneg_right ht (sq_nonneg _)
          _ = _ := by ring
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (by positivity) (norm_nonneg z))).mp hh
    refine ⟨(Qt t).comp C, ?_, ?_⟩
    · have hf := isCompactOperator_of_locallyCompactSpace_dom
        ((Vt t).orthogonalProjectionOnto.comp C)
      have hc := hf.clm_comp (Vt t).subtypeL
      have he : (Qt t).comp C = (Vt t).subtypeL.comp
          ((Vt t).orthogonalProjectionOnto.comp C) := by
        apply ContinuousLinearMap.ext
        intro z
        exact (actual_stopping_residual t).2.1 (C z)
      change IsCompactOperator ((Qt t).comp C)
      rw [he]
      exact hc
    · rw [dist_eq_norm]
      exact hb.trans_lt (by linarith)
  rwa [isClosed_setOfPred_isCompactOperator.closure_eq] at hmem

theorem mean_Pi (F : G) : mean (Pi F) = 0 := by
  rw [centered_suffix_residual.2.2.1, map_sub, centered_suffix_residual.2.1, sub_self]

theorem Pi_idem (F : G) : Pi (Pi F) = Pi F := by
  rw [centered_suffix_residual.2.2.1 (Pi F), mean_Pi, map_zero, sub_zero]

private theorem Sigma_pair (z w : H) : inner ℝ z (Sigma w) = inner ℝ (C z) (C w) :=
  C.adjoint_inner_right z (C w)

private theorem ker_Sigma : Sigma.ker = C.ker := C.ker_adjoint_comp_self

private theorem covariance_formula :
    Sigma = J.adjoint.comp J - rankOne ℝ v v := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_left ℝ
  intro w
  rw [Sigma_pair]
  change inner ℝ (Pi (J w)) (Pi (J z)) = _
  have hp : inner ℝ (Pi (J w)) (Pi (J z)) = inner ℝ (J w) (Pi (Pi (J z))) :=
    Submodule.inner_starProjection_left_eq_right (ℝ ∙ constG 1)ᗮ _ _
  rw [hp, Pi_idem, centered_suffix_residual.2.2.1, inner_sub_right]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right, ContinuousLinearMap.adjoint_inner_right, rankOne_apply,
    inner_smul_right, v, ContinuousLinearMap.adjoint_inner_left]
  have hc (c : ℝ) : constG c = c • constG 1 := by
    simpa using constG.map_smul c (1:ℝ)
  rw [hc, inner_smul_right]
  change inner ℝ (J w) (J z) - mean (J z)*inner ℝ (J w) (constG 1) =
    inner ℝ (J w) (J z) - inner ℝ (constG 1) (J z)*inner ℝ (J w) (constG 1)
  rfl

private theorem mean_indicator (p : Edge) : mean (indicator p) = M.real (cylinder p.val) := by
  rw [centered_suffix_residual.1]
  change (∫ ω, indicatorConstLp 2 _ _ (1 : ℝ) ω ∂M) = _
  rw [integral_indicatorConstLp]
  simp

private theorem covariance_entry (p q : Edge) :
    inner ℝ (lp.single 2 p (1 : ℝ)) (Sigma (lp.single 2 q (1 : ℝ))) =
      M.real (cylinder p.val ∩ cylinder q.val)-
        M.real (cylinder p.val)*M.real (cylinder q.val) := by
  rw [covariance_formula, ContinuousLinearMap.sub_apply, inner_sub_right,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    J_single, J_single, one_smul, one_smul, rankOne_apply, inner_smul_right]
  have hv (r : Edge) : inner ℝ (lp.single 2 r (1 : ℝ)) v = M.real (cylinder r.val) := by
    rw [v, ContinuousLinearMap.adjoint_inner_right, J_single, one_smul, real_inner_comm]
    exact mean_indicator r
  have hv' (r : Edge) : inner ℝ v (lp.single 2 r (1 : ℝ)) = M.real (cylinder r.val) :=
    (real_inner_comm _ _).trans (hv r)
  rw [hv', hv, mul_comm (M.real (cylinder q.val))]
  congr 1
  exact L2.real_inner_indicatorConstLp_one_indicatorConstLp_one _ _

/-- Stopping averages approximate the actual centered trace in operator norm.
The uncentered trace and its actual covariance are compact, and the covariance
has the original rank-one correction and all-vector quadratic form. -/
theorem actual_compact_covariance :
    IsCompactOperator J ∧ IsCompactOperator C ∧ IsCompactOperator Sigma ∧
    Sigma = J.adjoint.comp J - rankOne ℝ v v ∧
    (∀ z w : H, inner ℝ z (Sigma w) = inner ℝ (C z) (C w)) ∧
    (∀ z : H, inner ℝ z (Sigma z) = ‖C z‖^2) ∧
    Sigma.ker = C.ker ∧
    (∀ p q : Edge,
      inner ℝ (lp.single 2 p (1 : ℝ)) (Sigma (lp.single 2 q (1 : ℝ))) =
        M.real (cylinder p.val ∩ cylinder q.val)-
          M.real (cylinder p.val)*M.real (cylinder q.val)) := by
  have hr : IsCompactOperator (constG.comp (mean.comp J)) := by
    exact (isCompactOperator_of_locallyCompactSpace_rng constG).comp_clm (mean.comp J)
  have hJ : J = C + constG.comp (mean.comp J) := by
    apply ContinuousLinearMap.ext
    intro z
    change J z = Pi (J z)+constG (mean (J z))
    rw [centered_suffix_residual.2.2.1, sub_add_cancel]
  refine ⟨?_, compact_C, compact_C.clm_comp C.adjoint, covariance_formula,
    Sigma_pair, ?_, ker_Sigma, covariance_entry⟩
  · rw [hJ]
    exact compact_C.add hr
  · intro z
    rw [Sigma_pair, real_inner_self_eq_norm_sq]

/-- Exactly the original free-root trace domain. -/
def D : Submodule ℝ G where
  carrier := {F | ∃ (c : ℝ) (z : H), F = constG c + J z}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro F T ⟨c,z,rfl⟩ ⟨d,w,rfl⟩
    exact ⟨c+d,z+w,by simp only [map_add]; abel⟩
  smul_mem' := by
    rintro c F ⟨d,z,rfl⟩
    exact ⟨c*d,c • z,by simp only [← smul_eq_mul, map_smul, smul_add]⟩

/-- The energy is the infimum over the original representations, including the free root. -/
def energy (F : G) : ℝ := sInf {r : ℝ | ∃ (c : ℝ) (z : H),
  F = constG c + J z ∧ r = ‖z‖^2}

private theorem C_project (z : H) : C (K.starProjection z) = C z := by
  have hk : z-K.starProjection z ∈ Sigma.ker := by
    change z-(Sigma.ker)ᗮ.starProjection z ∈ Sigma.ker
    rw [Submodule.starProjection_orthogonal_val]
    convert Submodule.starProjection_apply_mem Sigma.ker z using 1
    abel
  rw [ker_Sigma] at hk
  have hz : C (z-K.starProjection z) = 0 := hk
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

private theorem C_injective_K {z w : H} (hz : z ∈ K) (hw : w ∈ K)
    (he : C z = C w) : z = w := by
  have hn : z-w ∈ Sigma.ker := by
    rw [ker_Sigma]
    change C (z-w) = 0
    rw [map_sub, he, sub_self]
  have ho : z-w ∈ (Sigma.ker)ᗮ := K.sub_mem hz hw
  have hi := ho (z-w) hn
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp hi)

private theorem domain_centered {F : G} (hF : F ∈ D) :
    ∃ z : H, z ∈ K ∧ C z = Pi F := by
  obtain ⟨c,z,rfl⟩ := hF
  refine ⟨K.starProjection z, Submodule.starProjection_apply_mem _ _, ?_⟩
  rw [C_project, map_add, BiasedBoundaryCentering.Pi_const, zero_add]
  rfl

/-- The unique effective lift of a trace, in the orthogonal complement of the covariance kernel. -/
def lift (F : D) : H := (domain_centered F.property).choose

private theorem lift_mem (F : D) : lift F ∈ K := (domain_centered F.property).choose_spec.1
private theorem C_lift (F : D) : C (lift F) = Pi F := (domain_centered F.property).choose_spec.2

private theorem lift_rep (F : D) :
    F.val = constG (mean F.val-mean (J (lift F))) + J (lift F) := by
  have he := C_lift F
  change Pi (J (lift F)) = Pi F.val at he
  rw [centered_suffix_residual.2.2.1, centered_suffix_residual.2.2.1] at he
  calc
    F.val = (F.val-constG (mean F.val))+constG (mean F.val) := by abel
    _ = (J (lift F)-constG (mean (J (lift F))))+constG (mean F.val) := by rw [he]
    _ = constG (mean F.val-mean (J (lift F)))+J (lift F) := by rw [map_sub]; abel

private theorem lift_project (F : D) (c : ℝ) (z : H)
    (h : F.val = constG c+J z) : lift F = K.starProjection z := by
  apply C_injective_K (lift_mem F) (Submodule.starProjection_apply_mem _ _)
  rw [C_lift, h, map_add, BiasedBoundaryCentering.Pi_const, zero_add, C_project]
  rfl

/-- The original free-root infimum is attained, uniquely in K, with the original
root coefficient restored. Every other original extension has at least this energy. -/
theorem free_root_least_energy (F : D) :
    lift F ∈ K ∧ C (lift F) = Pi F.val ∧
    F.val = constG (mean F.val-mean (J (lift F)))+J (lift F) ∧
    energy F.val = ‖lift F‖^2 ∧
    (∀ (c : ℝ) (z : H), F.val = constG c+J z →
      lift F = K.starProjection z ∧ ‖lift F‖^2 ≤ ‖z‖^2) ∧
    (∀ z : H, z ∈ K → C z = Pi F.val → z = lift F) := by
  have hb (c : ℝ) (z : H) (hz : F.val = constG c+J z) : ‖lift F‖^2 ≤ ‖z‖^2 := by
    rw [lift_project F c z hz]
    exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ z) 2
  refine ⟨lift_mem F, C_lift F, lift_rep F, ?_, ?_, ?_⟩
  · apply IsLeast.csInf_eq
    refine ⟨⟨mean F.val-mean (J (lift F)),lift F,lift_rep F,rfl⟩, ?_⟩
    rintro r ⟨c,z,hz,rfl⟩
    exact hb c z hz
  · intro c z hz
    exact ⟨lift_project F c z hz, hb c z hz⟩
  · intro z hz he
    exact C_injective_K hz (lift_mem F) (he.trans (C_lift F).symm)

/-- The polarized original energy, using its attained least-norm increments. -/
def form (F T : D) : ℝ := inner ℝ (lift F) (lift T)

private theorem lift_add (F T : D) : lift (F+T) = lift F+lift T := by
  apply C_injective_K (lift_mem (F+T)) (K.add_mem (lift_mem F) (lift_mem T))
  rw [map_add,C_lift,C_lift,C_lift]
  exact Pi.map_add F.val T.val

private theorem lift_sub (F T : D) : lift (F-T) = lift F-lift T := by
  apply C_injective_K (lift_mem (F-T)) (K.sub_mem (lift_mem F) (lift_mem T))
  rw [map_sub,C_lift,C_lift,C_lift]
  exact Pi.map_sub F.val T.val

private theorem energy_polarization (F T : D) :
    form F T = (energy (F+T).val-energy (F-T).val)/4 := by
  rw [(free_root_least_energy (F+T)).2.2.2.1,
    (free_root_least_energy (F-T)).2.2.2.1,lift_add,lift_sub,
    norm_add_sq_real,norm_sub_sq_real]
  unfold form
  ring

/-- The weak variational graph of the original free-root form. -/
def weakGraph (u h : G) : Prop :=
  ∃ hu : u ∈ D, ∀ F : D, form ⟨u,hu⟩ F = inner ℝ h F.val

private def traceD (z : H) : D := ⟨J z, 0, z, by simp⟩
private def constantD (c : ℝ) : D := ⟨constG c, c, 0, by simp⟩

private theorem lift_trace (z : H) : lift (traceD z) = K.starProjection z :=
  (free_root_least_energy (traceD z)).2.2.2.2.1 0 z (by simp [traceD]) |>.1

private theorem lift_constant (c : ℝ) : lift (constantD c) = 0 := by
  have he := ((free_root_least_energy (constantD c)).2.2.2.2.1 c 0
    (by simp [constantD])).1
  simpa using he

theorem adjoint_mem_K (h : G) : C.adjoint h ∈ K := by
  change ∀ z ∈ Sigma.ker, inner ℝ z (C.adjoint h) = 0
  intro z hz
  rw [ker_Sigma] at hz
  rw [ContinuousLinearMap.adjoint_inner_right, show C z = 0 from hz, inner_zero_left]

theorem inner_centered (h F : G) (hh : mean h = 0) :
    inner ℝ h (Pi F) = inner ℝ h F := by
  have he : Pi h = h := by
    rw [centered_suffix_residual.2.2.1, hh, map_zero, sub_zero]
  change inner ℝ h ((ℝ ∙ constG 1)ᗮ.starProjection F) = _
  rw [← Submodule.inner_starProjection_left_eq_right]
  exact congrArg (fun x => inner ℝ x F) he

private theorem represented_of_centered (F : G) (z : H) (hz : C z = Pi F) : F ∈ D := by
  refine ⟨mean F-mean (J z),z,?_⟩
  change Pi (J z) = Pi F at hz
  rw [centered_suffix_residual.2.2.1, centered_suffix_residual.2.2.1] at hz
  rw [map_sub]
  calc
    F = (F-constG (mean F))+constG (mean F) := by abel
    _ = (J z-constG (mean (J z)))+constG (mean F) := by rw [hz]
    _ = _ := by abel

/-- The weak graph uses all traces in the original domain. It is exactly the
constant translate of the actual covariance CC*, with the right-hand side mean zero. -/
private theorem variational_graph_core (u h : G) :
    weakGraph u h ↔ mean h = 0 ∧
      u = constG (mean u)+C (C.adjoint h) := by
  constructor
  · rintro ⟨hu,hweak⟩
    let U : D := ⟨u,hu⟩
    have hh : mean h = 0 := by
      have he := hweak (constantD 1)
      rw [form, lift_constant, inner_zero_right] at he
      change 0 = inner ℝ h (constG 1) at he
      change inner ℝ (constG 1) h = 0
      rw [real_inner_comm]
      exact he.symm
    have hl : lift U = C.adjoint h := by
      apply ext_inner_right ℝ
      intro z
      have he := hweak (traceD z)
      change inner ℝ (lift U) (lift (traceD z)) = inner ℝ h (J z) at he
      rw [lift_trace, ← Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr (lift_mem U)] at he
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact he.trans (inner_centered h (J z) hh).symm
    refine ⟨hh,?_⟩
    have he := C_lift U
    rw [hl] at he
    change C (C.adjoint h) = Pi u at he
    rw [he, centered_suffix_residual.2.2.1]
    abel
  · rintro ⟨hh,hu⟩
    have hc : C (C.adjoint h) = Pi u := by
      rw [hu, map_add, BiasedBoundaryCentering.Pi_const, zero_add]
      exact (Pi_idem (J (C.adjoint h))).symm
    have hd := represented_of_centered u (C.adjoint h) hc
    refine ⟨hd,?_⟩
    intro F
    have hl : lift ⟨u,hd⟩ = C.adjoint h :=
      (C_injective_K (lift_mem ⟨u,hd⟩) (adjoint_mem_K h)
        ((C_lift ⟨u,hd⟩).trans hc.symm))
    rw [form, hl, ContinuousLinearMap.adjoint_inner_left, C_lift]
    exact inner_centered h F.val hh

private theorem lift_graph_eq : {x : G × H | ∃ F : D, x = (F.val,lift F)} =
      {x : G × H | x.2 ∈ K ∧ C x.2 = Pi x.1} := by
    ext x
    constructor
    · rintro ⟨F,rfl⟩
      exact ⟨lift_mem F,C_lift F⟩
    · rintro ⟨hk,hc⟩
      have hd := represented_of_centered x.1 x.2 hc
      refine ⟨⟨x.1,hd⟩,?_⟩
      apply Prod.ext
      · rfl
      · exact (free_root_least_energy ⟨x.1,hd⟩).2.2.2.2.2 x.2 hk hc

private theorem closed_lift_graph :
    IsClosed {x : G × H | ∃ F : D, x = (F.val,lift F)} := by
  rw [lift_graph_eq]
  have hk : IsClosed {x : G × H | x.2 ∈ K} := by
    exact Sigma.ker.isClosed_orthogonal.preimage continuous_snd
  exact hk.inter (isClosed_eq (C.continuous.comp continuous_snd)
    (Pi.continuous.comp continuous_fst))

/-- The original form domain in its complete least-increment graph norm. -/
def formSpace : Submodule ℝ (G × H) where
  carrier := {x | x.2 ∈ K ∧ C x.2 = Pi x.1}
  zero_mem' := ⟨K.zero_mem,by simp⟩
  add_mem' := by
    intro x y hx hy
    change x.2+y.2 ∈ K ∧ C (x.2+y.2) = Pi (x.1+y.1)
    exact ⟨K.add_mem hx.1 hy.1,by rw [map_add,map_add,hx.2,hy.2]⟩
  smul_mem' := by
    intro c x hx
    change c • x.2 ∈ K ∧ C (c • x.2) = Pi (c • x.1)
    exact ⟨K.smul_mem c hx.1,by rw [map_smul,map_smul,hx.2]⟩

/-- The actual inclusion into G of the original energy domain, in graph coordinates. -/
def formInclusion : formSpace →L[ℝ] G :=
  (ContinuousLinearMap.fst ℝ G H).comp formSpace.subtypeL

private def incrementInclusion : formSpace →L[ℝ] H :=
  (ContinuousLinearMap.snd ℝ G H).comp formSpace.subtypeL

private theorem form_space_identification (x : formSpace) :
    ∃ F : D, x.val = (F.val,lift F) ∧ energy F.val = ‖x.val.2‖^2 := by
  have hx : x.val ∈ {y : G × H | y.2 ∈ K ∧ C y.2 = Pi y.1} := x.property
  rw [← lift_graph_eq] at hx
  obtain ⟨F,hF⟩ := hx
  refine ⟨F,hF,?_⟩
  have hz := congrArg Prod.snd hF
  rw [hz]
  exact (free_root_least_energy F).2.2.2.1

private theorem compact_form_inclusion : IsCompactOperator formInclusion := by
  have he : formInclusion = constG.comp (mean.comp formInclusion)+C.comp incrementInclusion := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := x.property.2
    change C x.val.2 = Pi x.val.1 at hx
    change x.val.1 = constG (mean x.val.1)+C x.val.2
    rw [hx,centered_suffix_residual.2.2.1]
    abel
  rw [he]
  exact ((isCompactOperator_of_locallyCompactSpace_rng constG).comp_clm
    (mean.comp formInclusion)).add
    (actual_compact_covariance.2.1.comp_clm incrementInclusion)

/-- The least-norm pairing has exactly the original infimum on its diagonal,
and its entire weak variational graph is the actual covariance graph. -/
theorem free_root_variational_graph :
    (∀ F : D, form F F = energy F.val) ∧
    (∀ F T : D, form F T = (energy (F+T).val-energy (F-T).val)/4) ∧
    IsClosed {x : G × H | ∃ F : D, x = (F.val,lift F)} ∧
    (∀ x : formSpace, ∃ F : D,
      x.val = (F.val,lift F) ∧ energy F.val = ‖x.val.2‖^2) ∧
    IsCompactOperator formInclusion ∧
    (∀ u h : G, weakGraph u h ↔ mean h = 0 ∧
      u = constG (mean u)+C (C.adjoint h)) := by
  constructor
  · intro F
    rw [form, real_inner_self_eq_norm_sq, (free_root_least_energy F).2.2.2.1]
  · exact ⟨energy_polarization,closed_lift_graph,form_space_identification,compact_form_inclusion,variational_graph_core⟩

#print axioms actual_compact_covariance
#print axioms free_root_least_energy
#print axioms free_root_variational_graph

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm
