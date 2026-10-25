/- GID: D5/S3/Quantum/Analysis/HeisenbergCentralRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/HeisenbergCentralRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Central rigidity of the complex compact smooth joint Heisenberg graph on raw whole-space Lebesgue measure. -/

import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Tactic

/-! The complex joint graph and its whole-line central rigidity. -/

open MeasureTheory Set Filter LineDeriv
open scoped ENNReal Topology FourierTransform SchwartzMap ComplexConjugate

noncomputable section
namespace D5.S3.Quantum.Analysis.HeisenbergCentralRigidity

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev State := Lp ℂ 2 (volume : Measure Space)
abbrev Components := Fin 3 → State
abbrev Ambient := State × Components

def axis (i : Fin 3) : Space := EuclideanSpace.single i 1
private def coord (i : Fin 3) : Space → ℂ := fun x => (x i : ℂ)
private theorem coord_growth (i : Fin 3) : (coord i).HasTemperateGrowth := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp (EuclideanSpace.proj i).hasTemperateGrowth

/-- The actual whole-space Heisenberg frame, in U,V,Z order. -/
def frame (i : Fin 3) (x : Space) : Space :=
  ![axis 0 - (x 1 / 2) • axis 2, axis 1 + (x 0 / 2) • axis 2, axis 2] i

/-- The three fields are U, V and Z, in this order. -/
def field (i : Fin 3) : 𝓢(Space, ℂ) →L[ℂ] 𝓢(Space, ℂ) :=
  ![lineDerivOpCLM ℂ 𝓢(Space, ℂ) (axis 0) -
      (1 / 2 : ℂ) • (SchwartzMap.smulLeftCLM ℂ (coord 1)).comp
        (lineDerivOpCLM ℂ 𝓢(Space, ℂ) (axis 2)),
    lineDerivOpCLM ℂ 𝓢(Space, ℂ) (axis 1) +
      (1 / 2 : ℂ) • (SchwartzMap.smulLeftCLM ℂ (coord 0)).comp
        (lineDerivOpCLM ℂ 𝓢(Space, ℂ) (axis 2)),
    lineDerivOpCLM ℂ 𝓢(Space, ℂ) (axis 2)] i

private theorem field_apply (i : Fin 3) (φ : 𝓢(Space, ℂ)) (x : Space) :
    field i φ x = fderiv ℝ φ x (frame i x) := by
  fin_cases i <;>
    simp [field, frame, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      SchwartzMap.smulLeftCLM_apply_apply, coord_growth, coord, map_sub, map_add,
      map_smul, Complex.real_smul, Complex.ofReal_div] <;> ring

private def distributionField (i : Fin 3) : 𝓢'(Space, ℂ) →L[ℂ] 𝓢'(Space, ℂ) :=
  ![lineDerivOpCLM ℂ 𝓢'(Space, ℂ) (axis 0) -
      (1 / 2 : ℂ) • (TemperedDistribution.smulLeftCLM ℂ (coord 1)).comp
        (lineDerivOpCLM ℂ 𝓢'(Space, ℂ) (axis 2)),
    lineDerivOpCLM ℂ 𝓢'(Space, ℂ) (axis 1) +
      (1 / 2 : ℂ) • (TemperedDistribution.smulLeftCLM ℂ (coord 0)).comp
        (lineDerivOpCLM ℂ 𝓢'(Space, ℂ) (axis 2)),
    lineDerivOpCLM ℂ 𝓢'(Space, ℂ) (axis 2)] i

/-- Exactly the compactly supported complex smooth core, represented as Schwartz functions. -/
def compactCore : Submodule ℂ 𝓢(Space, ℂ) where
  carrier := {φ | HasCompactSupport φ}
  zero_mem' := by simpa using (HasCompactSupport.zero : HasCompactSupport (0 : Space → ℂ))
  add_mem' := fun hφ hψ => hφ.add hψ
  smul_mem' := fun c φ hφ => hφ.comp_left (show c • (0 : ℂ) = 0 by simp)

/-- State and all three derivatives of one and the same core function. -/
def coreJet : compactCore →ₗ[ℂ] Ambient :=
  let J := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)
  (J.toLinearMap.comp compactCore.subtype).prod
    (LinearMap.pi fun i => (J.comp (field i)).toLinearMap.comp compactCore.subtype)

/-- Simultaneous closure in state and all three L2 components. -/
def jointGraph : Submodule ℂ Ambient := (LinearMap.range coreJet).topologicalClosure

private def embedding : State →L[ℂ] 𝓢'(Space, ℂ) :=
  Lp.toTemperedDistributionCLM ℂ volume 2

private theorem embedding_injective : Function.Injective embedding := by
  apply LinearMap.ker_eq_bot.mp
  exact Lp.ker_toTemperedDistributionCLM_eq_bot

private theorem schwartz_multiply (i : Fin 3) (φ : 𝓢(Space, ℂ)) :
    ((SchwartzMap.smulLeftCLM ℂ (coord i) φ : 𝓢(Space, ℂ)) : 𝓢'(Space, ℂ)) =
      TemperedDistribution.smulLeftCLM ℂ (coord i) (φ : 𝓢'(Space, ℂ)) := by
  ext ψ
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply]
  congr 1
  funext x
  simp [SchwartzMap.smulLeftCLM_apply_apply (coord_growth i), smul_eq_mul, mul_left_comm, mul_assoc]

private theorem field_embedding (i : Fin 3) (φ : 𝓢(Space, ℂ)) :
    embedding ((field i φ).toLp 2 volume) = distributionField i (embedding (φ.toLp 2 volume)) := by
  have hd (j : Fin 3) := TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq (μ := (volume : Measure Space)) φ (axis j)
  fin_cases i <;>
    simp [embedding, field, distributionField, map_sub, map_add, map_smul,
      Lp.toTemperedDistribution_toLp_eq, hd, schwartz_multiply]

private theorem graph_distribution (p : Ambient) (hp : p ∈ jointGraph) (i : Fin 3) :
    embedding (p.2 i) = distributionField i (embedding p.1) := by
  have hc : IsClosed {q : Ambient | embedding (q.2 i) = distributionField i (embedding q.1)} :=
    isClosed_eq (embedding.continuous.comp ((continuous_apply i).comp continuous_snd))
      ((distributionField i).continuous.comp (embedding.continuous.comp continuous_fst))
  apply closure_minimal (t := {q : Ambient | embedding (q.2 i) = distributionField i (embedding q.1)}) ?_ hc hp
  rintro q ⟨φ, rfl⟩
  exact field_embedding i φ

private theorem central_distribution_kernel (u : State)
    (hu : ∂_{axis 2} (embedding u) = 0) : u = 0 := by
  let F : State := 𝓕 u
  have hfourier := TemperedDistribution.fourier_lineDerivOp_eq (embedding u) (axis 2)
  have hmul : TemperedDistribution.smulLeftCLM ℂ (fun x : Space => (inner ℝ x (axis 2) : ℂ))
      (embedding F) = 0 := by
    have hnonzero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    rw [hu] at hfourier
    have hcast : (𝓕 (embedding u)) = embedding F := by
      exact Lp.fourier_toTemperedDistribution_eq u
    rw [hcast] at hfourier
    exact (smul_eq_zero.mp hfourier.symm).resolve_left hnonzero
  have hcoord : (fun x : Space => (inner ℝ x (axis 2) : ℂ)) = coord 2 := by
    funext x
    simp [axis, coord, EuclideanSpace.inner_single_right]
  rw [hcoord] at hmul
  have hlocal : LocallyIntegrable (fun x : Space => coord 2 x * F x) volume :=
    LocallyIntegrable.continuous_mul (coord_growth 2).1.continuous
      ((Lp.memLp F).locallyIntegrable (by norm_num))
  have hzero : (fun x : Space => coord 2 x * F x) =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    intro ψ hψ hcψ
    let ψc : 𝓢(Space, ℂ) := (hcψ.comp_left (show Complex.ofRealCLM 0 = 0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hψ)
    have he := congrArg (fun T : 𝓢'(Space, ℂ) => T ψc) hmul
    simpa [embedding, Lp.toTemperedDistribution_apply, coord_growth,
      SchwartzMap.smulLeftCLM_apply_apply, ψc, smul_eq_mul, mul_assoc, mul_left_comm] using he
  have hnull : volume {x : Space | x 2 = 0} = 0 := by
    have hk : (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).toLinearMap.ker ≠ ⊤ := by
      intro h
      have hh : axis 2 ∈ (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).toLinearMap.ker := by rw [h]; trivial
      simpa [axis] using hh
    exact Measure.addHaar_submodule volume _ hk
  have hF : F = 0 := by
    apply Lp.ext
    have hne : ∀ᵐ x : Space, x 2 ≠ 0 := by
      simpa only [ae_iff, not_not] using hnull
    filter_upwards [hzero, hne] with x hx hn
    have hx' : coord 2 x ≠ 0 := by simpa [coord] using hn
    simpa using (mul_eq_zero.mp hx).resolve_left hx'
  have := congrArg (fun v : State => 𝓕⁻ v) hF
  simpa [F] using this

private theorem vertical_zero (p : Ambient) (hp : p ∈ jointGraph) (hz : p.1 = 0) :
    p.2 = 0 := by
  funext i
  apply embedding_injective
  rw [graph_distribution p hp i, hz, map_zero, map_zero]
  simp

/-- The compact smooth joint gradient, as Mathlib's partial linear map. -/
def coreOperator : State →ₗ.[ℂ] Components := (LinearMap.range coreJet).toLinearPMap

/-- The closure of the compact smooth joint gradient. -/
def closedOperator : State →ₗ.[ℂ] Components := coreOperator.closure

private theorem core_operator_graph : coreOperator.graph = LinearMap.range coreJet := by
  apply Submodule.toLinearPMap_graph_eq
  intro p hp hz
  exact vertical_zero p (Submodule.le_topologicalClosure _ hp) hz

private theorem core_closable : coreOperator.IsClosable := by
  refine ⟨jointGraph.toLinearPMap, ?_⟩
  rw [core_operator_graph, Submodule.toLinearPMap_graph_eq jointGraph vertical_zero]
  rfl

private theorem closed_operator_graph : closedOperator.graph = jointGraph := by
  rw [closedOperator, ← core_closable.graph_closure_eq_closure_graph, core_operator_graph]
  rfl

private theorem core_dense : Dense (coreOperator.domain : Set State) := by
  have hd := Lp.dense_hasCompactSupport_contDiff (E := Space) (F := ℂ)
    (μ := (volume : Measure Space)) (p := 2) (by norm_num)
  apply hd.mono
  rintro u ⟨f, huf, hc, hs⟩
  let φ : compactCore := ⟨hc.toSchwartzMap hs, hc⟩
  have he : (coreJet φ).1 = u := by
    apply Lp.ext
    exact (hc.toSchwartzMap hs).coeFn_toLp 2 volume |>.trans huf.symm
  apply LinearPMap.mem_domain_of_mem_graph
  rw [core_operator_graph]
  exact ⟨φ, Prod.ext he rfl⟩

private theorem graph_limits (p : Ambient) : p ∈ jointGraph ↔
    ∃ φ : ℕ → compactCore,
      Tendsto (fun n => (coreJet (φ n)).1) atTop (𝓝 p.1) ∧
      ∀ i, Tendsto (fun n => (coreJet (φ n)).2 i) atTop (𝓝 (p.2 i)) := by
  change p ∈ closure (LinearMap.range coreJet : Set Ambient) ↔ _
  rw [mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨q, hq, hl⟩
    choose φ hφ using hq
    have he : q = fun n => coreJet (φ n) := funext fun n => (hφ n).symm
    rw [he] at hl
    exact ⟨φ, hl.fst_nhds, tendsto_pi_nhds.mp hl.snd_nhds⟩
  · rintro ⟨φ, hu, hg⟩
    exact ⟨fun n => coreJet (φ n), fun n => ⟨φ n, rfl⟩,
      hu.prodMk_nhds (tendsto_pi_nhds.mpr hg)⟩

private theorem graph_weak_central (p : Ambient) (hp : p ∈ jointGraph)
    (η : Space → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) :
    (∫ x : Space, (p.2 2) x * conj (η x)) =
      -(∫ x : Space, p.1 x * conj (fderiv ℝ η x (axis 2))) := by
  let ψ : 𝓢(Space, ℂ) :=
    (hcη.comp_left (show conj (0 : ℂ) = 0 by simp)).toSchwartzMap
      (Complex.conjCLE.contDiff.comp hη)
  have hψ (x : Space) : (∂_{axis 2} ψ) x = conj (fderiv ℝ η x (axis 2)) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change fderiv ℝ (fun x => conj (η x)) x (axis 2) = _
    have hd := (Complex.conjCLE.hasFDerivAt.comp x
      ((hη.differentiable (by norm_num)) x).hasFDerivAt).fderiv
    exact congrArg (fun L : Space →L[ℝ] ℂ => L (axis 2)) hd
  have hψval (x : Space) : ψ x = conj (η x) := rfl
  have he := congrArg (fun T : 𝓢'(Space, ℂ) => T ψ) (graph_distribution p hp 2)
  have hd : distributionField 2 = lineDerivOpCLM ℂ 𝓢'(Space, ℂ) (axis 2) := rfl
  rw [hd] at he
  simpa only [embedding, lineDerivOpCLM_apply, TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply,
    map_neg, smul_eq_mul, hψ, hψval, mul_comm, integral_neg,
    zero_apply] using he

/-- Every original compact smooth function occurs with its three actual derivatives;
the graph is the single-valued closed simultaneous completion, and its central
component is the complex weak derivative with trivial kernel on the whole space. -/
theorem central_rigidity :
    Dense (coreOperator.domain : Set State) ∧
    coreOperator.IsClosable ∧ closedOperator.IsClosed ∧
    closedOperator.graph = jointGraph ∧
    (∀ p : Ambient, p ∈ jointGraph ↔ ∃ φ : ℕ → compactCore,
      Tendsto (fun n => (coreJet (φ n)).1) atTop (𝓝 p.1) ∧
      ∀ i, Tendsto (fun n => (coreJet (φ n)).2 i) atTop (𝓝 (p.2 i))) ∧
    (∀ p ∈ jointGraph, ∀ q ∈ jointGraph, p.1 = q.1 → p.2 = q.2) ∧
    (∀ p ∈ jointGraph, ∀ η : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ x : Space, (p.2 2) x * conj (η x)) =
        -(∫ x : Space, p.1 x * conj (fderiv ℝ η x (axis 2)))) ∧
    (∀ p ∈ jointGraph, p.2 2 = 0 ↔ p.1 = 0) ∧
    (∀ (f : Space → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f),
      ∃ p ∈ jointGraph, (p.1 : Space → ℂ) =ᵐ[volume] f ∧
        ∀ i, (p.2 i : Space → ℂ) =ᵐ[volume]
          (fun x => fderiv ℝ f x (frame i x))) := by
  refine ⟨core_dense, core_closable, core_closable.closure_isClosed,
    closed_operator_graph, graph_limits, ?_,
    graph_weak_central, ?_, ?_⟩
  · intro p hp q hq he
    have hv := vertical_zero (p - q) (jointGraph.sub_mem hp hq) (by simpa [he])
    exact sub_eq_zero.mp hv
  · intro p hp
    constructor
    · intro hz
      apply central_distribution_kernel
      have he := graph_distribution p hp 2
      simpa [distributionField, hz] using he.symm
    · intro hz
      exact congrFun (vertical_zero p hp hz) 2
  · intro f hs hc
    let φ : compactCore := ⟨hc.toSchwartzMap hs, hc⟩
    refine ⟨coreJet φ, Submodule.le_topologicalClosure _ ⟨φ, rfl⟩,
      (hc.toSchwartzMap hs).coeFn_toLp 2 volume, ?_⟩
    intro i
    filter_upwards [(field i (hc.toSchwartzMap hs)).coeFn_toLp 2 volume] with x hx
    exact hx.trans (field_apply i (hc.toSchwartzMap hs) x)

#print axioms central_rigidity
end D5.S3.Quantum.Analysis.HeisenbergCentralRigidity
