/- GID: D5/S3/Quantum/Analysis/SchwartzWeakAdjoint
   generality: I
   mirror-B: D5/B/S3/Quantum/Analysis/SchwartzWeakAdjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact tests characterize the actual Schwartz differential adjoint graph. -/

/-
The cutoff argument uses SchwartzCutoffGraph and its attributed W21 source chain.
Integration by parts, the Schwartz embedding and the partial-map adjoint use
pinned Mathlib directly, without copying an additional supplier proof.
-/

import D5.S3.Quantum.Analysis.SchwartzCutoffGraph
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

open SchwartzMap MeasureTheory LineDeriv Filter LinearPMap
open scoped Topology LineDeriv ENNReal InnerProductSpace ComplexConjugate
noncomputable section
namespace D5.S3.Quantum.Analysis.SchwartzWeakAdjoint
open D5.S3.Quantum.Analysis.SchwartzCutoffGraph

abbrev Hilbert (d : ℕ) := Lp ℂ 2 (volume : Measure (Space d))

def expressionLM (d : ℕ) (a b : Fin d → ℝ) : 𝓢(Space d, ℂ) →ₗ[ℂ] 𝓢(Space d, ℂ) where
  toFun := differential d a b
  map_add' φ ζ := by
    classical
    simp only [differential, lineDerivOp_add, _root_.map_add, smul_add,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by abel
  map_smul' c φ := by
    classical
    have hp (j : Fin d) :
        SchwartzMap.smulLeftCLM ℂ (fun x : Space d => x j ^ 2) (c • φ) =
        c • SchwartzMap.smulLeftCLM ℂ (fun x : Space d => x j ^ 2) φ := by
      ext x
      have hg : (fun x : Space d => x j ^ 2).HasTemperateGrowth :=
        (EuclideanSpace.proj j).hasTemperateGrowth.pow 2
      simp [SchwartzMap.smulLeftCLM_apply_apply hg]
      ring
    simp only [differential, lineDerivOp_smul, hp, Finset.smul_sum, smul_add, RingHom.id_apply]
    exact Finset.sum_congr rfl fun j _ => by
      rw [smul_comm (-a j) c, smul_comm (b j) c]

def schwartzOperator (d : ℕ) (a b : Fin d → ℝ) : Hilbert d →ₗ.[ℂ] Hilbert d :=
  let J := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Space d))
  { domain := LinearMap.range J.toLinearMap
    toFun := (J.toLinearMap.comp (expressionLM d a b)).comp
      (LinearEquiv.ofInjective J.toLinearMap (SchwartzMap.injective_toLp 2 volume)).symm.toLinearMap }

def Weak (d : ℕ) (a b : Fin d → ℝ) (f g : Hilbert d) : Prop :=
  ∀ (ψ : Space d → ℂ) (hc : HasCompactSupport ψ) (hs : ContDiff ℝ (⊤ : ℕ∞) ψ),
    ⟪(differential d a b (hc.toSchwartzMap hs)).toLp 2 volume, f⟫_ℂ =
      ⟪(hc.toSchwartzMap hs).toLp 2 volume, g⟫_ℂ

set_option maxHeartbeats 800000 in
theorem compact_test_adjoint_graph (d : ℕ) (a b : Fin d → ℝ) (f g : Hilbert d) :
    Dense ((schwartzOperator d a b).domain : Set (Hilbert d)) ∧
    (schwartzOperator d a b).IsFormalAdjoint (schwartzOperator d a b) ∧
    (schwartzOperator d a b).IsClosable ∧
    (Weak d a b f g ↔ (f, g) ∈ (schwartzOperator d a b)†.graph) := by
  classical
  let J := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Space d))
  let S := schwartzOperator d a b
  let e := LinearEquiv.ofInjective J.toLinearMap (SchwartzMap.injective_toLp 2 volume)
  have hS (φ : 𝓢(Space d, ℂ)) : S (e φ) = J (differential d a b φ) := by
    change J (differential d a b (e.symm (e φ))) = _
    rw [e.symm_apply_apply]
  have he (φ : 𝓢(Space d, ℂ)) : ((e φ : S.domain) : Hilbert d) = J φ := rfl
  have hdense : Dense (S.domain : Set (Hilbert d)) := by
    change Dense (Set.range (fun φ : 𝓢(Space d, ℂ) => φ.toLp 2 volume))
    exact SchwartzMap.denseRange_toLpCLM (F := ℂ)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (μ := (volume : Measure (Space d)))
  have hsympair (φ ζ : 𝓢(Space d, ℂ)) :
      ⟪J (differential d a b φ), J ζ⟫_ℂ = ⟪J φ, J (differential d a b ζ)⟫_ℂ := by
    let L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
      (ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap
    have hL (z w : ℂ) : L z w = inner ℂ z w := by
      change conj z * w = inner ℂ z w
      simp [RCLike.inner_apply, mul_comm]
    have hsecond (v : Space d) :
        ⟪J (∂_{v} (∂_{v} φ)), J ζ⟫_ℂ = ⟪J φ, J (∂_{v} (∂_{v} ζ))⟫_ℂ := by
      simp only [J, SchwartzMap.toLpCLM_apply, SchwartzMap.inner_toL2_toL2_eq]
      simp only [← hL]
      rw [SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left φ (∂_{v} ζ) L v,
        SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left (∂_{v} φ) ζ L v,
        neg_neg]
    have hpotential (j : Fin d) :
        ⟪J (SchwartzMap.smulLeftCLM ℂ (fun x : Space d => x j ^ 2) φ), J ζ⟫_ℂ =
        ⟪J φ, J (SchwartzMap.smulLeftCLM ℂ (fun x : Space d => x j ^ 2) ζ)⟫_ℂ := by
      simp only [J, SchwartzMap.toLpCLM_apply, SchwartzMap.inner_toL2_toL2_eq]
      apply integral_congr_ae
      filter_upwards with x
      have hp : (fun x : Space d => x j ^ 2).HasTemperateGrowth :=
        (EuclideanSpace.proj j).hasTemperateGrowth.pow 2
      simp only [SchwartzMap.smulLeftCLM_apply_apply hp]
      simp [Complex.real_smul, mul_comm, mul_left_comm]
    have hreal_left (r : ℝ) (u v : Hilbert d) : ⟪r • u, v⟫_ℂ = r • ⟪u, v⟫_ℂ := by
      rw [← algebraMap_smul ℂ r u, RCLike.algebraMap_eq_ofReal, inner_smul_real_left]
    have hreal_right (r : ℝ) (u v : Hilbert d) : ⟪u, r • v⟫_ℂ = r • ⟪u, v⟫_ℂ := by
      rw [← algebraMap_smul ℂ r v, RCLike.algebraMap_eq_ofReal, inner_smul_real_right]
    have hJreal (r : ℝ) (u : 𝓢(Space d, ℂ)) : J (r • u) = r • J u :=
      (SchwartzMap.toLpCLM ℝ ℂ 2 volume).map_smul r u
    simp only [differential, map_sum, _root_.map_add, hJreal, inner_sum, sum_inner,
      inner_add_left, inner_add_right, hreal_left, hreal_right]
    exact Finset.sum_congr rfl fun j _ => by rw [hsecond, hpotential]
  have hsym : S.IsFormalAdjoint S := by
    intro x y
    obtain ⟨φ, rfl⟩ := e.surjective x
    obtain ⟨ζ, rfl⟩ := e.surjective y
    simpa only [hS, he] using hsympair φ ζ
  have hclose : S.IsClosable := LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨S†, LinearPMap.adjoint_isClosed hdense, hsym.le_adjoint hdense⟩
  refine ⟨hdense, hsym, hclose, ?_⟩
  have hext : Weak d a b f g ↔
      ∀ φ : 𝓢(Space d, ℂ), ⟪J (differential d a b φ), f⟫_ℂ = ⟪J φ, g⟫_ℂ := by
    refine ⟨fun hw φ => ?_, fun h ψ hc hs => h (hc.toSchwartzMap hs)⟩
    let c : ContDiffBump (0 : Space d) := ⟨1, 2, by norm_num, by norm_num⟩
    let χ := c.hasCompactSupport.toSchwartzMap c.contDiff
    have hc : HasCompactSupport χ := c.hasCompactSupport
    have hz : χ 0 = 1 := c.one_of_mem_closedBall (by simp [c])
    have hb : ∀ x, ‖χ x‖ ≤ 1 := fun x => by
      change ‖c x‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg c.nonneg]
      exact c.le_one
    obtain ⟨ψ, _, hp, hv, hi⟩ := scaled_cutoff_graph d a b φ χ hc hz hb
    have hl := hi.inner (𝕜 := ℂ) (tendsto_const_nhds (x := f))
    have hr := hv.inner (𝕜 := ℂ) (tendsto_const_nhds (x := g))
    have htest (n : ℕ) :
        ⟪(differential d a b (ψ n)).toLp 2 volume, f⟫_ℂ =
          ⟪(ψ n).toLp 2 volume, g⟫_ℂ := by
      have heq : (hp n).toSchwartzMap ((ψ n).smooth ⊤) = ψ n := by ext x; rfl
      simpa only [heq] using hw (ψ n) (hp n) ((ψ n).smooth ⊤)
    exact tendsto_nhds_unique
      (hl.congr' (Eventually.of_forall htest)) hr
  rw [hext, LinearPMap.mem_graph_iff]
  constructor
  · intro h
    have hid : ∀ x : S.domain, ⟪g, (x : Hilbert d)⟫_ℂ = ⟪f, S x⟫_ℂ := by
      intro x
      obtain ⟨φ, rfl⟩ := e.surjective x
      simpa only [hS, he, inner_conj_symm] using congrArg conj (h φ).symm
    have hm := LinearPMap.mem_adjoint_domain_of_exists f ⟨g, hid⟩
    exact ⟨⟨f, hm⟩, rfl, LinearPMap.adjoint_apply_eq hdense ⟨f, hm⟩ hid⟩
  · rintro ⟨y, hy, hg⟩ φ
    have h := LinearPMap.adjoint_isFormalAdjoint hdense y (e φ)
    rw [hg, hS, he, hy] at h
    simpa only [inner_conj_symm] using (congrArg conj h).symm

#print axioms compact_test_adjoint_graph
end D5.S3.Quantum.Analysis.SchwartzWeakAdjoint
