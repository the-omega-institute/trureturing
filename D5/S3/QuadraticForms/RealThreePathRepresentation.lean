/- GID: D5/S3/QuadraticForms/RealThreePathRepresentation
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/RealThreePathRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original real-linear Hilbert models of arbitrary-marker three-path balance. -/

module

public import D5.S3.QuadraticForms.RealThreePathPolar
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic

/-! Radical descent retains the original real scalar action and labels in the Hilbert model. -/

public section

noncomputable section

namespace D5.S3.QuadraticForms.RealThreePathRepresentation

open RealThreePathPolar
open ThreeWayPositiveKernel

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- A minimal complete Hilbert model with the original real-linear label map. -/
structure HilbertModel (U : V → V) (q : V → ℝ) where
  carrier : Type v
  [normed : NormedAddCommGroup carrier]
  [innerProduct : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  label : V →ₗ[ℝ] carrier
  normSq : ∀ x, q x = q 0 + ‖label x‖ ^ 2
  phase : ∀ x, label (U x) = omega • label x
  minimal : (Submodule.span ℂ (Set.range label)).topologicalClosure = ⊤

attribute [instance] HilbertModel.normed HilbertModel.innerProduct HilbertModel.complete

private theorem marker_descent (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (U : V → V)
    (ht : ∀ x y, B x y + B x (U y) + B (U x) y = 0) :
    ∃ T : (V ⧸ B.ker) →ₗ[ℝ] (V ⧸ B.ker),
      ∀ x, T (B.ker.mkQ x) = B.ker.mkQ (U x) := by
  let N := B.ker
  let π := N.mkQ
  have heq (x y : V) (hxy : π x = π y) : π (U x) = π (U y) := by
    apply (Submodule.Quotient.eq N).mpr
    have hh := (Submodule.Quotient.eq N).mp hxy
    change B (x - y) = 0 at hh
    change B (U x - U y) = 0
    ext z
    have hz := congrArg (fun f => f z) hh
    simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply] at hz ⊢
    have hUz := congrArg (fun f => f (U z)) hh
    simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply] at hUz
    linarith [ht x z, ht y z]
  let f : V ⧸ N → V ⧸ N := fun z => Quotient.liftOn z (fun x => π (U x))
    (fun x y hxy => heq x y ((Submodule.Quotient.eq N).mpr
      ((Submodule.quotientRel_def N).mp hxy)))
  have hf (x : V) : f (π x) = π (U x) := rfl
  have ha (x y : V) : π (U (x + y)) = π (U x) + π (U y) := by
    rw [← map_add]
    apply (Submodule.Quotient.eq N).mpr
    change B (U (x + y) - (U x + U y)) = 0
    ext z
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.zero_apply]
    have hh := ht (x + y) z
    simp only [map_add, LinearMap.add_apply] at hh
    linarith [ht x z, ht y z]
  have hs (t : ℝ) (x : V) : π (U (t • x)) = t • π (U x) := by
    rw [← map_smul]
    apply (Submodule.Quotient.eq N).mpr
    change B (U (t • x) - t • U x) = 0
    ext z
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, LinearMap.zero_apply]
    have hh := ht (t • x) z
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hh
    linarith [ht x z]
  refine ⟨{ toFun := f
            map_add' := ?_
            map_smul' := ?_ }, hf⟩
  · intro x y
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    rw [← map_add, hf, hf, hf]
    exact ha x y
  · intro t x
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    rw [← map_smul, hf, hf]
    exact hs t x

private theorem additive_label_real {W : Type*} [AddCommGroup W] [Module ℝ W]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (g : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : W →+ H)
    (hn : ∀ x, g x x = ‖f x‖ ^ 2) : ∀ (t : ℝ) (x : W), f (t • x) = t • f x := by
  intro t x
  let a : ℝ →+ H := AddMonoidHom.mk' (fun s => f (s • x)) (by
    intro s t; simp [add_smul, map_add])
  have hb (s : ℝ) : ‖a s‖ ≤ ‖f x‖ * ‖s‖ := by
    have he := hn (s • x)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hn] at he
    have hs : ‖s‖ ^ 2 = s ^ 2 := Real.norm_eq_abs s ▸ sq_abs s
    change ‖f (s • x)‖ ≤ ‖f x‖ * ‖s‖
    nlinarith [norm_nonneg (f (s • x)), norm_nonneg (f x), norm_nonneg s,
      mul_nonneg (norm_nonneg (f x)) (norm_nonneg s)]
  have hc : Continuous a := AddMonoidHomClass.continuous_of_bound a ‖f x‖ hb
  simpa [a] using map_real_smul a hc t (1 : ℝ)

end D5.S3.QuadraticForms.RealThreePathRepresentation
