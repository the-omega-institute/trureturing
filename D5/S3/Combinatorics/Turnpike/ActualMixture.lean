/- GID: D5/S3/Combinatorics/Turnpike/ActualMixture
   generality: G
   mirror-B: none(waiver:covered-by-distinct-full-mixture-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite convex mixtures of whole actual rulers -/

module
public import D5.S3.Combinatorics.Turnpike.PrunedTriangleLP

/-! Omega original.
# Finite convex mixtures of whole actual rulers
-/
@[expose] public section
namespace Omega.Turnpike
open scoped BigOperators
noncomputable section

def ActualMixture {n d : ℕ} (y : Fin d → ℝ) (μ : Fin d → ℕ)
    (P : Assignment n d) : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∃ (w : Fin K → ℝ) (x : Fin K → Fin n → ℝ),
    (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧ (∀ k, Realizes y μ (x k)) ∧
    ∀ e q, P e q = ∑ k, w k * (if x k e.1.2 - x k e.1.1 = y q then 1 else 0)

theorem mixture_forbidden {n d : ℕ} {y : Fin d → ℝ} {μ : Fin d → ℕ}
    {P : Assignment n d} (h : ActualMixture y μ P) (e : Interval n) (q : Fin d)
    (hf : ∀ x : Fin n → ℝ, Realizes y μ x → x e.1.2 - x e.1.1 ≠ y q) :
    P e q = 0 := by
  classical
  obtain ⟨K,_,w,x,_,_,hx,hP⟩ := h
  rw [hP e q]
  exact Finset.sum_eq_zero fun k _ => by simp [hf (x k) (hx k)]
end
end Omega.Turnpike
