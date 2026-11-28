/- GID: D5/S3/Combinatorics/Turnpike/SubsetTriangleLP
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Subset transport cuts and finite support certificates -/

module

public import D5.S3.Combinatorics.Turnpike.PrunedTriangleLP
public import Mathlib.Data.Finset.Powerset

/-! Omega original.
# Subset transport cuts and finite support certificates

Completion sets use the entire guarded numerical relation with the propagated
three-edge product mask. Empty subsets and empty completions are included.
-/
@[expose] public section
namespace Omega.Turnpike
open scoped BigOperators
noncomputable section

def SubsetCompletion {n d : ℕ} (y : Fin d → ℝ) (μ : Fin d → ℕ)
    (τ : Triangle n) (u v w : Fin 3) (U V : Finset (Fin d)) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun c => ∃ r : Relation y μ,
    ProductAllowed μ τ r.1 ∧ coordinate u r.1 ∈ U ∧
      coordinate v r.1 ∈ V ∧ coordinate w r.1 = c

def SubsetCuts {n d : ℕ} (y : Fin d → ℝ) (μ : Fin d → ℕ)
    (P : Assignment n d) : Prop :=
  ∀ τ : Triangle n, ∀ u v w : Fin 3, u < v → w ≠ u → w ≠ v →
    ∀ U V : Finset (Fin d),
    (∑ a ∈ U, P (edge τ u) a) + (∑ b ∈ V, P (edge τ v) b) ≤
      1 + ∑ c ∈ SubsetCompletion y μ τ u v w U V, P (edge τ w) c

def tableCompletion {d : ℕ} (B : Finset (Fin d × Fin d × Fin d))
    (u v w : Fin 3) (U V : Finset (Fin d)) : Finset (Fin d) :=
  (B.filter fun r => coordinate u r ∈ U ∧ coordinate v r ∈ V).image (coordinate w)

/-- A finite table of valid atoms suffices; omitted atoms only strengthen the checks. -/
theorem subsetCuts_of_support {n d : ℕ} {y : Fin d → ℝ} {μ : Fin d → ℕ}
    (P : Assignment n d) (S : Interval n → Finset (Fin d))
    (B : Triangle n → Finset (Fin d × Fin d × Fin d))
    (nonneg : ∀ e q, 0 ≤ P e q)
    (zeros : ∀ e q, q ∉ S e → P e q = 0)
    (valid : ∀ τ r, r ∈ B τ →
      y r.1 + y r.2.1 = y r.2.2 ∧ (r.1 ≠ r.2.1 ∨ 2 ≤ μ r.1) ∧
        ProductAllowed μ τ r)
    (checks : ∀ τ u v w, u < v → w ≠ u → w ≠ v →
      ∀ U ∈ (S (edge τ u)).powerset, ∀ V ∈ (S (edge τ v)).powerset,
        (∑ a ∈ U, P (edge τ u) a) + (∑ b ∈ V, P (edge τ v) b) ≤
          1 + ∑ c ∈ tableCompletion (B τ) u v w U V, P (edge τ w) c) :
    SubsetCuts y μ P := by
  classical
  intro τ u v w huv hwu hwv U V
  let U₀ := U ∩ S (edge τ u)
  let V₀ := V ∩ S (edge τ v)
  have hsum (e : Interval n) (A : Finset (Fin d)) :
      (∑ q ∈ A ∩ S e, P e q) = ∑ q ∈ A, P e q := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro q hq hn
    exact zeros e q (fun hs => hn (Finset.mem_inter.mpr ⟨hq, hs⟩))
  have hc : tableCompletion (B τ) u v w U₀ V₀ ⊆
      SubsetCompletion y μ τ u v w U V := by
    intro c hc
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hr,hU,hV⟩ := Finset.mem_filter.mp hr
    obtain ⟨he,hg,hm⟩ := valid τ r hr
    simp only [SubsetCompletion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨r,he,hg⟩,hm,(Finset.mem_inter.mp hU).1,
      (Finset.mem_inter.mp hV).1,rfl⟩
  have h := checks τ u v w huv hwu hwv U₀
    (Finset.mem_powerset.mpr Finset.inter_subset_right) V₀
    (Finset.mem_powerset.mpr Finset.inter_subset_right)
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hc
    (fun q _ _ => nonneg (edge τ w) q)
  dsimp only [U₀,V₀] at h
  rw [hsum,hsum] at h
  linarith

/-- Weighted marginal regrouping for arbitrary finite labels. -/
theorem weighted_marginal {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (T : α → ℝ) (p : β → ℝ) (z : β → ℝ)
    (hm : ∀ q, (∑ r, if f r = q then T r else 0) = p q) :
    (∑ r, z (f r) * T r) = ∑ q, z q * p q := by
  classical
  calc
    _ = ∑ q, ∑ r ∈ Finset.univ.filter (fun r => f r = q), z (f r) * T r :=
      (Finset.sum_fiberwise Finset.univ f (fun r => z (f r) * T r)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_filter, ← hm q, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : f r = q <;> simp [h]
end
end Omega.Turnpike
