/- GID: D5/S3/Combinatorics/Turnpike/PartialFlow
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse partial flows certify every second subset simultaneously -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetTriangleLP
public import Mathlib.Algebra.Order.BigOperators.Group.List
/-! Omega original.
# Sparse partial flows certify every second subset simultaneously
-/
@[expose] public section
namespace Omega.Turnpike
open scoped BigOperators

abbrev FlowAtom (d : ℕ) := (Fin d × Fin d × Fin d) × ℕ

def flowMass {d : ℕ} (L : List (FlowAtom d)) : ℕ := (L.map Prod.snd).sum

def flowMarginal {d : ℕ} (L : List (FlowAtom d)) (v : Fin 3) (q : Fin d) : ℕ :=
  (L.map fun a => if coordinate v a.1 = q then a.2 else 0).sum

def PartialFlowCheck {d : ℕ} (B : Finset (Fin d × Fin d × Fin d))
    (p : Fin 3 → Fin d → ℕ) (u v w : Fin 3) (U : Finset (Fin d))
    (L : List (FlowAtom d)) : Prop :=
  (∀ a ∈ L, a.1 ∈ B ∧ coordinate u a.1 ∈ U) ∧
  (∑ q ∈ U, p u q) ≤ flowMass L ∧
  (∀ q, flowMarginal L v q ≤ p v q) ∧
  (∀ q, flowMarginal L w q ≤ p w q)

instance {d : ℕ} (B : Finset (Fin d × Fin d × Fin d))
    (p : Fin 3 → Fin d → ℕ) (u v w : Fin 3) (U : Finset (Fin d))
    (L : List (FlowAtom d)) : Decidable (PartialFlowCheck B p u v w U L) := by
  unfold PartialFlowCheck
  infer_instance

private theorem list_indicator_sum {α β : Type*} [DecidableEq β]
    (L : List α) (f : α → β) (z : α → ℕ) (A : Finset β) :
    (L.map fun a => if f a ∈ A then z a else 0).sum =
      ∑ q ∈ A, (L.map fun a => if f a = q then z a else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ← ih]
    simp

/-- A separate sparse flow for U proves the cut for every V, including empty V. -/
theorem partialFlow_cut {d : ℕ} (B : Finset (Fin d × Fin d × Fin d))
    (p : Fin 3 → Fin d → ℕ) (u v w : Fin 3) (U : Finset (Fin d))
    (L : List (FlowAtom d)) (D : ℕ)
    (check : PartialFlowCheck B p u v w U L) (total : ∑ q, p v q = D)
    (V : Finset (Fin d)) :
    (∑ q ∈ U, p u q) + (∑ q ∈ V, p v q) ≤
      D + ∑ q ∈ tableCompletion B u v w U V, p w q := by
  classical
  let C := tableCompletion B u v w U V
  have point (a : FlowAtom d) (ha : a ∈ L) :
      a.2 ≤ (if coordinate v a.1 ∈ Finset.univ \ V then a.2 else 0) +
        (if coordinate w a.1 ∈ C then a.2 else 0) := by
    by_cases hv : coordinate v a.1 ∈ V
    · have hc : coordinate w a.1 ∈ C :=
        Finset.mem_image.mpr ⟨a.1, Finset.mem_filter.mpr
          ⟨(check.1 a ha).1, (check.1 a ha).2, hv⟩, rfl⟩
      simp [hv, hc]
    · simp [hv]
  have hmass : flowMass L ≤
      (∑ q ∈ Finset.univ \ V, flowMarginal L v q) +
      (∑ q ∈ C, flowMarginal L w q) := by
    unfold flowMass flowMarginal
    rw [← list_indicator_sum, ← list_indicator_sum, ← List.sum_map_add]
    exact List.sum_le_sum point
  have hv := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ \ V) => check.2.2.1 q)
  have hw := Finset.sum_le_sum (fun q (_ : q ∈ C) => check.2.2.2 q)
  have ht : (∑ q ∈ V, p v q) + (∑ q ∈ Finset.univ \ V, p v q) = D := by
    simpa only [Finset.compl_eq_univ_sdiff] using
      (Finset.sum_add_sum_compl V (p v)).trans total
  dsimp only [C] at hmass hw
  have hu := check.2.1
  omega
end Omega.Turnpike
