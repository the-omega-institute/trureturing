/- GID: D5/S3/Topology/Separation/DisjointCopyTower
   generality: G
   mirror-B: D5/B/S3/Topology/Separation/DisjointCopyTower
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: A nonempty compact binary-copy tower contains disjoint infinite closed homeomorphic subspaces. -/

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Find

/-! The nonemptiness of the tower levels does not itself imply infinitude.
A finite level would yield a least finite level cardinality. One copy of
the next level injects into that level and misses a point of the other
nonempty copy, contradicting that least cardinality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function

namespace D5.S3.Topology.Separation.DisjointCopyTower

universe u

private theorem levels_infinite {X : Type u} [TopologicalSpace X]
    (K : ℕ → Set X) (hne : ∀ n, (K n).Nonempty)
    (hcopies : ∀ n, ∃ A B : Set X, A ⊆ K n ∧ B ⊆ K n ∧ Disjoint A B ∧
      Nonempty (K (n + 1) ≃ₜ A) ∧ Nonempty (K (n + 1) ≃ₜ B)) :
    ∀ n, (K n).Infinite := by
  classical
  intro n hfinite
  let P : ℕ → Prop := fun m => ∃ j, (K j).Finite ∧ Nat.card (K j) = m
  have hex : ∃ m, P m := ⟨Nat.card (K n), n, hfinite, rfl⟩
  obtain ⟨j, hj, hcard⟩ := Nat.find_spec hex
  obtain ⟨A, B, hA, hB, hdisj, ⟨eA⟩, ⟨eB⟩⟩ := hcopies j
  let f : K (j + 1) → K j := fun x => ⟨(eA x).val, hA (eA x).property⟩
  have hf : Injective f := by
    intro x y hxy
    apply eA.injective
    exact Subtype.ext (congrArg (fun w : K j => (w : X)) hxy)
  letI : Fintype (K j) := hj.fintype
  letI : Fintype (K (j + 1)) := Fintype.ofInjective f hf
  obtain ⟨x, hx⟩ := hne (j + 1)
  let z : K (j + 1) := ⟨x, hx⟩
  let b : K j := ⟨(eB z).val, hB (eB z).property⟩
  have hb : b ∉ range f := by
    rintro ⟨y, hy⟩
    have hv : (eA y).val = (eB z).val := congrArg Subtype.val hy
    exact Set.disjoint_left.mp hdisj (hv ▸ (eA y).property) (eB z).property
  have hlt : Nat.card (K (j + 1)) < Nat.find hex := by
    rw [← hcard]
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_of_notMem f hf hb
  have hmin : Nat.find hex ≤ Nat.card (K (j + 1)) :=
    Nat.find_min' hex ⟨j + 1, Set.toFinite _, rfl⟩
  exact Nat.not_le_of_lt hlt hmin

/-- In a Hausdorff space, a sequence of nonempty compact sets, each containing
two disjoint copies of the next, forces two disjoint infinite closed
homeomorphic subspaces. In particular the next level cannot be merely finite. -/
theorem exists_disjoint_infinite_closed_copies {X : Type u} [TopologicalSpace X] [T2Space X]
    (K : ℕ → Set X) (hcompact : ∀ n, IsCompact (K n))
    (hne : ∀ n, (K n).Nonempty)
    (hcopies : ∀ n, ∃ A B : Set X, A ⊆ K n ∧ B ⊆ K n ∧ Disjoint A B ∧
      Nonempty (K (n + 1) ≃ₜ A) ∧ Nonempty (K (n + 1) ≃ₜ B)) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ A.Infinite ∧ B.Infinite ∧
      Disjoint A B ∧ Nonempty (A ≃ₜ B) := by
  classical
  have hinfinite := levels_infinite K hne hcopies
  obtain ⟨A, B, _, _, hdisj, ⟨eA⟩, ⟨eB⟩⟩ := hcopies 0
  letI : CompactSpace (K (0 + 1)) := isCompact_iff_compactSpace.mp (hcompact (0 + 1))
  letI : CompactSpace A := eA.compactSpace
  letI : CompactSpace B := eB.compactSpace
  have hAc : IsClosed A := (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  have hBc : IsClosed B := (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  have hAi : A.Infinite := by
    intro hfin
    letI : Finite A := hfin.to_subtype
    letI : Finite (K (0 + 1)) := Finite.of_injective eA eA.injective
    exact hinfinite (0 + 1) (Set.toFinite _)
  have hBi : B.Infinite := by
    intro hfin
    letI : Finite B := hfin.to_subtype
    letI : Finite (K (0 + 1)) := Finite.of_injective eB eB.injective
    exact hinfinite (0 + 1) (Set.toFinite _)
  exact ⟨A, B, hAc, hBc, hAi, hBi, hdisj, ⟨eA.symm.trans eB⟩⟩

end D5.S3.Topology.Separation.DisjointCopyTower
