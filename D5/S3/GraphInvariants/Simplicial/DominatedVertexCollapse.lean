/- GID: D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse
   generality: G
   mirror-B: D5/B/S3/GraphInvariants/Simplicial/DominatedVertexCollapse
   mirror-E: none(waiver:finite-combinatorial-collapse)
   anchors: []
   utility: none
   digest: Finite relative simplicial collapse deletes a dominated vertex. -/

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Preorder.Finite
import Mathlib.Logic.Relation

/-!
The four collapse primitives below are adapted from TauCetiProject/TauCeti,
revision 64bb4d871548995899dee90beda88b787fafe27d:
AlgebraicTopology/SimplicialComplex/LinkStar.lean,
AlgebraicTopology/SimplicialComplex/ElementaryCollapse.lean and
AlgebraicTopology/SimplicialComplex/Collapse/Basic.lean.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors
Released under the Apache 2.0 license; the full license is retained at
`docs/reports/polarization-suppliers/tauceti-LICENSE.txt`.
Adaptation: only the deletion, free-pair and two collapse relation definitions
are retained, in this namespace and against the resolved Mathlib API.
These ports can be replaced when equivalent primitives exist in our resolved
Mathlib and direct substitutions compile, subject to frozen-content reconciliation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.GraphInvariants.Simplicial.DominatedVertexCollapse

universe u
open Finset

/-- The deletion of a simplex retains exactly the faces not containing it. -/
def deletion {ι : Type u}
    (K : PreAbstractSimplicialComplex ι) (σ : Finset ι) : PreAbstractSimplicialComplex ι where
  faces := {ρ | ρ ∈ K ∧ ¬ σ ⊆ ρ}
  isRelLowerSet_faces := by
    rintro a ⟨haK, haσ⟩
    refine ⟨(K.isRelLowerSet_faces haK).1, fun {b} hba hbne => ⟨?_, ?_⟩⟩
    · exact (K.isRelLowerSet_faces haK).2 hba hbne
    · exact fun h => haσ (h.trans hba)

/-- A free pair has exactly two cofaces of its lower face, including itself. -/
structure IsFreePair {ι : Type u} (K : PreAbstractSimplicialComplex ι)
    (σ τ : Finset ι) : Prop where
  lower_mem : σ ∈ K
  upper_mem : τ ∈ K
  lower_ssubset_upper : σ ⊂ τ
  eq_lower_or_eq_upper : ∀ ⦃ω : Finset ι⦄, ω ∈ K → σ ⊆ ω → ω = σ ∨ ω = τ

/-- One elementary collapse deletes a free lower face and its unique proper coface. -/
def ElementaryCollapsesTo {ι : Type u}
    (K L : PreAbstractSimplicialComplex ι) : Prop :=
  ∃ (σ τ : Finset ι), IsFreePair K σ τ ∧ L = deletion K σ

/-- A finite, possibly empty, sequence of elementary collapses. -/
def CollapsesTo {ι : Type u}
    (K L : PreAbstractSimplicialComplex ι) : Prop :=
  Relation.ReflTransGen ElementaryCollapsesTo K L

/-- A finite complex collapses to the deletion of a vertex whose every face
can be extended by a distinct fixed vertex. Faces away from the deleted vertex
remain throughout the sequence. No face or vertex is required to exist. -/
theorem collapsesTo_deletion_of_vertex_domination
    {ι : Type u} [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) (hfin : K.faces.Finite)
    (v w : ι) (hvw : v ≠ w)
    (hdom : ∀ A : Finset ι, A ∈ K → v ∈ A → insert w A ∈ K) :
    CollapsesTo K (deletion K {v}) := by
  classical
  generalize hn : K.faces.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | h n ih =>
    let active : Set (Finset ι) := {A | A ∈ K ∧ v ∈ A ∧ w ∉ A}
    by_cases ha : active.Nonempty
    · obtain ⟨A, hA⟩ := ha
      have hafin : active.Finite := hfin.subset (fun _ h => h.1)
      obtain ⟨σ, _, hmax⟩ := hafin.exists_le_maximal hA
      have hσ : σ ∈ K ∧ v ∈ σ ∧ w ∉ σ := hmax.1
      have hfree : IsFreePair K σ (insert w σ) := by
        refine ⟨hσ.1, hdom σ hσ.1 hσ.2.1, ssubset_insert hσ.2.2, ?_⟩
        intro ω hω hσω
        by_cases hwω : w ∈ ω
        · have hσerase : σ ⊆ ω.erase w := subset_erase.mpr ⟨hσω, hσ.2.2⟩
          have hverase : v ∈ ω.erase w := hσerase hσ.2.1
          have herase : ω.erase w ∈ active :=
            ⟨(K.isRelLowerSet_faces hω).2 (erase_subset _ _) ⟨v, hverase⟩,
              hverase, notMem_erase _ _⟩
          have heq : ω.erase w = σ :=
            Finset.Subset.antisymm (hmax.2 herase hσerase) hσerase
          right
          rw [← insert_erase hwω, heq]
        · left
          exact Finset.Subset.antisymm (hmax.2 ⟨hω, hσω hσ.2.1, hwω⟩ hσω) hσω
      let L := deletion K σ
      have hLsub : L.faces ⊆ K.faces := fun _ h => h.1
      have hLfin : L.faces.Finite := hfin.subset hLsub
      have hLlt : L.faces.ncard < n := by
        rw [← hn]
        apply Set.ncard_lt_ncard _ hfin
        refine ⟨hLsub, ?_⟩
        intro h
        exact (h hσ.1).2 Finset.Subset.rfl
      have hLdom : ∀ B : Finset ι, B ∈ L → v ∈ B → insert w B ∈ L := by
        intro B hB hvB
        exact ⟨hdom B hB.1 hvB,
          fun h => hB.2 ((subset_insert_iff_of_notMem hσ.2.2).mp h)⟩
      have htarget : deletion L {v} = deletion K {v} := by
        apply SetLike.ext
        intro B
        change ((B ∈ K ∧ ¬ σ ⊆ B) ∧ ¬ ({v} : Finset ι) ⊆ B) ↔
          B ∈ K ∧ ¬ ({v} : Finset ι) ⊆ B
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · rintro ⟨hB, hvB⟩
          exact ⟨⟨hB, fun h => hvB (singleton_subset_iff.mpr (h hσ.2.1))⟩, hvB⟩
      have htail : CollapsesTo L (deletion L {v}) :=
        ih L.faces.ncard hLlt L hLfin hLdom rfl
      rw [htarget] at htail
      exact Relation.ReflTransGen.head ⟨σ, insert w σ, hfree, rfl⟩ htail
    · have htarget : K = deletion K {v} := by
        apply SetLike.ext
        intro B
        change B ∈ K ↔ B ∈ K ∧ ¬ ({v} : Finset ι) ⊆ B
        refine ⟨fun hB => ⟨hB, ?_⟩, fun h => h.1⟩
        intro hvB
        have hvface : ({v} : Finset ι) ∈ K :=
          (K.isRelLowerSet_faces hB).2 hvB (singleton_nonempty v)
        exact ha ⟨{v}, hvface, mem_singleton_self _, by simpa using hvw.symm⟩
      rw [← htarget]
      exact Relation.ReflTransGen.refl

end D5.S3.GraphInvariants.Simplicial.DominatedVertexCollapse
