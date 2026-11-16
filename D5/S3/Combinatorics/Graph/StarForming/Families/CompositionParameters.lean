/- GID: D5/S3/Combinatorics/Graph/StarForming/Families/CompositionParameters
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Families/CompositionParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact canonical maxima for arbitrary interfaces between H0 blocks. -/

import D5.S3.Combinatorics.Graph.StarForming.Semantics
import D5.S3.Combinatorics.Graph.StarForming.ExactCard
import Mathlib.Tactic.NormNum

namespace D5.S3.Combinatorics.Graph.StarForming
open StarFormingDissociationRefutation

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable instance {I : Type*} (R : I → I → Prop) :
    DecidableRel (Amplification.family R).Adj := Classical.decRel _

/-- Exact canonical SF for every directed interface, including zero blocks
and same-block relation entries. No connectivity hypothesis is introduced. -/
theorem sf_family {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) :
    SF (Amplification.family R) 2 = 6 * Fintype.card I := by
  classical
  obtain ⟨hupper, S, hminimal, hcard⟩ := Composition.exact_composition_card R
  apply le_antisymm
  · apply Finset.sup_le
    intro T hT
    exact hupper T ((minimal_iff _ T).mpr (Finset.mem_filter.mp hT).2)
  · rw [← hcard]
    exact Finset.le_sup (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), (minimal_iff _ S).mp hminimal⟩)

/-- Inter-block edges cannot enlarge the dissociation optimum. Selecting the
entire first bipartition side attains five vertices per block for every R. -/
theorem beta_family {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) :
    beta (Amplification.family R) 2 = 5 * Fintype.card I := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    have hi := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp
      (Finset.mem_filter.mp hS).2
    rw [Composition.card_eq_sum_blocks]
    calc
      ∑ i : I, (Composition.blockSelection (↑S) i).card ≤ ∑ _ : I, 5 := by
        apply Finset.sum_le_sum
        intro i _
        let T := Composition.blockSelection (↑S) i
        have hmem (v : Fin 10) : v ∈ T ↔ (i, v) ∈ S := by
          simp [T, Composition.blockSelection]
        have hT : IsKIndependent Amplification.base 2 T := by
          apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
          intro v hv a ha b hb hva hvb
          exact congrArg Prod.snd
            (hi (i, v) ((hmem v).mp hv) (i, a) ((hmem a).mp ha)
              (i, b) ((hmem b).mp hb) (Or.inl ⟨rfl, hva⟩) (Or.inl ⟨rfl, hvb⟩))
        exact (Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.subset_univ T), hT⟩)).trans h0_properties.2.2
      _ = 5 * Fintype.card I := by simp [Nat.mul_comm]
  · let A : Finset (I × Fin 10) := Finset.univ.product {0, 1, 2, 3, 4}
    have hside : ∀ v ∈ ({0, 1, 2, 3, 4} : Finset (Fin 10)),
        ∀ w ∈ ({0, 1, 2, 3, 4} : Finset (Fin 10)), ¬ Amplification.base.Adj v w := by
      decide +kernel
    have hno (v : I × Fin 10) (hv : v ∈ A) (w : I × Fin 10) (hw : w ∈ A) :
        ¬ (Amplification.family R).Adj v w := by
      have hv' := (Finset.mem_product.mp hv).2
      have hw' := (Finset.mem_product.mp hw).2
      rintro (⟨_, he⟩ | ⟨he, _, _⟩ | ⟨_, he, _⟩)
      · exact hside v.2 hv' w.2 hw' he
      · rw [he] at hv'; norm_num at hv'
      · rw [he] at hw'; norm_num at hw'
    have hi : IsKIndependent (Amplification.family R) 2 A := by
      intro v hv
      have he : A.filter ((Amplification.family R).Adj v) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun w hw => hno v hv w hw)
      simp [he]
    have hc : A.card = 5 * Fintype.card I := by simp [A, Nat.mul_comm]
    rw [← hc]
    exact Finset.le_sup (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ A), hi⟩)

end D5.S3.Combinatorics.Graph.StarForming
