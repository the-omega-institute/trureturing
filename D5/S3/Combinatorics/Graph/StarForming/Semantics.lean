/- GID: D5/S3/Combinatorics/Graph/StarForming/Semantics
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Semantics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Transport the exact port-composition proof to canonical finite graph invariants. -/

import D5.S3.Combinatorics.Graph.StarForming.ExactCard
import D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting

/-!
The supplier's set-valued local predicate and the canonical non-induced-star
predicate describe the same selections. Minimality is transported in both
directions, including the empty vertex type, before taking the finite maximum.
The composition proof is received from subquorum-colorings revision
48728b42d39ab3de5de251c61da5a404ec418a69; this file supplies its canonical bridge.
-/

namespace D5.S3.Combinatorics.Graph.StarForming

open StarFormingDissociationRefutation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The local neighbor-count and existential-witness presentations agree. -/
theorem forms_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Amplification.Forms G (↑S : Set V) ↔ IsStarForming G 2 S := by
  rw [starForming_two_iff]
  constructor
  · intro h x hx
    rcases h x hx with ⟨a, ha, b, hb, hab, hxa, hxb⟩ | ⟨c, hc, hxc, l, hl, hcl⟩
    · exact Or.inl (Nat.succ_le_iff.mpr (Finset.one_lt_card.mpr
        ⟨a, Finset.mem_filter.mpr ⟨ha, hxa⟩,
          b, Finset.mem_filter.mpr ⟨hb, hxb⟩, hab⟩))
    · exact Or.inr ⟨c, hc, hxc, Finset.one_le_card.mpr
        ⟨l, Finset.mem_filter.mpr ⟨hl, hcl⟩⟩⟩
  · intro h x hx
    rcases h x hx with hd | ⟨c, hc, hxc, hd⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
        1 < (S.filter (G.Adj x)).card)
      exact Or.inl ⟨a, (Finset.mem_filter.mp ha).1,
        b, (Finset.mem_filter.mp hb).1, hab,
        (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩
    · obtain ⟨l, hl⟩ := Finset.one_le_card.mp hd
      exact Or.inr ⟨c, hc, hxc, l,
        (Finset.mem_filter.mp hl).1, (Finset.mem_filter.mp hl).2⟩

/-- Set minimality ranges over precisely the same finite subsets. -/
theorem minimal_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Amplification.Minimal G (↑S : Set V) ↔ IsMinimalStarForming G 2 S := by
  classical
  constructor
  · rintro ⟨hf, hm⟩
    refine ⟨(forms_iff G S).mp hf, ?_⟩
    intro T hT hfT
    exact hm (↑T) (Finset.coe_ssubset.mpr hT) ((forms_iff G T).mpr hfT)
  · rintro ⟨hf, hm⟩
    refine ⟨(forms_iff G S).mpr hf, ?_⟩
    intro T hT hfT
    let U : Finset V := Finset.univ.filter (· ∈ T)
    have hU : (↑U : Set V) = T := by ext x; simp [U]
    have hproper : U ⊂ S := Finset.coe_ssubset.mp (hU ▸ hT)
    exact hm U hproper ((forms_iff G U).mp (hU ▸ hfT))

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
