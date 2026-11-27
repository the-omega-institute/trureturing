/- GID: D5/S3/Topology/CofaceComparisonObstruction
   generality: G
   mirror-B: D5/B/S3/Topology/CofaceComparisonObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: A failed coface comparison has a witness bounded by the simplex dimension. -/

module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import OmegaBuild.Commands

/-! Local obstruction detection for selectable cofaces in Question 6.3 of
Mosquera-Lois and Tanaka. An incomparable requirement forces enlargement by
its union with the currently forced face. -/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace D5.S3.Topology.CofaceComparisonObstruction

variable {V : Type*}

/-- If no face containing `s` is comparable to all prescribed cofaces, a
subfamily of at most one plus the maximum number of vertices available for
enlarging `s` already rules out every extension. In a two-dimensional
complex a singleton therefore needs at most three conflicting requirements. -/
theorem exists_small_infeasible_family
    (K : PreAbstractSimplicialComplex V) (bound : ℕ)
    (requirements : Finset (Finset V)) {s : Finset V} (hs : s ∈ K)
    (hbound : ∀ t ∈ K, s ⊆ t → t.card ≤ bound)
    (hinfeasible : ∀ t ∈ K, s ⊆ t →
      ¬ ∀ b ∈ requirements, b ⊆ t ∨ t ⊆ b) :
    ∃ witness ⊆ requirements, witness.card ≤ bound + 1 - s.card ∧
      ∀ t ∈ K, s ⊆ t → ¬ ∀ b ∈ witness, b ⊆ t ∨ t ⊆ b := by
  classical
  have find_witness (fuel : ℕ) :
      ∀ current ∈ K, s ⊆ current → fuel = bound + 1 - current.card →
        (∀ t ∈ K, current ⊆ t → ¬ ∀ b ∈ requirements, b ⊆ t ∨ t ⊆ b) →
        ∃ witness ⊆ requirements, witness.card ≤ fuel ∧
          ∀ t ∈ K, current ⊆ t → ¬ ∀ b ∈ witness, b ⊆ t ∨ t ⊆ b := by
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro current hcurrent hsc hfuel hfail
      have hbnd := hbound current hcurrent hsc
      obtain ⟨b, hb, hbc, hcb⟩ : ∃ b ∈ requirements, ¬ b ⊆ current ∧ ¬ current ⊆ b := by
        simpa only [not_forall, not_or, exists_prop] using hfail current hcurrent Finset.Subset.rfl
      let larger := current ∪ b
      have hgrow : current.card < larger.card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.subset_union_left, ?_⟩
        intro he
        exact hbc (he.symm ▸ Finset.subset_union_right)
      have forced {t : Finset V} (hct : current ⊆ t) (htb : b ⊆ t ∨ t ⊆ b) : larger ⊆ t :=
        Finset.union_subset hct (htb.resolve_right fun h => hcb (hct.trans h))
      by_cases hlarger : larger ∈ K
      · have hsl : s ⊆ larger := hsc.trans Finset.subset_union_left
        have hremaining := hbound larger hlarger hsl
        have hsmaller : bound + 1 - larger.card < fuel := by omega
        obtain ⟨w, hw, hwcard, hwfail⟩ := ih _ hsmaller larger hlarger hsl rfl
          (fun t ht hlt => hfail t ht (Finset.subset_union_left.trans hlt))
        have hcard := Finset.card_insert_le b w
        refine ⟨insert b w, Finset.insert_subset hb hw, by omega, ?_⟩
        intro t ht hst hgood
        have hlt := forced hst (hgood b (Finset.mem_insert_self _ _))
        exact hwfail t ht hlt (fun a ha => hgood a (Finset.mem_insert_of_mem ha))
      · refine ⟨{b}, Finset.singleton_subset_iff.mpr hb, ?_, ?_⟩
        · simp only [Finset.card_singleton]
          omega
        · intro t ht hst hgood
          have hlt := forced hst (hgood b (Finset.mem_singleton_self _))
          exact hlarger ((K.isRelLowerSet_faces ht).2 hlt
            ((K.isRelLowerSet_faces hcurrent).1.mono Finset.subset_union_left))
  exact find_witness _ s hs Finset.Subset.rfl rfl hinfeasible

end D5.S3.Topology.CofaceComparisonObstruction
