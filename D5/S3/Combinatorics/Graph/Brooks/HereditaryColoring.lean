/- GID: D5/S3/Combinatorics/Graph/Brooks/HereditaryColoring
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Brooks/HereditaryColoring
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum]
   utility: none
   digest: Hereditary sparse four-clique-free graphs admit three colors. -/

import D5.S3.Combinatorics.Graph.Brooks.Subcubic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Brooks.HereditaryColoring
open SimpleGraph Finset
open scoped BigOperators

/-- Every finite graph of hereditary average degree at most three is three-colorable
if it has no four-clique. Low-degree deletion reduces to the subcubic theorem. -/
theorem hereditary_sparse_three_colorable {V : Type*} [Finite V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsparse : ∀ S : Finset V,
      2*(G.induce (S : Set V)).edgeFinset.card ≤ 3*S.card)
    (hfree : G.CliqueFree 4) : G.Colorable 3 := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hcolor : ∀ S : Finset V, (G.induce (S : Set V)).Colorable 3 := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      let H := G.induce (S : Set V)
      by_cases hlow : ∃ v : S, H.degree v < 3
      · obtain ⟨v,hv⟩ := hlow
        have hsmaller := ih (S.erase v.val) (erase_ssubset v.property)
        let f : H.induce ({v}ᶜ : Set S) →g G.induce (S.erase v.val : Set V) :=
          { toFun := fun u => ⟨u.val.val, mem_erase.mpr ⟨by
              intro heq
              exact u.property (Set.mem_singleton_iff.mpr (Subtype.ext heq)),u.val.property⟩⟩
            map_rel' := by intro u w huw; exact huw }
        have hdeleted : (H.induce ({v}ᶜ : Set S)).Colorable 3 :=
          SimpleGraph.Colorable.of_hom f hsmaller
        exact hdeleted.of_induce_compl_singleton hv
      · have hmin : ∀ v : S, 3 ≤ H.degree v := by
          intro v
          by_contra hv
          exact hlow ⟨v,by omega⟩
        have hsum : (∑ v : S, H.degree v) = 2*H.edgeFinset.card :=
          H.sum_degrees_eq_twice_card_edges
        have hbound := hsparse S
        have hle : (∑ v : S, 3) ≤ ∑ v : S, H.degree v :=
          sum_le_sum (fun v _ => hmin v)
        have heq : (∑ v : S, 3) = ∑ v : S, H.degree v := by
          have hconst : (∑ _v : S, 3) = 3*S.card := by simp [Nat.mul_comm]
          change 2*H.edgeFinset.card ≤ 3*S.card at hbound
          omega
        have hreg : ∀ v : S, H.degree v=3 := by
          intro v
          exact ((sum_eq_sum_iff_of_le (fun v _ => hmin v)).mp heq v (mem_univ _)).symm
        have hmax : H.maxDegree ≤ 3 := H.maxDegree_le_of_forall_degree_le 3
          (fun v => (hreg v).le)
        have hfreeH : H.CliqueFree 4 :=
          hfree.comap ⟨(SimpleGraph.Embedding.induce (S : Set V)).toCopy⟩
        exact BrooksSubcubic.brooks_cubic H hmax hfreeH
  have hc := hcolor univ
  let f : G →g G.induce ((univ : Finset V) : Set V) :=
    { toFun := fun v => ⟨v,mem_univ _⟩
      map_rel' := by intro u v huv; exact huv }
  exact SimpleGraph.Colorable.of_hom f hc

end D5.S3.Combinatorics.Graph.Brooks.HereditaryColoring
