/- GID: D5/S3/Combinatorics/Orthogonality/PartialSpreadHoles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/PartialSpreadHoles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Universal seven-hole orthogonality from eight disjoint full incidence blocks. -/

import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! This is the universal counting argument in the supplied n7 proof.
No partial spread is sampled or assumed representative. The actual symplectic
consumer must establish the complete point and incidence hypotheses. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.Orthogonality.PartialSpreadHoles
variable {α : Type*} [DecidableEq α]

/-- The entire uncovered point set for eight full blocks. -/
def holes (E : Finset α) (L : Fin 8 → Finset α) : Finset α :=
  E \ Finset.univ.biUnion L

/-- Every eight-member partial spread with the received full incidence data
has exactly seven holes and every hole is orthogonal to every hole. -/
theorem result (E : Finset α) (orthogonal : α → α → Prop)
    [DecidableRel orthogonal] (L : Fin 8 → Finset α)
    (hE : E.card = 63) (hsub : ∀ i, L i ⊆ E)
    (hcard : ∀ i, (L i).card = 7)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (L i) (L j))
    (hhyper : ∀ e ∈ E, (E.filter (orthogonal e)).card = 31)
    (hinc : ∀ e ∈ E, ∀ i,
      ((L i).filter (orthogonal e)).card = if e ∈ L i then 7 else 3) :
    (holes E L).card = 7 ∧ ∀ x ∈ holes E L, ∀ y ∈ holes E L, orthogonal x y := by
  let U := Finset.univ.biUnion L
  have hUsub : U ⊆ E := by
    intro x hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    exact hsub i hi
  have hUcard : U.card = 56 := by
    dsimp [U]
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisjoint i j hij)]
    simp [hcard]
  have hRcard : (holes E L).card = 7 := by
    rw [holes,Finset.card_sdiff_of_subset hUsub,hE,hUcard]
  refine ⟨hRcard,?_⟩
  intro x hx
  have hxE : x ∈ E := (Finset.mem_sdiff.mp hx).1
  have hxU : x ∉ U := (Finset.mem_sdiff.mp hx).2
  have hnot (i : Fin 8) : x ∉ L i := by
    intro hi
    exact hxU (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hi⟩)
  have hfiltered : (U.filter (orthogonal x)).card = 24 := by
    dsimp [U]
    rw [Finset.filter_biUnion,
      Finset.card_biUnion (fun i _ j _ hij =>
        (hdisjoint i j hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    have hi (i : Fin 8) : ((L i).filter (orthogonal x)).card = 3 := by
      rw [hinc x hxE i,if_neg (hnot i)]
    simp [hi]
  have hfiltered_sub : U.filter (orthogonal x) ⊆ E.filter (orthogonal x) := by
    intro y hy
    have hh := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hUsub hh.1,hh.2⟩
  have hf : (holes E L).filter (orthogonal x) =
      E.filter (orthogonal x) \ U.filter (orthogonal x) := by
    ext y
    simp only [holes,U,Finset.mem_filter,Finset.mem_sdiff]
    tauto
  have hholes : ((holes E L).filter (orthogonal x)).card = (holes E L).card := by
    rw [hf,Finset.card_sdiff_of_subset hfiltered_sub,hhyper x hxE,hfiltered,hRcard]
  exact Finset.card_filter_eq_iff.mp hholes

#print axioms result
end D5.S3.Combinatorics.Orthogonality.PartialSpreadHoles
