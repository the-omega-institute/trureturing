/- GID: D5/S3/FiniteGroups/FrobeniusHall
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FrobeniusHall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-point-free outside conjugation makes a finite normal subgroup a Hall subgroup. -/

import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Sylow


set_option autoImplicit false

namespace D5.S3.FiniteGroups.FrobeniusHall

/-- A finite normal subgroup on which every outside conjugation fixes only the identity
has order coprime to its index. No properness or nontriviality is required. -/
theorem coprime_card_index_of_fixedPointFree
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hfix : ∀ g : G, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1) :
    Nat.Coprime (Nat.card N) N.index := by
  classical
  apply Nat.coprime_of_dvd
  intro p hp hpN hpindex
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := default
  have hPN : ¬ (P : Subgroup G) ≤ N := by
    intro hPN
    exact P.not_dvd_index (hpindex.trans (Subgroup.index_dvd_of_le hPN))
  obtain ⟨g, hgP, hgN⟩ : ∃ g : G, g ∈ (P : Subgroup G) ∧ g ∉ N := by
    by_contra h
    apply hPN
    intro g hgP
    by_contra hgN
    exact h ⟨g, hgP, hgN⟩
  letI : MulAction (P : Subgroup G) N :=
    MulAction.compHom N
      ((MulAut.conjNormal : G →* MulAut N).comp (P : Subgroup G).subtype)
  have hone : (1 : N) ∈ MulAction.fixedPoints (P : Subgroup G) N := by
    apply MulAction.mem_fixedPoints.mpr
    intro x
    change MulAut.conjNormal (x : G) (1 : N) = 1
    exact map_one (MulAut.conjNormal (x : G) : MulAut N)
  obtain ⟨n, hn, hne⟩ :=
    P.isPGroup'.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hpN hone
  have hnfix : MulAut.conjNormal g n = n := by
    have h := MulAction.mem_fixedPoints.mp hn (⟨g, hgP⟩ : (P : Subgroup G))
    change MulAut.conjNormal g n = n at h
    exact h
  exact hne (hfix g hgN n hnfix).symm

/-- Bind-only complement consumer of the Hall step and Mathlib Schur-Zassenhaus. -/
theorem exists_right_complement'_of_fixedPointFree
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hfix : ∀ g : G, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1) :
    ∃ H : Subgroup G, N.IsComplement' H := by
  exact Subgroup.exists_right_complement'_of_coprime (N := N)
    (coprime_card_index_of_fixedPointFree N hfix)

end D5.S3.FiniteGroups.FrobeniusHall
