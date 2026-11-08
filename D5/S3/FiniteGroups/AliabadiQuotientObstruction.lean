/- GID: D5/S3/FiniteGroups/AliabadiQuotientObstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/AliabadiQuotientObstruction
   mirror-E: none(waiver:pure-finite-group-theorem)
   anchors: []
   utility: none
   digest: One nonidentity element of the commutator subgroup obstructs right quotients. -/

import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Tactic

/-! Abelianization does not suffice for quotients of two bijective enumerations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.FiniteGroups.AliabadiQuotientObstruction

/-- The complete finite nonabelian-group question, with actual multiplicities
and the literal right quotients of two bijective enumerations. -/
theorem exists_obstructed_multiset (G : Type u) [Group G] [Fintype G]
    (hna : ¬ IsMulCommutative G) :
    ∃ A : Multiset G, A.card = Fintype.card G ∧
      (A.map (Abelianization.of : G → Abelianization G)).prod = 1 ∧
      ¬ ∃ b c : Fin (Fintype.card G) → G,
        Function.Bijective b ∧ Function.Bijective c ∧
          A = (Finset.univ.val.map (fun i => b i * (c i)⁻¹)) := by
  classical
  have hcomm : commutator G ≠ ⊥ := fun h => hna ((commutator_eq_bot_iff G).mp h)
  have hntr : Nontrivial (commutator G) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hcomm
  obtain ⟨a, ha, hane⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp hntr
  have hproj : Abelianization.of a = 1 := by
    have hm : a ∈ (Abelianization.of : G →* Abelianization G).ker := by
      rwa [Abelianization.ker_of]
    exact hm
  have hn : 0 < Fintype.card G := Fintype.card_pos
  refine ⟨a ::ₘ Multiset.replicate (Fintype.card G - 1) 1, ?_, ?_, ?_⟩
  · simp only [Multiset.card_cons, Multiset.card_replicate]
    omega
  · simp [hproj]
  · rintro ⟨b, c, hb, hc, hA⟩
    let eb : Fin (Fintype.card G) ≃ G := Equiv.ofBijective b hb
    let ec : Fin (Fintype.card G) ≃ G := Equiv.ofBijective c hc
    let τ : Equiv.Perm (Fin (Fintype.card G)) := eb.trans ec.symm
    have hmove (i : Fin (Fintype.card G)) : τ i ≠ i ↔ b i * (c i)⁻¹ ≠ 1 := by
      change ec.symm (eb i) ≠ i ↔ b i * (c i)⁻¹ ≠ 1
      simp only [ne_eq, mul_inv_eq_one, Equiv.symm_apply_eq]
      rfl
    have hfilter := congrArg (fun s : Multiset G => (s.filter (fun x => x ≠ 1)).card) hA
    have hcard : τ.support.card = 1 := by
      have hleft : ((a ::ₘ Multiset.replicate (Fintype.card G - 1) 1).filter
          (fun x : G => x ≠ 1)).card = 1 := by simp [hane, Multiset.mem_replicate]
      rw [hleft, Multiset.filter_map, Multiset.card_map] at hfilter
      have heq : (Finset.univ.val.filter
          ((fun x : G => x ≠ 1) ∘ (fun i => b i * (c i)⁻¹))).card = τ.support.card := by
        change (Finset.univ.filter (fun i => b i * (c i)⁻¹ ≠ 1)).card = τ.support.card
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mem_support]
        exact (hmove i).symm
      exact heq ▸ hfilter.symm
    exact τ.card_support_ne_one hcard

end D5.S3.FiniteGroups.AliabadiQuotientObstruction
