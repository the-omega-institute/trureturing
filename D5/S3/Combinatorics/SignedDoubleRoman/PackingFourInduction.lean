/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingFourInduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingFourInduction
   mirror-E: none(waiver:four-centre-induction)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Four saturated centres give an isolated ten-vertex reduction with four selections. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingFourCentres
import D5.S3.Combinatorics.SignedDoubleRoman.PackingInductionCore
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingFourInduction

open Finset MixedDefs PackingFourCentres PackingInductionCore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The eight centre attachments force either a thin clique vertex or two attachments everywhere. -/
theorem four_centre_case (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S K A B : Finset V) (u v : V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S) (hno : C.CliqueFreeOn (S : Set V) 4)
    (hR : insert u (insert v (K ∪ A ∪ B)) ⊆ S)
    (hK : K.card = 4) (hA : A.card = 2) (hB : B.card = 2)
    (hKA : Disjoint K A) (hKB : Disjoint K B) (hAB : Disjoint A B)
    (hu : u ∉ K ∪ A ∪ B) (hv : v ∉ K ∪ A ∪ B) (huv : u ≠ v)
    (hDu : D.neighborFinset u = insert v A)
    (hDv : D.neighborFinset v = insert u B)
    (hDA : ∀ r ∈ A, D.neighborFinset r ⊆ insert u K)
    (hDB : ∀ r ∈ B, D.neighborFinset r ⊆ insert v K)
    (hDC : ∀ r ∈ A ∪ B, D.degree r = 3)
    (hpair : ∀ r ∈ A ∪ B, (D.neighborFinset r ∩ K).card = 2)
    (hCK : ∀ r ∈ K, C.neighborFinset r ⊆ K)
    (hDK : ∀ r ∈ K, D.neighborFinset r ⊆ A ∪ B) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let R := insert u (insert v (K ∪ A ∪ B))
  have hmemu : u ∈ S := hR (by simp)
  have hmemv : v ∈ S := hR (by simp)
  have huA : u ∉ A := fun h => hu (by simp [h])
  have huB : u ∉ B := fun h => hu (by simp [h])
  have hvA : v ∉ A := fun h => hv (by simp [h])
  have hvB : v ∉ B := fun h => hv (by simp [h])
  have hCu : C.neighborFinset u = ∅ := by
    have hd := hdegree u hmemu
    change (C.neighborFinset u).card + (D.neighborFinset u).card ≤ 3 at hd
    rw [hDu, card_insert_of_notMem hvA, hA] at hd
    exact card_eq_zero.mp (by omega)
  have hCv : C.neighborFinset v = ∅ := by
    have hd := hdegree v hmemv
    change (C.neighborFinset v).card + (D.neighborFinset v).card ≤ 3 at hd
    rw [hDv, card_insert_of_notMem huB, hB] at hd
    exact card_eq_zero.mp (by omega)
  have hCC : ∀ r ∈ A ∪ B, C.neighborFinset r = ∅ := by
    intro r hr
    have hrS : r ∈ S := hR (by simp only [mem_insert, mem_union] at hr ⊢; tauto)
    have hd := hdegree r hrS
    rw [hDC r hr] at hd
    exact card_eq_zero.mp (by change (C.neighborFinset r).card + 3 ≤ 3 at hd; omega)
  have hclosed : ∀ r ∈ R, C.neighborFinset r ∪ D.neighborFinset r ⊆ R := by
    intro r hr
    simp only [R, mem_insert, mem_union] at hr
    rcases hr with hr | hr | (hr | hr) | hr
    · subst r
      simp only [hCu, empty_union, hDu]
      intro x hx
      rcases mem_insert.mp hx with rfl | hx <;> simp [R, hx]
    · subst r
      simp only [hCv, empty_union, hDv]
      intro x hx
      rcases mem_insert.mp hx with rfl | hx <;> simp [R, hx]
    · apply union_subset
      · exact (hCK r hr).trans (by intro x hx; simp [R, hx])
      · exact (hDK r hr).trans (by
          intro x hx
          simp only [R, mem_insert, mem_union] at hx ⊢
          tauto)
    · rw [hCC r (mem_union_left _ hr), empty_union]
      exact (hDA r hr).trans (by
        intro x hx
        simp only [R, mem_insert, mem_union] at hx ⊢
        tauto)
    · rw [hCC r (mem_union_right _ hr), empty_union]
      exact (hDB r hr).trans (by
        intro x hx
        simp only [R, mem_insert, mem_union] at hx ⊢
        tauto)
  have hselection : ∃ Q : Finset V, Q ⊆ R ∧ MixedAdmissible C D Q ∧
      R.card ≤ 3 * Q.card := by
    by_cases hthin : ∃ z ∈ K, (D.neighborFinset z).card ≤ 1
    · obtain ⟨z, hz, hDz⟩ := hthin
      have hp : ∃ p ∈ A, ¬ D.Adj p z := by
        by_contra! hh
        have hsub : A ⊆ D.neighborFinset z := by
          intro p hp
          exact (D.mem_neighborFinset _ _).mpr (hh p hp).symm
        have hcard := card_le_card hsub
        omega
      obtain ⟨p, hp, hpz⟩ := hp
      obtain ⟨q, hq⟩ := card_pos.mp (by omega : 0 < B.card)
      exact ⟨{u, z, p, q}, meeting_edges_selection C D K A B u v z p q
        hK hA hB hKA hKB hAB hu hv huv hz hp hq hDu hDv hDK hDA hDB
        hDz hpz hCu hCC (hCK z hz) hclosed⟩
    · have hlarge : ∀ r ∈ K, 2 ≤ (D.neighborFinset r).card := by
        intro r hr
        have hn : ¬(D.neighborFinset r).card ≤ 1 := fun h => hthin ⟨r, hr, h⟩
        omega
      have hcount : (∑ r ∈ K, (D.neighborFinset r).card) = 8 := by
        have hdouble := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := K) (t := A ∪ B) D.Adj
        have habove : ∀ r ∈ K, (A ∪ B).bipartiteAbove D.Adj r = D.neighborFinset r := by
          intro r hr
          ext t
          simp only [bipartiteAbove, mem_filter, SimpleGraph.mem_neighborFinset]
          exact ⟨And.right, fun h => ⟨hDK r hr ((D.mem_neighborFinset _ _).mpr h), h⟩⟩
        have hbelow : ∀ r ∈ A ∪ B, K.bipartiteBelow D.Adj r = D.neighborFinset r ∩ K := by
          intro r hr
          ext t
          simp only [bipartiteBelow, mem_filter, mem_inter, SimpleGraph.mem_neighborFinset]
          constructor
          · rintro ⟨ht, h⟩
            exact ⟨h.symm, ht⟩
          · rintro ⟨h, ht⟩
            exact ⟨ht, h.symm⟩
        calc
          (∑ r ∈ K, (D.neighborFinset r).card) =
              ∑ r ∈ K, ((A ∪ B).bipartiteAbove D.Adj r).card := by
                apply sum_congr rfl
                intro r hr
                rw [habove r hr]
          _ = ∑ r ∈ A ∪ B, (K.bipartiteBelow D.Adj r).card := hdouble
          _ = ∑ _r ∈ A ∪ B, 2 := by
            apply sum_congr rfl
            intro r hr
            rw [hbelow r hr, hpair r hr]
          _ = 8 := by simp [card_union_of_disjoint hAB, hA, hB]
      have hsmall : ∀ r ∈ K, (D.neighborFinset r).card ≤ 2 := by
        intro r hr
        have hsumlow : ∑ t ∈ K.erase r, 2 ≤ ∑ t ∈ K.erase r, (D.neighborFinset t).card :=
          sum_le_sum (fun t ht => hlarge t (mem_of_mem_erase ht))
        have hsum : ∑ t ∈ K, (D.neighborFinset t).card =
            (D.neighborFinset r).card + ∑ t ∈ K.erase r, (D.neighborFinset t).card :=
          (sum_erase_add K (fun t => (D.neighborFinset t).card) hr).symm.trans (Nat.add_comm _ _)
        have hconst : (∑ _t ∈ K.erase r, 2) = 6 := by
          simp [card_erase_of_mem hr, hK]
        omega
      exact ⟨A ∪ B, disjoint_edges_selection C D K A B u v hK hA hB hKA hKB hAB hu hv
        hDu hDv hsmall (fun r hr => by
          rcases mem_union.mp hr with hr | hr
          · exact (hDA r hr).trans (by intro t ht; simp only [mem_insert] at ht ⊢; tauto)
          · exact (hDB r hr).trans (by intro t ht; simp only [mem_insert] at ht ⊢; tauto))
          hCC hclosed⟩
  obtain ⟨Q, hQ, hgood, hcount⟩ := hselection
  apply clean_reduce C D S R Q ih hR hQ ⟨u, by simp [R]⟩ hcount
    hsupport hdegree hgood.1 _ _ hno
  · intro q hq t ht
    have htR := (mem_sdiff.mp ht).2
    constructor
    · intro h
      exact htR (hclosed q (hQ hq) (mem_union_left _ ((C.mem_neighborFinset _ _).mpr h)))
    · intro h
      exact htR (hclosed q (hQ hq) (mem_union_right _ ((D.mem_neighborFinset _ _).mpr h)))
  · intro r hr
    have hempty : D.neighborFinset r ∩ (S \ R) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact (mem_sdiff.mp (mem_inter.mp ht).2).2
        (hclosed r hr (mem_union_right _ (mem_inter.mp ht).1))
    simpa [hempty] using hgood.2 r

end D5.S3.Combinatorics.SignedDoubleRoman.PackingFourInduction
