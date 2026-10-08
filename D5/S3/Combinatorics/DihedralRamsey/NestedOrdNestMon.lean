/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedOrdNestMon
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedOrdNestMon
   mirror-E: none(waiver:ordered-nested-matching-monotone-path)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Ordered nested matching versus monotone path Ramsey equality. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedRamseyDefs
import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyLayers
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedOrdNestMon

open DihedralRamseyDefs MonotoneRamseyDefs NestedRamseyDefs Finset

/-- Conjecture 4.31 of arXiv:2604.16188. -/
theorem result : claimOrdNestMon := by
  classical
  intro a b ha _ hb
  let N := 1 + (a - 1) * (b - 1)
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    OrderedEmbeddable (nestMatching a) G ∨ OrderedEmbeddable (monoPath b) Gᶜ}
  have upper : N ∈ S := by
    intro G
    by_cases hone : b = 1
    · subst b
      right
      let ψ : Fin 1 → Fin N := fun _ => ⟨0, by simp [N]⟩
      refine ⟨ψ, ?_, ?_⟩
      · intro i j hij
        have hi := i.isLt
        have hj := j.isLt
        have h := Fin.lt_def.mp hij
        omega
      · intro i j hij
        have h := (SimpleGraph.fromRel_adj _ _ _).mp hij
        have hi := i.isLt
        have hj := j.isLt
        rcases h.2 with h | h <;> omega
    · have hb2 : 2 ≤ b := by omega
      by_cases hblue : OrderedEmbeddable (monoPath b) Gᶜ
      · exact Or.inr hblue
      left
      have labels := monotone_path_labels hb2 Gᶜ hblue
      obtain ⟨r, hr⟩ := labels
      have large : ∃ c : Fin (b - 1), a ≤ (univ.filter fun v => r v = c).card := by
        obtain ⟨c, _, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
          (s := univ) (t := univ) (f := r) (n := a - 1)
          (fun _ _ => mem_univ _) (by simp [N, Nat.mul_comm])
        exact ⟨c, by omega⟩
      obtain ⟨c, hc⟩ := large
      let C := univ.filter fun v => r v = c
      let e : Fin a ↪o Fin N := C.orderEmbOfCardLe hc
      refine ⟨e, e.strictMono, ?_⟩
      intro i j hij
      have hclique := label_fiber_clique Gᶜ r hr c
      have hne := e.injective.ne ((nestMatching a).ne_of_adj hij)
      have he := hclique (C.orderEmbOfCardLe_mem hc i) (C.orderEmbOfCardLe_mem hc j) hne
      simpa only [compl_compl] using he
  have lower : ∀ n ∈ S, N ≤ n := by
    intro n hn
    by_contra hnot
    have hnN : n ≤ (a - 1) * (b - 1) := by dsimp [N] at hnot; omega
    let G : SimpleGraph (Fin n) := SimpleGraph.fromRel fun x y =>
      x.val / (a - 1) = y.val / (a - 1)
    have adj : ∀ x y, G.Adj x y ↔ x ≠ y ∧ x.val / (a - 1) = y.val / (a - 1) := by
      intro x y
      simp [G, SimpleGraph.fromRel_adj, eq_comm]
    have noRed : ¬OrderedEmbeddable (nestMatching a) G := by
      rintro ⟨ψ, hψ, hedge⟩
      let z : Fin a := ⟨0, by omega⟩
      let t : Fin a := ⟨a - 1, by omega⟩
      have hz : (nestMatching a).Adj z t := by
        apply (SimpleGraph.fromRel_adj _ _ _).mpr
        refine ⟨?_, Or.inl ?_⟩
        · intro he
          have hv := congrArg Fin.val he
          dsimp [z, t] at hv
          omega
        · dsimp [z, t]
          omega
      have sameEnds := (adj _ _).mp (hedge z t hz) |>.2
      have same : ∀ i : Fin a, (ψ i).val / (a - 1) = (ψ z).val / (a - 1) := by
        intro i
        have hiz : z ≤ i := by exact Fin.mk_le_mk.mpr (Nat.zero_le _)
        have hit : i ≤ t := by
          apply Fin.mk_le_mk.mpr
          have hi := i.isLt
          change i.val ≤ a - 1
          omega
        have hlo := Nat.div_le_div_right (c := a - 1) (Fin.le_def.mp (hψ.monotone hiz))
        have hhi := Nat.div_le_div_right (c := a - 1) (Fin.le_def.mp (hψ.monotone hit))
        omega
      apply block_path_avoiding ha
      refine ⟨0, false, ψ, hψ, ?_⟩
      intro i j hij
      have hi : dihedralPerm 0 false i = i := by
        apply Fin.ext
        simp [dihedralPerm, Nat.mod_eq_of_lt i.isLt]
      have hj : dihedralPerm 0 false j = j := by
        apply Fin.ext
        simp [dihedralPerm, Nat.mod_eq_of_lt j.isLt]
      rw [hi, hj]
      apply (adj _ _).mpr
      exact ⟨hψ.injective.ne ((altPath a).ne_of_adj hij),
        (same i).trans (same j).symm⟩
    have noBlue : ¬OrderedEmbeddable (monoPath b) Gᶜ := by
      obtain ⟨d, hd⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
      subst b
      rintro ⟨ψ, hψ, hedge⟩
      let r : Fin (d + 1) → Fin d := fun i =>
        ⟨(ψ i).val / (a - 1), by
          apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
          have hv := (ψ i).isLt
          simpa [Nat.mul_comm] using lt_of_lt_of_le hv hnN⟩
      have hr : StrictMono r := by
        apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        have hblue := hedge i.castSucc i.succ ?_
        · exact block_blue_quotient_lt
            (hψ (show i.castSucc < i.succ from Fin.castSucc_lt_succ)) hblue
        · apply (SimpleGraph.fromRel_adj _ _ _).mpr
          exact ⟨(Fin.castSucc_lt_succ).ne, Or.inl rfl⟩
      have hh := Fintype.card_le_of_injective r hr.injective
      simp only [Fintype.card_fin] at hh
      omega
    exact (hn G).elim noRed noBlue
  change sInf S = N
  exact le_antisymm (Nat.sInf_le upper) (lower _ (Nat.sInf_mem ⟨N, upper⟩))

#print axioms result

end D5.S3.Combinatorics.DihedralRamsey.NestedOrdNestMon
