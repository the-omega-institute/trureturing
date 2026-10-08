/- GID: D5/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankDeletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankDeletion
   mirror-E: none(waiver:short-cycle-deletion)
   anchors: []
   utility: none
   digest: Isolating one vertex per short cycle bounds the growth of the independence number. -/

import D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PhylogeneticRank

open SimpleGraph PhylogeneticRankDefs
open Classical in
/-- The cycle representatives form a small deletion set; outside it all edges are retained. -/
theorem exists_short_cycle_free_deletion {n : ℕ} (X : SimpleGraph (Fin n)) :
    ∃ H : SimpleGraph (Fin n), H ≤ X ∧ H.CliqueFree 3 ∧
      (∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        H.Adj a b → H.Adj b c → H.Adj c d → H.Adj d a → False) ∧
      H.indepNum ≤ X.indepNum +
        (Finset.univ.filter (fun f : {f : Fin 3 → Fin n // Function.Injective f} =>
          X.Adj (f.val 0) (f.val 1) ∧ X.Adj (f.val 1) (f.val 2) ∧
            X.Adj (f.val 2) (f.val 0))).card +
        (Finset.univ.filter (fun f : {f : Fin 4 → Fin n // Function.Injective f} =>
          X.Adj (f.val 0) (f.val 1) ∧ X.Adj (f.val 1) (f.val 2) ∧
            X.Adj (f.val 2) (f.val 3) ∧ X.Adj (f.val 3) (f.val 0))).card := by
  classical
  let A := Finset.univ.filter (fun f : {f : Fin 3 → Fin n // Function.Injective f} =>
    X.Adj (f.val 0) (f.val 1) ∧ X.Adj (f.val 1) (f.val 2) ∧
      X.Adj (f.val 2) (f.val 0))
  let B := Finset.univ.filter (fun f : {f : Fin 4 → Fin n // Function.Injective f} =>
    X.Adj (f.val 0) (f.val 1) ∧ X.Adj (f.val 1) (f.val 2) ∧
      X.Adj (f.val 2) (f.val 3) ∧ X.Adj (f.val 3) (f.val 0))
  let D : Finset (Fin n) := A.image (fun f => f.val 0) ∪ B.image (fun f => f.val 0)
  have hD : D.card ≤ A.card + B.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  let H : SimpleGraph (Fin n) :=
    { Adj := fun a b => X.Adj a b ∧ a ∉ D ∧ b ∉ D
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun _ h => h.1.ne rfl⟩ }
  have htriangle : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False := by
    intro a b c hab hbc hca
    have hab' := hab.1.ne
    have hbc' := hbc.1.ne
    have hca' := hca.1.ne
    let f : {f : Fin 3 → Fin n // Function.Injective f} :=
      ⟨![a, b, c], by
        intro i j he
        fin_cases i <;> fin_cases j <;> simp_all⟩
    have hf : f ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hab.1, hbc.1, hca.1⟩
    have ha : a ∈ D := Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨f, hf, rfl⟩)
    exact hab.2.1 ha
  have htri : H.CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.mp hs.2
    subst s
    have hab' := hs.1 (by simp) (by simp) hab
    have hbc' := hs.1 (by simp) (by simp) hbc
    have hca' := hs.1 (by simp) (by simp) hac.symm
    exact htriangle a b c hab' hbc' hca'
  have hfour : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      H.Adj a b → H.Adj b c → H.Adj c d → H.Adj d a → False := by
    intro a b c d hab hac had hbc hbd hcd eab ebc ecd eda
    let f : {f : Fin 4 → Fin n // Function.Injective f} :=
      ⟨![a, b, c, d], by
        intro i j he
        fin_cases i <;> fin_cases j <;> simp_all⟩
    have hf : f ∈ B := by
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨eab.1, ebc.1, ecd.1, eda.1⟩
    have ha : a ∈ D := Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨f, hf, rfl⟩)
    exact eab.2.1 ha
  refine ⟨H, (fun _ _ h => h.1), htri, hfour, ?_⟩
  obtain ⟨I, hI, hcard⟩ := H.exists_isNIndepSet_indepNum
  let J := I \ D
  have hJ : X.IsIndepSet J := by
    rw [isIndepSet_iff]
    intro a ha b hb hab he
    have ha' : a ∈ I ∧ a ∉ D := Finset.mem_sdiff.mp ha
    have hb' : b ∈ I ∧ b ∉ D := Finset.mem_sdiff.mp hb
    exact hI ha'.1 hb'.1 hab ⟨he, ha'.2, hb'.2⟩
  have hj := hJ.card_le_indepNum
  have hi : I.card ≤ J.card + D.card := by
    have hsub : I ⊆ J ∪ D := by
      intro a ha
      by_cases hd : a ∈ D
      · exact Finset.mem_union_right _ hd
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, hd⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  change H.indepNum ≤ X.indepNum + A.card + B.card
  omega

#print axioms exists_short_cycle_free_deletion

end D5.S3.Combinatorics.PhylogeneticRank
