/- GID: D5/S3/Combinatorics/RestrictedPairSumClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RestrictedPairSumClassification
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Restricted pair sums on at least three nonzero elements force an additive subgroup carrier. -/

import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Finite restricted pair sums and the additive translation stabilizer. -/

noncomputable section
open scoped Pointwise

namespace D5.S3.Combinatorics.RestrictedPairSumClassification
open scoped Classical

theorem restricted_pair_sum_classification
    {G : Type*} [AddCommGroup G] (A : Finset G)
    (h0 : 0 ∉ A) (hcard : 3 ≤ A.card)
    (hpair : ∀ ⦃a b : G⦄, a ∈ A → b ∈ A → a ≠ b → a + b ∈ insert 0 A) :
    ∃ H : AddSubgroup G, (H : Set G) = (↑(insert 0 A) : Set G) := by
  let S : Finset G := insert 0 A
  let P : AddSubgroup G := AddAction.stabilizer G (↑S : Set G)
  have hSfinite : (↑S : Set G).Finite := S.finite_toSet
  have hPsub : (P : Set G) ⊆ (↑S : Set G) := by
    intro g hg
    have hg0 := (AddAction.mem_stabilizer_set' hSfinite).1 hg
      (show (0 : G) ∈ (↑S : Set G) by simp [S])
    change g + 0 ∈ S at hg0
    simpa using hg0
  have period_of_mem (x : G) (hx : x ∈ S)
      (hxs : ∀ y, y ∈ S → x + y ∈ S) : x ∈ P := by
    apply (AddAction.mem_stabilizer_set' hSfinite).2
    intro y hy
    change x + y ∈ S
    change y ∈ S at hy
    exact hxs y hy
  by_cases hall : ∀ x ∈ A, x = -x
  · have hSperiod : ∀ x, x ∈ S → x ∈ P := by
      intro x hx
      apply period_of_mem x hx
      intro y hy
      rcases Finset.mem_insert.mp hx with rfl | hxA
      · simpa [S] using hy
      rcases Finset.mem_insert.mp hy with rfl | hyA
      · simpa [S] using (Finset.mem_insert.mpr (Or.inr hxA) : x ∈ insert 0 A)
      by_cases hxy : x = y
      · subst y
        have hxx : x + x = 0 := by
          calc
            x + x = x + -x := congrArg (fun z => x + z) (hall x hxA)
            _ = 0 := add_neg_cancel x
        simp [S, hxx]
      · exact hpair hxA hyA hxy
    refine ⟨P, ?_⟩
    apply Set.Subset.antisymm hPsub
    intro x hx
    exact hSperiod x hx
  push_neg at hall
  obtain ⟨a0, ha0, ha0_ne_neg⟩ := hall
  have hInv : ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ u + v = 0 := by
    by_cases h : ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ u + v = 0
    · exact h
    have hnoinv : ∀ ⦃u v : G⦄, u ∈ A → v ∈ A → u + v = 0 → u = v := by
      intro u v hu hv huv
      by_contra hne
      exact h ⟨u, hu, v, hv, hne, huv⟩
    have htranslate : ∀ (c : G), c ∈ A → ∀ ⦃t : G⦄, t ∈ A.erase c →
        ∃ d, d ∈ A.erase c ∧ c + d = t := by
      intro c hc t ht
      let B : Finset G := A.erase c
      have hmap : ∀ d, d ∈ B → c + d ∈ B := by
        intro d hd
        have hdA : d ∈ A := (Finset.mem_erase.mp hd).2
        have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
        have hcdS := hpair hc hdA (by
          intro h'
          exact hdc h'.symm)
        have hcd0 : c + d ≠ 0 := by
          intro hzero
          exact hdc (hnoinv (u := c) (v := d) hc hdA hzero).symm
        have hcd_ne_c : c + d ≠ c := by
          intro heq
          have hd0 : d = 0 := by
            apply add_left_cancel (a := c)
            simpa using heq
          exact h0 (by simpa [hd0] using hdA)
        apply Finset.mem_erase.mpr
        refine ⟨hcd_ne_c, ?_⟩
        exact Finset.mem_insert.mp hcdS |>.resolve_left hcd0
      have hsub : B.image (fun d => c + d) ⊆ B := by
        intro z hz
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
        exact hmap d hd
      have himage : B.image (fun d => c + d) = B := by
        apply Finset.eq_of_subset_of_card_le hsub
        have hinj : Set.InjOn (fun d => c + d) (↑B : Set G) := by
          intro x hx y hy hxy
          exact add_left_cancel hxy
        exact (Finset.card_image_iff.mpr hinj).ge
      have ht' : t ∈ B.image (fun d => c + d) := by
        rw [himage]
        exact ht
      obtain ⟨d, hd, hdt⟩ := Finset.mem_image.mp ht'
      exact ⟨d, hd, hdt⟩
    have hAerase_nonempty : (A.erase a0).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem ha0]
      omega
    obtain ⟨b, hb⟩ := hAerase_nonempty
    have hba : b ≠ a0 := (Finset.mem_erase.mp hb).1
    have hbA : b ∈ A := (Finset.mem_erase.mp hb).2
    have habS : a0 + b ∈ insert 0 A := hpair ha0 hbA hba.symm
    have hab0 : a0 + b ≠ 0 := by
      intro hz
      exact hba.symm (hnoinv ha0 hbA hz)
    have hab_ne_a : a0 + b ≠ a0 := by
      intro hz
      have hb0 : b = 0 := by
        apply add_left_cancel (a := a0)
        simpa using hz
      exact h0 (by simpa [hb0] using hbA)
    have hcA : a0 + b ∈ A := Finset.mem_insert.mp habS |>.resolve_left hab0
    have hbc : b ∈ A.erase (a0 + b) := by
      apply Finset.mem_erase.mpr
      refine ⟨?_, hbA⟩
      intro hz
      have ha0zero : a0 = 0 := by
        apply add_right_cancel (b := b)
        simpa using hz.symm
      exact h0 (by simpa [ha0zero] using ha0)
    obtain ⟨d, hd, hcd⟩ := htranslate (a0 + b) hcA hbc
    have hdA : d ∈ A := (Finset.mem_erase.mp hd).2
    have had : a0 + d = 0 := by
      calc
        a0 + d = (a0 + b) + d - b := by abel
        _ = b - b := by rw [hcd]
        _ = 0 := sub_self b
    have hda : d ≠ a0 := by
      intro hda
      have haa : a0 + a0 = 0 := by simpa [hda] using had
      exact ha0_ne_neg (eq_neg_of_add_eq_zero_left haa)
    exact ⟨a0, ha0, d, hdA, hda.symm, had⟩
  obtain ⟨a, ha, na, hna, hane, hane_sum⟩ := hInv
  have hna_eq : na = -a := by
    apply eq_neg_of_add_eq_zero_left
    simpa [add_comm] using hane_sum
  have hane_neg : a ≠ -a := by simpa [hna_eq] using hane
  have hna_mem : -a ∈ A := by simpa [hna_eq] using hna
  have hE : ((A.erase a).erase (-a)).Nonempty := by
    by_contra hE
    have hE0 : (A.erase a).erase (-a) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    have hAsub : A ⊆ {a, -a} := by
      intro x hx
      by_cases hxa : x = a
      · simp [hxa]
      by_cases hxn : x = -a
      · simp [hxn]
      have hxE : x ∈ (A.erase a).erase (-a) := by
        apply Finset.mem_erase.mpr
        refine ⟨hxn, ?_⟩
        apply Finset.mem_erase.mpr
        exact ⟨hxa, hx⟩
      rw [hE0] at hxE
      exact False.elim (by simpa using hxE)
    have hAc : A.card ≤ ({a, -a} : Finset G).card := Finset.card_le_card hAsub
    simp [hane_neg] at hAc
    omega
  have hEperiod : ∀ x, x ∈ (A.erase a).erase (-a) → x ∈ P := by
    intro x hx
    have hxn : x ≠ -a := (Finset.mem_erase.mp hx).1
    have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    have hxA : x ∈ A := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
    have hxp : x + a ∈ A := by
      have hs := hpair hxA ha hxa
      have hzero : x + a ≠ 0 := by
        intro hz
        exact hxn (eq_neg_of_add_eq_zero_left hz)
      exact Finset.mem_insert.mp hs |>.resolve_left hzero
    have hxm : x + -a ∈ A := by
      have hs := hpair hxA hna_mem hxn
      have hzero : x + -a ≠ 0 := by
        intro hz
        have : x = a := by
          simpa using (eq_neg_of_add_eq_zero_left hz)
        exact hxa this
      exact Finset.mem_insert.mp hs |>.resolve_left hzero
    have hxd : x + a ≠ x + -a := by
      intro heq
      exact hane_neg (add_left_cancel heq)
    apply period_of_mem x (Finset.mem_insert.mpr (Or.inr hxA))
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hyA
    · simpa [S] using (show x ∈ S from Finset.mem_insert.mpr (Or.inr hxA))
    by_cases hxy : x = y
    · subst y
      have hxxS : x + x ∈ insert 0 A := by
        simpa [add_assoc, add_left_comm, add_comm] using hpair hxp hxm hxd
      simpa [S] using hxxS
    · exact hpair hxA hyA hxy
  obtain ⟨b, hbE⟩ := hE
  have hbA : b ∈ A := (Finset.mem_erase.mp (Finset.mem_erase.mp hbE).2).2
  have hbP : b ∈ P := hEperiod b hbE
  have hnbP : -b ∈ P := P.neg_mem hbP
  have haP : a ∈ P := by
    by_contra haP
    have habS' : -b + a ∈ S := by
      have hmem := (AddAction.mem_stabilizer_set' hSfinite).1 hnbP
        (show a ∈ (↑S : Set G) by exact Finset.mem_coe.mpr (Finset.mem_insert.mpr (Or.inr ha)))
      exact hmem
    have hzero : a - b ≠ 0 := by
      intro hz
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hbE).2).1 (sub_eq_zero.mp hz).symm
    have hne_a : a - b ≠ a := by
      intro hz
      have hb0 : b = 0 := by
        calc
          b = a - (a - b) := by abel
          _ = a - a := by rw [hz]
          _ = 0 := sub_self a
      exact h0 (by simpa [hb0] using (Finset.mem_erase.mp (Finset.mem_erase.mp hbE).2).2)
    have habA : a - b ∈ A := by
      have hs : a - b ∈ S := by simpa [sub_eq_add_neg, add_comm] using habS'
      exact Finset.mem_insert.mp hs |>.resolve_left hzero
    by_cases hneg : a - b = -a
    · have htwo : a + a = b := by
        calc
          a + a = a + (a - b) + b := by abel
          _ = a + (-a) + b := by rw [hneg]
          _ = b := by abel
      have hsum : ∀ y, y ∈ S → a + y ∈ S := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hyA
        · simpa [S] using (Finset.mem_insert.mpr (Or.inr ha) : a ∈ insert 0 A)
        by_cases hay : a = y
        · subst y
          simpa [htwo, S] using (show b ∈ S from Finset.mem_insert.mpr (Or.inr hbA))
        · exact hpair ha hyA hay
      exact haP (period_of_mem a (Finset.mem_insert.mpr (Or.inr ha)) hsum)
    · have habE : a - b ∈ (A.erase a).erase (-a) := by
        apply Finset.mem_erase.mpr
        refine ⟨hneg, ?_⟩
        apply Finset.mem_erase.mpr
        exact ⟨hne_a, habA⟩
      have habP := hEperiod (a - b) habE
      apply haP
      have hsumP := P.add_mem habP hbP
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsumP
  have hnaP : -a ∈ P := P.neg_mem haP
  have hAperiod : ∀ x, x ∈ A → x ∈ P := by
    intro x hx
    by_cases hxa : x = a
    · simpa [hxa] using haP
    by_cases hxn : x = -a
    · simpa [hxn] using hnaP
    exact hEperiod x (Finset.mem_erase.mpr ⟨hxn, Finset.mem_erase.mpr ⟨hxa, hx⟩⟩)
  refine ⟨P, ?_⟩
  apply Set.Subset.antisymm hPsub
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hxA
  · exact P.zero_mem
  · exact hAperiod x hxA

end D5.S3.Combinatorics.RestrictedPairSumClassification
