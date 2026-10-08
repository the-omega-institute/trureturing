/- GID: D5/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankCover
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankCover
   mirror-E: none(waiver:complement-cover-bound)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Intersecting edge families in triangle-free graphs have a common endpoint. -/

import D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankTree
import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PhylogeneticRank

open SimpleGraph PhylogeneticRankDefs

/-- Two intersecting edges force a star, since the alternative third edge makes a triangle. -/
theorem intersecting_edges_have_center {V : Type*} (H : SimpleGraph V)
    (hH : H.CliqueFree 3) (R : V → V → Prop)
    (hedge : ∀ a b, R a b → H.Adj a b)
    (hmeet : ∀ a b c d, R a b → R c d → a = c ∨ a = d ∨ b = c ∨ b = d)
    (hne : ∃ a b, R a b) : ∃ x, ∀ a b, R a b → a = x ∨ b = x := by
  classical
  obtain ⟨a, b, hab⟩ := hne
  by_cases ha : ∀ c d, R c d → c = a ∨ d = a
  · exact ⟨a, ha⟩
  push Not at ha
  obtain ⟨c, d, hcd, hca, hda⟩ := ha
  have hbc : b = c ∨ b = d := by
    rcases hmeet a b c d hab hcd with h | h | h | h
    · exact (hca h.symm).elim
    · exact (hda h.symm).elim
    · exact Or.inl h
    · exact Or.inr h
  have htri : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False := by
    intro x y z hxy hyz hzx
    apply hH {x, y, z}
    refine ⟨?_, ?_⟩
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
      all_goals first
        | exact (hij rfl).elim
        | assumption
        | exact hxy.symm
        | exact hyz.symm
        | exact hzx.symm
    · have hxy' := hxy.ne
      have hyz' := hyz.ne
      have hzx' := hzx.ne
      simp [hxy', hyz', hzx'.symm]
  refine ⟨b, ?_⟩
  intro u v huv
  by_contra h
  push Not at h
  have hua : u = a ∨ v = a := by
    rcases hmeet a b u v hab huv with h' | h' | h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm
    · exact (h.1 h'.symm).elim
    · exact (h.2 h'.symm).elim
  have hu_other : u = c ∨ u = d ∨ v = c ∨ v = d :=
    hmeet u v c d huv hcd
  rcases hbc with hbc | hbd
  · subst c
    rcases hua with rfl | rfl
    · rcases hu_other with h' | h' | h' | h'
      · exact (h.1 h').elim
      · exact (hda h'.symm).elim
      · exact (h.2 h').elim
      · subst v
        exact htri _ b d (hedge _ _ hab) (hedge _ _ hcd) (hedge _ _ huv).symm
    · rcases hu_other with h' | h' | h' | h'
      · exact (h.1 h').elim
      · subst u
        exact htri _ b d (hedge _ _ hab) (hedge _ _ hcd) (hedge _ _ huv)
      · exact (h.2 h').elim
      · exact (hda h'.symm).elim
  · subst d
    rcases hua with rfl | rfl
    · rcases hu_other with h' | h' | h' | h'
      · exact (hca h'.symm).elim
      · exact (h.1 h').elim
      · subst v
        exact htri _ b c (hedge _ _ hab) (hedge _ _ hcd).symm (hedge _ _ huv).symm
      · exact (h.2 h').elim
    · rcases hu_other with h' | h' | h' | h'
      · subst u
        exact htri _ b c (hedge _ _ hab) (hedge _ _ hcd).symm (hedge _ _ huv)
      · exact (h.1 h').elim
      · exact (hca h'.symm).elim
      · exact (h.2 h').elim

/-- Four points forces each coordinate's tight complement edges into one star. -/
theorem embedding_rank_lower_bound {n k : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n))
    (htri : H.CliqueFree 3)
    (hfour : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      H.Adj a b → H.Adj b c → H.Adj c d → H.Adj d a → False)
    (hconn : Hᶜ.Connected) (hdiam : ∀ a b, Hᶜ.dist a b ≤ 2)
    (hemb : HasTreeEmbedding Hᶜ k) : n - H.indepNum ≤ k := by
  classical
  obtain ⟨T, f, he⟩ := hemb
  have hk : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst k
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
    have hpos := hconn.pos_dist_of_ne hab
    have he' := he a b
    simp only [iSup_of_empty', Real.sSup_empty] at he'
    have hzero : Hᶜ.dist a b = 0 := by exact_mod_cast he'
    omega
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let t := fun i a b => (T i).dist (f i a) (f i b)
  have hdom : ∀ i a b, t i a b ≤ (Hᶜ.dist a b : ℝ) := by
    intro i a b
    change (T i).dist (f i a) (f i b) ≤ (Hᶜ.dist a b : ℝ)
    rw [he]
    exact le_ciSup (Set.finite_range (fun j : Fin k => (T j).dist (f j a) (f j b))).bddAbove i
  have htwo : ∀ a b, H.Adj a b → Hᶜ.dist a b = 2 := by
    intro a b hab
    have hnot : ¬Hᶜ.Adj a b := by simp [compl_adj, hab]
    have hgt := hconn.one_lt_dist_of_ne_of_not_adj hab.ne hnot
    have hle := hdiam a b
    omega
  have hcovered : ∀ a b, H.Adj a b → ∃ i, t i a b = 2 := by
    intro a b hab
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => t i a b)
    refine ⟨i, ?_⟩
    rw [← he, htwo a b hab, Nat.cast_ofNat] at hi
    exact hi
  let R := fun i a b => H.Adj a b ∧ t i a b = 2
  have hmeet : ∀ i a b c d, R i a b → R i c d →
      a = c ∨ a = d ∨ b = c ∨ b = d := by
    intro i a b c d hab hcd
    by_contra hdis
    push Not at hdis
    obtain ⟨hac, had, hbc, hbd⟩ := hdis
    have hab' := hab.1.ne
    have hcd' := hcd.1.ne
    have hf := tree_four_point (T i) (f i a) (f i b) (f i c) (f i d)
    change t i a b + t i c d ≤ max (t i a c + t i b d) (t i a d + t i b c) at hf
    rw [hab.2, hcd.2] at hf
    have hle : ∀ x y, t i x y ≤ 2 := by
      intro x y
      exact (hdom i x y).trans (by exact_mod_cast hdiam x y)
    have htight : ∀ x y, x ≠ y → t i x y = 2 → H.Adj x y := by
      intro x y hxy hval
      by_contra hnxy
      have hgxy : Hᶜ.Adj x y := (compl_adj H x y).mpr ⟨hxy, hnxy⟩
      have hdistxy := (dist_eq_one_iff_adj).mpr hgxy
      have hti := hdom i x y
      rw [hval, hdistxy, Nat.cast_one] at hti
      norm_num at hti
    rcases le_max_iff.mp hf with h | h
    · have hac' : t i a c = 2 := by linarith [hle a c, hle b d]
      have hbd' : t i b d = 2 := by linarith [hle a c, hle b d]
      exact hfour a b d c hab' had hac hbd hbc hcd'.symm hab.1
        (htight b d hbd hbd') hcd.1.symm (htight a c hac hac').symm
    · have had' : t i a d = 2 := by linarith [hle a d, hle b c]
      have hbc' : t i b c = 2 := by linarith [hle a d, hle b c]
      exact hfour a b c d hab' hac had hbc hbd hcd' hab.1
        (htight b c hbc hbc') hcd.1 (htight a d had had').symm
  have hcentres : ∀ i : Fin k, ∃ x : Fin n, ∀ a b, R i a b → a = x ∨ b = x := by
    intro i
    by_cases hi : ∃ a b, R i a b
    · exact intersecting_edges_have_center H htri (R i) (fun _ _ h => h.1) (hmeet i) hi
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro a b hab
      exact (hi ⟨a, b, hab⟩).elim
  choose centre hc using hcentres
  let C : Finset (Fin n) := Finset.univ.image centre
  have hC : C.card ≤ k := by
    exact (Finset.card_image_le).trans_eq (Fintype.card_fin k)
  have hI : H.IsIndepSet (Cᶜ : Finset (Fin n)) := by
    rw [isIndepSet_iff]
    intro a ha b hb _ hab
    obtain ⟨i, hi⟩ := hcovered a b hab
    rcases hc i a b ⟨hab, hi⟩ with h | h
    · have hmem : a ∈ C := by rw [h]; exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
      exact (Finset.mem_compl.mp ha) hmem
    · have hmem : b ∈ C := by rw [h]; exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
      exact (Finset.mem_compl.mp hb) hmem
  have hind := hI.card_le_indepNum
  rw [Finset.card_compl, Fintype.card_fin] at hind
  have hcN : C.card ≤ n := by simpa using Finset.card_le_univ C
  omega

#print axioms intersecting_edges_have_center
#print axioms embedding_rank_lower_bound

end D5.S3.Combinatorics.PhylogeneticRank
