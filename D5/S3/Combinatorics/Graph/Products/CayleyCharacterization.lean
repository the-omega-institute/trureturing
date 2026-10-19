/- GID: D5/S3/Combinatorics/Graph/Products/CayleyCharacterization
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Products/CayleyCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Prod]
   utility: none
   digest: Finite connected abelian Cayley Cartesian squares are well-covered precisely in the complete case. -/

import D5.S3.Combinatorics.Graph.Products.NearEmptyLayer
import D5.S3.Combinatorics.Graph.WellCoveredPowerCliqueProduct

open SimpleGraph Finset
open WellCoveredPowerCliqueProduct

namespace CayleySquare

variable {V : Type}

private theorem maximal_iff (G : SimpleGraph V) (I : Finset V) :
    IsMaximalIndep G I ↔ Maximal G.IsIndepSet (I : Set V) := by
  classical
  constructor
  · intro h
    refine ⟨(by intro x hx y hy hxy; exact h.1 x hx y hy hxy), ?_⟩
    intro U hU hIU x hx
    by_contra hxI
    obtain ⟨y, hy, hxy⟩ := h.2 x hxI
    exact hU hx (hIU hy) hxy.ne hxy
  · intro h
    refine ⟨(by intro x hx y hy hxy; exact h.1 hx hy hxy), ?_⟩
    intro x hx
    by_contra! hn
    have hi : G.IsIndepSet (insert x (I : Set V)) := by
      exact (Set.pairwise_insert (r := fun a b => ¬ G.Adj a b)).mpr
        ⟨h.1, fun y hy _ => ⟨hn y hy, fun ha => hn y hy ha.symm⟩⟩
    exact hx (h.2 hi (Set.subset_insert x _) (Set.mem_insert x _))

private theorem complete_square_card [Fintype V] [Nonempty V] (I : Finset (V × V))
    (hI : IsMaximalIndep ((⊤ : SimpleGraph V) □ (⊤ : SimpleGraph V)) I) : I.card = Fintype.card V := by
  classical
  have hf : Set.InjOn Prod.fst (I : Set (V × V)) := by
    intro p hp q hq he
    by_contra hn
    have hs : p.2 ≠ q.2 := fun h => hn (Prod.ext he h)
    exact hI.1 p hp q hq hn (Or.inr ⟨hs, he⟩)
  have hg : Set.InjOn Prod.snd (I : Set (V × V)) := by
    intro p hp q hq he
    by_contra hn
    have hs : p.1 ≠ q.1 := fun h => hn (Prod.ext h he)
    exact hI.1 p hp q hq hn (Or.inl ⟨hs, he⟩)
  have hle : I.card ≤ Fintype.card V := by
    rw [← card_image_of_injOn hf]
    exact card_le_univ _
  apply Nat.le_antisymm hle
  by_contra! hn
  have hfst : (I.image Prod.fst).card < (univ : Finset V).card := by
    simpa [card_image_of_injOn hf] using hn
  have hsnd : (I.image Prod.snd).card < (univ : Finset V).card := by
    simpa [card_image_of_injOn hg] using hn
  obtain ⟨x, _, hx⟩ := exists_mem_notMem_of_card_lt_card hfst
  obtain ⟨y, _, hy⟩ := exists_mem_notMem_of_card_lt_card hsnd
  have hxy : (x,y) ∉ I := fun h => hx (mem_image.mpr ⟨(x,y),h,rfl⟩)
  obtain ⟨p,hp,ha⟩ := hI.2 (x,y) hxy
  rcases ha with ⟨_,he⟩ | ⟨_,he⟩
  · exact hy (mem_image.mpr ⟨p,hp,he.symm⟩)
  · exact hx (mem_image.mpr ⟨p,hp,he.symm⟩)

private theorem wellCovered_complete [Nonempty V] : WellCovered (⊤ : SimpleGraph V) := by
  classical
  have hcard (I : Finset V) (hI : IsMaximalIndep (⊤ : SimpleGraph V) I) : I.card = 1 := by
    have hi : I.Nonempty := by
      obtain ⟨x⟩ := ‹Nonempty V›
      by_cases hx : x ∈ I
      · exact ⟨x,hx⟩
      · obtain ⟨y,hy,_⟩ := hI.2 x hx
        exact ⟨y,hy⟩
    have hle : I.card ≤ 1 := card_le_one.mpr (by
      intro x hx y hy
      by_contra hn
      exact hI.1 x hx y hy hn hn)
    have := card_pos.mpr hi
    omega
  intro I J hI hJ
  rw [hcard I hI, hcard J hJ]

private theorem power_one (G : SimpleGraph V) (hc : G.Connected) : power G 1 = G := by
  ext x y
  change (x ≠ y ∧ G.dist x y ≤ 1) ↔ G.Adj x y
  constructor
  · rintro ⟨hne, hle⟩
    apply G.dist_eq_one_iff_adj.mp
    have : G.dist x y ≠ 0 := fun h => hne (hc.dist_eq_zero_iff.mp h)
    omega
  · intro ha
    exact ⟨ha.ne, by rw [G.dist_eq_one_iff_adj.mpr ha]⟩

private theorem complete_square_wcp [Finite V] [Nonempty V] : WCP ((⊤ : SimpleGraph V) □ (⊤ : SimpleGraph V)) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hc : ((⊤ : SimpleGraph V) □ (⊤ : SimpleGraph V)).Connected := connected_top.boxProd connected_top
  refine ⟨hc, ?_⟩
  intro d hd
  by_cases hdone : d = 1
  · rw [hdone, power_one _ hc]
    intro I J hI hJ
    rw [complete_square_card I hI, complete_square_card J hJ]
  · have htwo : 2 ≤ d := by omega
    have hdist (x y : V × V) : ((⊤ : SimpleGraph V) □ (⊤ : SimpleGraph V)).dist x y ≤ 2 := by
      rw [SimpleGraph.dist, SimpleGraph.edist_boxProd, SimpleGraph.edist_top, SimpleGraph.edist_top]
      split_ifs <;> norm_num
    have heq : power ((⊤ : SimpleGraph V) □ (⊤ : SimpleGraph V)) d = ⊤ := by
      ext x y
      change (x ≠ y ∧ ((⊤ : SimpleGraph V) □ (⊤ : SimpleGraph V)).dist x y ≤ d) ↔ x ≠ y
      exact and_iff_left ((hdist x y).trans htwo)
    rw [heq]
    exact wellCovered_complete

variable {A : Type} [Finite A] [AddCommGroup A]

/-- The complete/well-covered/all-positive-powers equivalence includes every finite abelian group. -/
theorem cayley_square_characterization (S : Set A) (hzero : (0 : A) ∉ S)
    (hneg : ∀ a ∈ S, -a ∈ S) (hc : (addCayley S).Connected) :
    ((addCayley S = ⊤) ↔ WellCovered ((addCayley S) □ (addCayley S))) ∧
    (WellCovered ((addCayley S) □ (addCayley S)) ↔
      ∀ d : ℕ, 1 ≤ d → WellCovered (power ((addCayley S) □ (addCayley S)) d)) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  let G := addCayley S
  have hcomplete : G = ⊤ → WCP (G □ G) := by
    intro h
    rw [h]
    exact complete_square_wcp
  have hfirst : (∀ d : ℕ, 1 ≤ d → WellCovered (power (G □ G) d)) → WellCovered (G □ G) := by
    intro h
    have hp := h 1 le_rfl
    rw [power_one (G □ G) (hc.boxProd hc)] at hp
    exact hp
  have hconverse : WellCovered (G □ G) → G = ⊤ := by
    intro hWC
    by_contra hne
    have hnonadj : ∃ x y : A, x ≠ y ∧ ¬ G.Adj x y := by
      by_contra! h
      apply hne
      ext x y
      exact ⟨fun ha => ha.ne, fun hxy => h x y hxy⟩
    obtain ⟨x,y,hxy,hnot⟩ := hnonadj
    have hind : G.IsIndepSet ({x,y} : Finset A) := by
      intro a ha b hb hab
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hnot
      · exact fun h => hnot h.symm
      · exact (hab rfl).elim
    have halpha : 2 ≤ G.indepNum := by
      have h := hind.card_le_indepNum
      simpa [hxy] using h
    obtain ⟨I,hI,hbound⟩ := exists_maximalIndepSet_near_empty_layer G hc
    obtain ⟨J,hJ⟩ := (G □ G).maximumIndepSet_exists
    have heq := hWC I J ((maximal_iff _ _).mpr hI)
      ((maximal_iff _ _).mpr (hJ.isMaximalIndepSet J))
    have hJcard := (G □ G).maximumIndepSet_card_eq_indepNum J hJ
    have halphaeq := indepNum_addCayley_square S hzero hneg
    have hn : 0 < Fintype.card A := Fintype.card_pos
    have hprod : Fintype.card A * G.indepNum =
        (Fintype.card A - 1) * G.indepNum + G.indepNum := by
      have hcard : Fintype.card A = Fintype.card A - 1 + 1 := by omega
      conv_lhs => rw [hcard]
      rw [Nat.add_mul, Nat.one_mul]
    change (G □ G).indepNum = Fintype.card A * G.indepNum at halphaeq
    rw [hJcard, halphaeq, hprod] at heq
    omega
  constructor
  · exact ⟨fun h => hfirst (hcomplete h).2, hconverse⟩
  · exact ⟨fun h => (hcomplete (hconverse h)).2, hfirst⟩

end CayleySquare
