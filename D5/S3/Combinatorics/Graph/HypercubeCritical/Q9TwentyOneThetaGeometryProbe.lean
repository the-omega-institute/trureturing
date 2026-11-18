import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneThetaProbe

/-! Coordinate support of the two branch vertices in the compressed theta graphs. -/

set_option autoImplicit false
noncomputable section

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q flip)
open private diff diff_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_self diff_symm diff_empty_iff diff_triangle_card diff_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry

private lemma port_support {n : ℕ} (z : Q n) {a f : Fin n} (haf : a ≠ f) :
    diff (flip (flip z f) a) z = {a, f} := by
  classical
  rw [diff_flip, diff_flip, diff_self]
  simp [haf]

/-- A branch vertex at distance two from a translated spoke either has two
outside coordinates, including the translation direction, or four coordinates
containing both coordinates of that spoke. -/
private lemma branch_label {n : ℕ} (z P : Q n) (s : Fin 4 → Fin n)
    (havoid : ∀ k, ¬ (hypercube n).Adj P (flip z (s k)))
    (i : Fin 4) {f : Fin n} (hf : f ∉ Set.range s)
    (hd : hammingDist P (flip (flip z f) (s i)) = 2) :
    let D := diff P z
    (D.card = 2 ∧ f ∈ D ∧ ∀ k, s k ∉ D) ∨
      (D.card = 4 ∧ s i ∈ D ∧ f ∈ D) := by
  classical
  let D := diff P z
  let C : Finset (Fin n) := {s i, f}
  have hne : s i ≠ f := fun h => hf ⟨i, h⟩
  have hcard : C.card = 2 := by simp [C, hne]
  have hdc := diff_triangle_card P (flip (flip z f) (s i)) z
  change (diff P (flip (flip z f) (s i))).card = 2 at hd
  rw [hd, port_support z hne] at hdc
  change 2 + 2 * (D ∩ C).card = D.card + C.card at hdc
  rw [hcard] at hdc
  have hcap := card_le_card (show D ∩ C ⊆ C from inter_subset_right)
  rw [hcard] at hcap
  have hpos : D.card ≠ 0 := by
    intro hz
    have hpz : P = z := (diff_empty_iff P z).mp (card_eq_zero.mp hz)
    exact havoid i (hpz ▸ BalancedCriticalSpectrum.flip_adj z (s i))
  by_cases h2 : D.card = 2
  · have hnone (k : Fin 4) : s k ∉ D := by
      intro hm
      apply havoid k
      change (diff P (flip z (s k))).card = 1
      rw [diff_symm P, diff_flip, diff_symm z P]
      change (if s k ∈ D then D.erase (s k) else insert (s k) D).card = 1
      rw [ite_eq_left hm, card_erase_of_mem hm, h2]
    have hfc : f ∈ D := by
      obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (D ∩ C).card by omega)
      obtain ⟨hxD, hxC⟩ := mem_inter.mp hx
      have hxC' : x = s i ∨ x = f := by simpa [C] using hxC
      rcases hxC' with he | he
      · exact (hnone i (he ▸ hxD)).elim
      · exact he ▸ hxD
    exact Or.inl ⟨h2, hfc, hnone⟩
  · have h4 : D.card = 4 := by omega
    have hn : C.card ≤ (D ∩ C).card := by omega
    have he : D ∩ C = C := eq_of_subset_of_card_le inter_subset_right hn
    have hsub : C ⊆ D ∩ C := by rw [he]
    have hs (x : Fin n) (hx : x ∈ C) : x ∈ D := (mem_inter.mp (hsub hx)).1
    exact Or.inr ⟨h4, hs _ (by simp [C]), hs _ (by simp [C])⟩

/-- A vertex touching three ports at distance two is uniquely determined if
two of their outward coordinates are distinct and the other two ports cannot
use the first port's direction. -/
private lemma branch_label_three {n : ℕ} (z P : Q n) (s : Fin 4 → Fin n)
    (hs : Function.Injective s)
    (havoid : ∀ k, ¬ (hypercube n).Adj P (flip z (s k)))
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {f g h : Fin n} (hf : f ∉ Set.range s) (hg : g ∉ Set.range s) (hh : h ∉ Set.range s)
    (hfg : f ≠ g)
    (hi : hammingDist P (flip (flip z f) (s i)) = 2)
    (hj : hammingDist P (flip (flip z g) (s j)) = 2)
    (hk : hammingDist P (flip (flip z h) (s k)) = 2) :
    diff P z = {f, g} := by
  classical
  let D := diff P z
  rcases branch_label z P s havoid i hf hi with ⟨hc, hfD, _⟩ | ⟨hc, hiD, hfD⟩
  · have hgD : g ∈ D := by
      rcases branch_label z P s havoid j hg hj with h | h
      · exact h.2.1
      · have h4 : D.card = 4 := h.1
        have h2 : D.card = 2 := hc
        omega
    have hsub : ({f, g} : Finset (Fin n)) ⊆ D := by
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hfD, hgD⟩
    have h2 : D.card = 2 := hc
    exact (eq_of_subset_of_card_le hsub (by simp [h2, hfg])).symm
  · have hjD : s j ∈ D ∧ g ∈ D := by
      rcases branch_label z P s havoid j hg hj with h | h
      · have h2 : D.card = 2 := h.1
        have h4 : D.card = 4 := hc
        omega
      · exact h.2
    have hkD : s k ∈ D := by
      rcases branch_label z P s havoid k hh hk with h | h
      · have h2 : D.card = 2 := h.1
        have h4 : D.card = 4 := hc
        omega
      · exact h.2.1
    have hsub : ({s i, s j, s k, f, g} : Finset (Fin n)) ⊆ D := by
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hiD, hjD.1, hkD, hfD, hjD.2⟩
    have hsize := card_le_card hsub
    have hfive : ({s i, s j, s k, f, g} : Finset (Fin n)).card = 5 := by
      have neF (a : Fin 4) : s a ≠ f := fun e => hf ⟨a, e⟩
      have neG (a : Fin 4) : s a ≠ g := fun e => hg ⟨a, e⟩
      simp [hs.eq_iff, hij, hik, hjk, neF, neG, hfg]
    have h4 : D.card = 4 := hc
    rw [hfive, h4] at hsize
    omega

#print axioms branch_label_three
