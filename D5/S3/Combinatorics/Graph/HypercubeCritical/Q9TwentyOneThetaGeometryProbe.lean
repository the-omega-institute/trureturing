import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneThetaProbe

/-! Coordinate support of the two branch vertices in the compressed theta graphs. -/

set_option autoImplicit false
noncomputable section

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q flip IsBalanced)
open private SideHigh compressed compressed_triangle_free from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private compressed_distance low_not_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private matched_edge_over_diagonal from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneCompressionProbe
open private star_ports_outside star_matched_diagonal_midpoint four_high_side_is_star from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneSquareGeometryProbe
open private theta_from_matched_diagonal from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneThetaProbe
attribute [local instance] Classical.propDecidable
open private diff diff_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_self diff_symm diff_empty_iff diff_triangle diff_triangle_card diff_injective
  two_step_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry

open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

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

/-- In the one-diagonal theta, the degree-three vertices share both ends
outside the diagonal. Their cube coordinates then coincide. -/
private lemma single_diagonal_branch_vertices_equal
    {n : ℕ} (z P Q' : Q n) (s : Fin 4 → Fin n) (hs : Function.Injective s)
    (hP : ∀ k, ¬ (hypercube n).Adj P (flip z (s k)))
    (hQ : ∀ k, ¬ (hypercube n).Adj Q' (flip z (s k)))
    {f g h : Fin n} (hf : f ∉ Set.range s) (hg : g ∉ Set.range s) (hh : h ∉ Set.range s)
    (hfg : f ≠ g)
    (hP0 : hammingDist P (flip (flip z f) (s 0)) = 2)
    (hQ2 : hammingDist Q' (flip (flip z f) (s 2)) = 2)
    (hP1 : hammingDist P (flip (flip z g) (s 1)) = 2)
    (hP3 : hammingDist P (flip (flip z h) (s 3)) = 2)
    (hQ1 : hammingDist Q' (flip (flip z g) (s 1)) = 2)
    (hQ3 : hammingDist Q' (flip (flip z h) (s 3)) = 2) : P = Q' := by
  have hp := branch_label_three z P s hs hP (by decide : (0 : Fin 4) ≠ 1)
    (by decide : (0 : Fin 4) ≠ 3) (by decide : (1 : Fin 4) ≠ 3)
    hf hg hh hfg hP0 hP1 hP3
  have hq := branch_label_three z Q' s hs hQ (by decide : (2 : Fin 4) ≠ 1)
    (by decide : (2 : Fin 4) ≠ 3) (by decide : (1 : Fin 4) ≠ 3)
    hf hg hh hfg hQ2 hQ1 hQ3
  exact diff_injective z (hp.trans hq.symm)

/-- Two ports in distinct outside directions determine the branch label up to
its size. A small label contains just the outside pair, and a large label
also contains the two spokes. -/
private lemma branch_label_two {n : ℕ} (z P : Q n) (s : Fin 4 → Fin n)
    (hs : Function.Injective s) (havoid : ∀ k, ¬ (hypercube n).Adj P (flip z (s k)))
    {i j : Fin 4} (hij : i ≠ j) {f g : Fin n}
    (hf : f ∉ Set.range s) (hg : g ∉ Set.range s) (hfg : f ≠ g)
    (hi : hammingDist P (flip (flip z f) (s i)) = 2)
    (hj : hammingDist P (flip (flip z g) (s j)) = 2) :
    diff P z = {f, g} ∨ diff P z = {s i, s j, f, g} := by
  classical
  let D := diff P z
  have hneF (k : Fin 4) : s k ≠ f := fun h => hf ⟨k, h⟩
  have hneG (k : Fin 4) : s k ≠ g := fun h => hg ⟨k, h⟩
  rcases branch_label z P s havoid i hf hi with ⟨hi2, hfi, _⟩ | ⟨hi4, hsi, hfi⟩
  · have h2 : D.card = 2 := hi2
    have hgD : g ∈ D := by
      rcases branch_label z P s havoid j hg hj with hl | hl
      · exact hl.2.1
      · have h4 : D.card = 4 := hl.1
        omega
    have hsub : ({f, g} : Finset (Fin n)) ⊆ D := by
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hfi, hgD⟩
    exact Or.inl (eq_of_subset_of_card_le hsub (by simp [h2, hfg])).symm
  · have h4 : D.card = 4 := hi4
    have hjD : s j ∈ D ∧ g ∈ D := by
      rcases branch_label z P s havoid j hg hj with hl | hl
      · have h2 : D.card = 2 := hl.1
        omega
      · exact hl.2
    have hsub : ({s i, s j, f, g} : Finset (Fin n)) ⊆ D := by
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hsi, hjD.1, hfi, hjD.2⟩
    exact Or.inr (eq_of_subset_of_card_le hsub
      (by simp [h4, hs.ne hij, hneF, hneG, hfg])).symm

#print axioms single_diagonal_branch_vertices_equal
#print axioms branch_label_two

/-- Between a small and a large branch label, a common neighbor is adjacent
to one of the two ports represented by the large label. -/
private lemma small_large_middle_touches_port {n : ℕ} {z small large m u v : Q n}
    {a b f g : Fin n} (hab : a ≠ b) (haf : a ≠ f) (hag : a ≠ g)
    (hbf : b ≠ f) (hbg : b ≠ g) (hfg : f ≠ g)
    (hsmall : diff small z = {f, g}) (hlarge : diff large z = {a, b, f, g})
    (hu : diff u z = {a, f}) (hv : diff v z = {b, g})
    (hsm : (hypercube n).Adj small m) (hlm : (hypercube n).Adj large m) :
    (hypercube n).Adj m u ∨ (hypercube n).Adj m v := by
  classical
  have hD : diff small large = {a, b} := by
    rw [diff_triangle small large z, hsmall, hlarge]
    ext k
    simp only [mem_union, mem_sdiff, mem_insert, mem_singleton]
    grind
  obtain ⟨t, ht⟩ := adjacent_exists_flip hsm
  have hmem : t ∈ diff small large := by
    by_contra! hn
    have h := hlm.symm
    change (diff m large).card = 1 at h
    rw [ht, diff_flip, ite_eq_right hn, card_insert_of_notMem hn, hD] at h
    simp [hab] at h
  rw [hD, mem_insert, mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · left
    have hM : diff m z = {t, f, g} := by
      rw [ht, diff_flip, hsmall, ite_eq_right (by simp [haf, hag])]
    change (diff m u).card = 1
    have hd : diff m u = {g} := by
      rw [diff_triangle m u z, hM, hu]
      ext k
      simp only [mem_union, mem_sdiff, mem_insert, mem_singleton]
      grind
    rw [hd, card_singleton]
  · right
    have hM : diff m z = {t, f, g} := by
      rw [ht, diff_flip, hsmall, ite_eq_right (by simp [hbf, hbg])]
    change (diff m v).card = 1
    have hd : diff m v = {f} := by
      rw [diff_triangle m v z, hM, hv]
      ext k
      simp only [mem_union, mem_sdiff, mem_insert, mem_singleton]
      grind
    rw [hd, card_singleton]

/-- The two labeled branch vertices in the two-diagonal theta cannot have a
degree-two common neighbor. It would also touch one of the four ports. -/
private lemma two_diagonal_middle_touches_port
    {n : ℕ} (z P Q' m : Q n) (s : Fin 4 → Fin n) (hs : Function.Injective s)
    (hP : ∀ k, ¬ (hypercube n).Adj P (flip z (s k)))
    (hQ : ∀ k, ¬ (hypercube n).Adj Q' (flip z (s k)))
    (hpq : P ≠ Q') {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    {f g : Fin n} (hf : f ∉ Set.range s) (hg : g ∉ Set.range s) (hfg : f ≠ g)
    (hi : hammingDist P (flip (flip z f) (s i)) = 2)
    (hj : hammingDist P (flip (flip z g) (s j)) = 2)
    (hk : hammingDist Q' (flip (flip z f) (s k)) = 2)
    (hl : hammingDist Q' (flip (flip z g) (s l)) = 2)
    (hmP : (hypercube n).Adj P m) (hmQ : (hypercube n).Adj Q' m) :
    (hypercube n).Adj m (flip (flip z f) (s i)) ∨
      (hypercube n).Adj m (flip (flip z g) (s j)) ∨
      (hypercube n).Adj m (flip (flip z f) (s k)) ∨
      (hypercube n).Adj m (flip (flip z g) (s l)) := by
  classical
  have neF (r : Fin 4) : s r ≠ f := fun h => hf ⟨r, h⟩
  have neG (r : Fin 4) : s r ≠ g := fun h => hg ⟨r, h⟩
  rcases branch_label_two z P s hs hP hij hf hg hfg hi hj with hp | hp
  all_goals rcases branch_label_two z Q' s hs hQ hkl hf hg hfg hk hl with hq | hq
  · exact (hpq (diff_injective z (hp.trans hq.symm))).elim
  · rcases small_large_middle_touches_port (hs.ne hkl) (neF k) (neG k)
      (neF l) (neG l) hfg hp hq (port_support z (neF k)) (port_support z (neG l)) hmP hmQ with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases small_large_middle_touches_port (hs.ne hij) (neF i) (neG i)
      (neF j) (neG j) hfg hq hp (port_support z (neF i)) (port_support z (neG j)) hmQ hmP with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hD := diff_triangle_card P Q' z
    rw [hp, hq] at hD
    have hi' : ({s i, s j, f, g} : Finset (Fin n)).card = 4 := by
      simp [hs.ne hij, neF, neG, hfg]
    have hk' : ({s k, s l, f, g} : Finset (Fin n)).card = 4 := by
      simp [hs.ne hkl, neF, neG, hfg]
    have hinter : ({s i, s j, f, g} : Finset (Fin n)) ∩ {s k, s l, f, g} = {f, g} := by
      ext r
      simp only [mem_inter, mem_insert, mem_singleton]
      have h₁ := hs.ne hik
      have h₂ := hs.ne hil
      have h₃ := hs.ne hjk
      have h₄ := hs.ne hjl
      grind
    rw [hi', hk', hinter, show ({f, g} : Finset (Fin n)).card = 2 by simp [hfg]] at hD
    have hstep := two_step_distance hmP hmQ.symm hpq
    change (diff P Q').card = 2 at hstep
    omega

#print axioms two_diagonal_middle_touches_port

/-- The signed star with a distinguished matched diagonal yields neither
theta graph. Both exclusions use the actual degree-two middle vertices. -/
private lemma four_high_star_obstruction
    {n : ℕ} {S : Finset (Q n)} (hb : IsBalanced S)
    {L R : Finset (S : Set (Q n))}
    (hpart : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (L : Set (S : Set (Q n))) (R : Set (S : Set (Q n))))
    (e : cycleGraph 4 ≃g compressed ((hypercube n).induce (S : Set (Q n))) L)
    (B : Fin 4 ↪ SideHigh ((hypercube n).induce (S : Set (Q n))) R)
    (hB : ∀ i y, ((hypercube n).induce (S : Set (Q n))).Adj (e i).val y.val ↔ y = B i)
    (hr : Fintype.card (SideHigh ((hypercube n).induce (S : Set (Q n))) R) = 6)
    (hd : ∀ y, (compressed ((hypercube n).induce (S : Set (Q n))) R).degree y =
      if y ∈ Set.range B then 2 else 3)
    (z : Q n) (s : Fin 4 → Fin n) (hs : Function.Injective s)
    (hA : ∀ i, (e i).val.val = flip z (s i))
    (h02 : (compressed ((hypercube n).induce (S : Set (Q n))) R).Adj (B 0) (B 2)) : False := by
  let G := (hypercube n).induce (S : Set (Q n))
  let H := compressed G R
  have hgirth := BalancedCubeGirth.eight_le_egirth S hb
  have hcross (i : Fin 4) : G.Adj (e i).val (B i).val := (hB i (B i)).mpr rfl
  have hdiag_table : ∀ i j : Fin 4, i ≠ j → ¬ (cycleGraph 4).Adj i j → j = i + 2 := by
    decide +kernel
  have hdiag (i j : Fin 4) (h : H.Adj (B i) (B j)) : j = i + 2 :=
    hdiag_table i j (fun he => h.ne (congrArg B he))
      (matched_edge_over_diagonal hpart hgirth e B hcross h)
  obtain ⟨P, Q', hpq, hP, hQ, htheta⟩ :=
    theta_from_matched_diagonal H hr B hd hdiag h02 (compressed_triangle_free hpart.symm hgirth)
  have hav (x : SideHigh G R) (hx : x ∉ Set.range B) (i : Fin 4) :
      ¬ (hypercube n).Adj x.val.val (flip z (s i)) := by
    intro h
    rw [← hA i] at h
    exact hx ⟨i, ((hB i x).mp h.symm).symm⟩
  obtain ⟨f, hf, B0, B2, m, hm, hm0, hm2, hmz⟩ :=
    star_matched_diagonal_midpoint hb e B hB z s hs hA (by decide +kernel) h02
  have hfne (k : Fin 4) (hk0 : k ≠ 0) (hk2 : k ≠ 2) {t : Fin n}
      (hkt : (B k).val.val = flip (flip z t) (s k)) : f ≠ t := by
    intro he
    have hmK : G.Adj m (B k).val := by
      change (hypercube n).Adj m.val (B k).val.val
      rw [hmz, hkt, he]
      exact BalancedCriticalSpectrum.flip_adj _ _
    exact low_not_three hm
      (fun h => (by decide : (0 : Fin 4) ≠ 2) (B.injective (Subtype.ext h)))
      (fun h => hk0 (B.injective (Subtype.ext h)).symm)
      (fun h => hk2 (B.injective (Subtype.ext h)).symm)
      hm0.symm hm2.symm hmK
  have choose_order (a b : Fin 4)
      (hne : (decide (H.Adj P (B a))) ≠ decide (H.Adj P (B b)))
      (ha : ¬ (H.Adj Q' (B a) ↔ H.Adj P (B a)))
      (hb' : ¬ (H.Adj Q' (B b) ↔ H.Adj P (B b))) :
      ∃ x : Bool, H.Adj P (B (if x then a else b)) ∧ H.Adj Q' (B (if x then b else a)) := by
    by_cases hp : H.Adj P (B a)
    · have hn : ¬ H.Adj P (B b) := by
        intro ht
        apply hne
        simp [hp, ht]
      exact ⟨true, by simp [hp], by simpa [hn] using hb'⟩
    · have hy : H.Adj P (B b) := by
        by_contra hn
        apply hne
        simp [hp, hn]
      exact ⟨false, by simp [hy], by simpa [hp] using ha⟩
  let near (b : Bool) : Fin 4 := if b then 0 else 2
  let far (b : Bool) : Fin 4 := if b then 2 else 0
  have coordF (b : Bool) :
      (B (near b)).val.val = flip (flip z f) (s (near b)) ∧
        (B (far b)).val.val = flip (flip z f) (s (far b)) := by
    cases b
    · exact ⟨B2, B0⟩
    · exact ⟨B0, B2⟩
  have transfer (x : SideHigh G R) (i : Fin 4) {t : Fin n}
      (h : H.Adj x (B i)) (ht : (B i).val.val = flip (flip z t) (s i)) :
      hammingDist x.val.val (flip (flip z t) (s i)) = 2 := ht ▸ compressed_distance h
  rcases htheta with ⟨h13, hPQ, hx, hy, haltern⟩ | ⟨_, _, hp1, hq1, hp3, hq3, hx, ha, hb'⟩
  · obtain ⟨g, hge, B1, B3, _, _, _, _, _⟩ :=
      star_matched_diagonal_midpoint hb e B hB z s hs hA (by decide +kernel) h13
    have hfg := hfne 1 (by decide) (by decide) B1
    obtain ⟨r, hpF, hqF⟩ := choose_order 0 2 hx (haltern 0) (haltern 2)
    obtain ⟨t, hpG, hqG⟩ := choose_order 1 3 hy (haltern 1) (haltern 3)
    let oddNear (b : Bool) : Fin 4 := if b then 1 else 3
    let oddFar (b : Bool) : Fin 4 := if b then 3 else 1
    have coordG :
        (B (oddNear t)).val.val = flip (flip z g) (s (oddNear t)) ∧
          (B (oddFar t)).val.val = flip (flip z g) (s (oddFar t)) := by
      cases t
      · exact ⟨B3, B1⟩
      · exact ⟨B1, B3⟩
    have hne₁ : near r ≠ oddNear t := by cases r <;> cases t <;> decide
    have hne₂ : near r ≠ far r := by cases r <;> decide
    have hne₃ : near r ≠ oddFar t := by cases r <;> cases t <;> decide
    have hne₄ : oddNear t ≠ far r := by cases r <;> cases t <;> decide
    have hne₅ : oddNear t ≠ oddFar t := by cases t <;> decide
    have hne₆ : far r ≠ oddFar t := by cases r <;> cases t <;> decide
    obtain ⟨_, l, hl, hpL, hqL⟩ := hPQ
    have hn : P.val.val ≠ Q'.val.val := fun he => hpq (Subtype.ext (Subtype.ext he))
    have htouch := two_diagonal_middle_touches_port z P.val.val Q'.val.val l.val s hs
      (hav P hP) (hav Q' hQ) hn hne₁ hne₂ hne₃ hne₄ hne₅ hne₆ hf hge hfg
      (transfer P _ hpF (coordF r).1) (transfer P _ hpG coordG.1)
      (transfer Q' _ hqF (coordF r).2) (transfer Q' _ hqG coordG.2) hpL hqL
    have cannot (k : Fin 4) (he : G.Adj l (B k).val) : False :=
      low_not_three hl (fun h => hpq (Subtype.ext h))
        (fun h => hP ⟨k, (Subtype.ext h).symm⟩)
        (fun h => hQ ⟨k, (Subtype.ext h).symm⟩) hpL.symm hqL.symm he
    rcases htouch with h | h | h | h
    · exact cannot _ ((coordF r).1 ▸ h)
    · exact cannot _ (coordG.1 ▸ h)
    · exact cannot _ ((coordF r).2 ▸ h)
    · exact cannot _ (coordG.2 ▸ h)
  · obtain ⟨g, hge, B1⟩ := star_ports_outside e B hB z s hs hA 1
    obtain ⟨h, hhe, B3⟩ := star_ports_outside e B hB z s hs hA 3
    have hfg := hfne 1 (by decide) (by decide) B1
    obtain ⟨r, hpF, hqF⟩ := choose_order 0 2 hx ha hb'
    have hne₁ : near r ≠ 1 := by cases r <;> decide
    have hne₂ : near r ≠ 3 := by cases r <;> decide
    have hne₃ : far r ≠ 1 := by cases r <;> decide
    have hne₄ : far r ≠ 3 := by cases r <;> decide
    have h13 : (1 : Fin 4) ≠ 3 := by decide
    have hp := branch_label_three z P.val.val s hs (hav P hP) hne₁ hne₂ h13
      hf hge hhe hfg (transfer P _ hpF (coordF r).1) (transfer P _ hp1 B1) (transfer P _ hp3 B3)
    have hq := branch_label_three z Q'.val.val s hs (hav Q' hQ) hne₃ hne₄ h13
      hf hge hhe hfg (transfer Q' _ hqF (coordF r).2) (transfer Q' _ hq1 B1) (transfer Q' _ hq3 B3)
    exact hpq (Subtype.ext (Subtype.ext (diff_injective z (hp.trans hq.symm))))

#print axioms four_high_star_obstruction

/-- A balanced slice cannot have this four-high and six-high compression. -/
private lemma four_high_slice_impossible
    {n : ℕ} {S : Finset (Q n)} (hb : IsBalanced S)
    {L R : Finset (S : Set (Q n))}
    (hpart : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (L : Set (S : Set (Q n))) (R : Set (S : Set (Q n))))
    (hdeg : ∀ v, ((hypercube n).induce (S : Set (Q n))).degree v = 2 ∨
      ((hypercube n).induce (S : Set (Q n))).degree v = 3)
    (hlow : ∀ {v w}, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False)
    (e : cycleGraph 4 ≃g compressed ((hypercube n).induce (S : Set (Q n))) L)
    (hcount : ∀ x : SideHigh ((hypercube n).induce (S : Set (Q n))) L,
      (GirthSliceCounting.degreeThree ((hypercube n).induce (S : Set (Q n)))
        (((hypercube n).induce (S : Set (Q n))).neighborFinset x.val)).card = 1)
    (hR : Fintype.card (SideHigh ((hypercube n).induce (S : Set (Q n))) R) = 6) : False := by
  obtain ⟨z, s, B, hs, hA, hB, hd, i, j, hne, hnon, h⟩ :=
    four_high_side_is_star hb hpart hdeg hlow e hcount hR
  let G := (hypercube n).induce (S : Set (Q n))
  have diag : ∀ i j : Fin 4, i ≠ j → ¬ (cycleGraph 4).Adj i j → j = i + 2 := by decide +kernel
  have hj := diag i j hne hnon
  have rotateAdj : ∀ a b c : Fin 4,
      (cycleGraph 4).Adj (a + c) (b + c) ↔ (cycleGraph 4).Adj a b := by decide +kernel
  let rot : cycleGraph 4 ≃g cycleGraph 4 :=
    { toEquiv := Equiv.addRight i, map_rel_iff' := fun {a b} => rotateAdj a b i }
  let e' := rot.trans e
  let B' : Fin 4 ↪ SideHigh G R := rot.toEquiv.toEmbedding.trans B
  have same_range : Set.range B' = Set.range B := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨rot k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨rot.symm k, by change B (rot (rot.symm k)) = B k; rw [rot.apply_symm_apply]⟩
  have hd' (x : SideHigh G R) : (compressed G R).degree x =
      if x ∈ Set.range B' then 2 else 3 := by
    simp only [same_range]
    exact hd x
  have hB' (k : Fin 4) (y : SideHigh G R) : G.Adj (e' k).val y.val ↔ y = B' k :=
    hB (rot k) y
  have hA' (k : Fin 4) : (e' k).val.val = flip z ((s ∘ rot) k) := hA (rot k)
  have h02 : (compressed G R).Adj (B' 0) (B' 2) := by
    change (compressed G R).Adj (B (0 + i)) (B (2 + i))
    rw [zero_add, add_comm 2, ← hj]
    exact h
  exact four_high_star_obstruction hb hpart e' B' hB' hR hd' z (s ∘ rot)
    (hs.comp rot.injective) hA' h02

#print axioms four_high_slice_impossible
