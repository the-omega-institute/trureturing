/- GID: D5/S3/Combinatorics/Partitions/LyudogovskiyDimensionJump
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/LyudogovskiyDimensionJump
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram]
   utility: none
   digest: The sharp local simplex dimension jump across a partition transfer is two. -/

import D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

/-!
# Sharp local simplex dimension jump in the partition graph

Each edge changes the maximum clique dimension through its endpoint by at most two.
The family of edges with row lists (k, k, k − 2, 1) and (k, k, k − 1) attains two
for every k ≥ 4, resolving Lyudogovskiy's Problem 8.4.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Partitions.LyudogovskiyDimensionJump

open YoungDiagram LyudogovskiySimplex

/-- The distinct positive row lengths of a Young diagram. -/
private def support (d : YoungDiagram) : Finset ℕ :=
  (Finset.range (d.colLen 0)).image d.rowLen

private theorem mem_support_iff {D : YoungDiagram} {l : ℕ} :
    l ∈ support D ↔ 0 < l ∧ ∃ i, D.rowLen i = l := by
  change l ∈ (Finset.range (D.colLen 0)).image D.rowLen ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨mem_iff_lt_rowLen.mp (mem_iff_lt_colLen.mpr (Finset.mem_range.mp hi)), i, rfl⟩
  · rintro ⟨hl, i, rfl⟩
    exact ⟨i, Finset.mem_range.mpr (mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr hl)), rfl⟩

private theorem one_cell {D E : YoungDiagram} (hDE : D ≤ E) (hcard : E.card = D.card + 1) :
    ∃ c, E.cells \ D.cells = {c} := by
  apply Finset.card_eq_one.mp
  rw [Finset.card_sdiff_of_subset (cells_subset_iff.mpr hDE)]
  change E.card - D.card = 1
  omega

private theorem mem_one_cell {D E : YoungDiagram} {c : ℕ × ℕ} (hc : E.cells \ D.cells = {c}) :
    c ∈ E ∧ c ∉ D :=
  Finset.mem_sdiff.mp (by rw [hc]; exact Finset.mem_singleton_self c)

private theorem eq_one_cell {D E : YoungDiagram} {c x : ℕ × ℕ}
    (hc : E.cells \ D.cells = {c}) (hE : x ∈ E) (hD : x ∉ D) : x = c := by
  have h : x ∈ E.cells \ D.cells := Finset.mem_sdiff.mpr ⟨hE, hD⟩
  rw [hc] at h
  exact Finset.mem_singleton.mp h

private theorem extension_key_injective {X : YoungDiagram}
    {c d : ℕ × ℕ} {A B : YoungDiagram}
    (hc : A.cells \ X.cells = {c}) (hd : B.cells \ X.cells = {d})
    (hkey : (if c.1 < X.colLen 0 then some c.2 else none) =
      (if d.1 < X.colLen 0 then some d.2 else none)) : c = d := by
  by_cases hci : c.1 < X.colLen 0
  · by_cases hdi : d.1 < X.colLen 0
    · simp only [hci, hdi, ite_true] at hkey
      have hcd2 : c.2 = d.2 := Option.some.inj hkey
      obtain ⟨hcA, hcX⟩ := mem_one_cell hc
      obtain ⟨hdB, hdX⟩ := mem_one_cell hd
      by_cases hle : c.1 ≤ d.1
      · exact eq_one_cell hd (B.up_left_mem hle hcd2.le hdB) hcX
      · exact (eq_one_cell hc (A.up_left_mem (by omega) hcd2.ge hcA) hdX).symm
    · simp only [hci, hdi, ite_true, ite_false] at hkey
      contradiction
  · by_cases hdi : d.1 < X.colLen 0
    · simp only [hci, hdi, ite_false, ite_true] at hkey
      contradiction
    · simp only [hci, hdi, ite_false] at hkey
      have hc_le : X.colLen 0 ≤ c.1 := by omega
      have hd_le : X.colLen 0 ≤ d.1 := by omega
      have hc_eq : c.1 = X.colLen 0 := by
        by_contra hne
        have hx : (X.colLen 0, 0) ∈ A :=
          A.isLowerSet (show (X.colLen 0, 0) ≤ c by constructor <;> omega) (mem_one_cell hc).1
        have hxX : (X.colLen 0, 0) ∉ X := by
          rw [YoungDiagram.mem_iff_lt_colLen]
          simp
        exact hne (congrArg Prod.fst (eq_one_cell hc hx hxX)).symm
      have hd_eq : d.1 = X.colLen 0 := by
        by_contra hne
        have hx : (X.colLen 0, 0) ∈ B :=
          B.isLowerSet (show (X.colLen 0, 0) ≤ d by constructor <;> omega) (mem_one_cell hd).1
        have hxX : (X.colLen 0, 0) ∉ X := by
          rw [YoungDiagram.mem_iff_lt_colLen]
          simp
        exact hne (congrArg Prod.fst (eq_one_cell hd hx hxX)).symm
      apply Prod.ext
      · exact hc_eq.trans hd_eq.symm
      · have hc0 : c.2 = 0 := by
          rw [← one_cell_lower_row hc]
          by_contra hpos
          exact hci (mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hpos)))
        have hd0 : d.2 = 0 := by
          rw [← one_cell_lower_row hd]
          by_contra hpos
          exact hdi (mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hpos)))
        omega

private theorem star_card_bound {n : ℕ} (hn : 0 < n)
    (C : Finset (Nat.Partition n))
    {X : YoungDiagram} (hX : X.card = n - 1)
    (hsub : ∀ p ∈ C, X ≤ YoungDiagram.ofPartition p) :
    C.card - 1 ≤ (support X).card := by
  classical
  have hm (p : C) : ∃ c : ℕ × ℕ,
      (YoungDiagram.ofPartition p.val).cells \ X.cells = {c} := by
    apply one_cell (hsub p.val p.property)
    rw [YoungDiagram.card_ofPartition, hX]
    omega
  let f (p : C) := Classical.choose (hm p)
  have hf (p : C) : (YoungDiagram.ofPartition p.val).cells \ X.cells = {f p} :=
    Classical.choose_spec (hm p)
  have hf_inj : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply diagram_injective
    apply YoungDiagram.ext
    rw [single_extension_cells (hsub p.val p.property) (hf p),
      single_extension_cells (hsub q.val q.property) (hf q), he]
  let g (p : C) : Option ℕ :=
    if (f p).1 < X.colLen 0 then some (f p).2 else none
  have hg_inj : Function.Injective g := by
    intro p q he
    apply hf_inj
    exact extension_key_injective (hf p) (hf q) he
  have hg_mem (p : C) : g p ∈ insert none ((support X).image some) := by
    by_cases hi : (f p).1 < X.colLen 0
    · have hg : g p = some (f p).2 := by simp [g, hi]
      rw [hg, Finset.mem_insert]
      right
      apply Finset.mem_image.mpr
      refine ⟨(f p).2, ?_, rfl⟩
      rw [← one_cell_lower_row (hf p)]
      exact Finset.mem_image.mpr ⟨(f p).1, Finset.mem_range.mpr hi, rfl⟩
    · have hg : g p = none := by simp [g, hi]
      rw [hg]
      simp
  let G := (Finset.univ : Finset C).image g
  have hGcard : G.card = C.card := by
    change ((Finset.univ : Finset C).image g).card = C.card
    rw [Finset.card_image_of_injective _ hg_inj]
    simp
  have hGsub : G ⊆ insert none ((support X).image some) := by
    intro z hz
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hz
    exact hg_mem p
  have hcard := Finset.card_le_card hGsub
  rw [hGcard] at hcard
  have htarget : (insert none ((support X).image some)).card = (support X).card + 1 := by
    have hsome : Function.Injective (fun k : ℕ => some k) :=
      fun a b h => Option.some.inj h
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ hsome]
  rw [htarget] at hcard
  omega

private theorem top_corner_injective {U A B : YoungDiagram} {c d : ℕ × ℕ}
    (hc : U.cells \ A.cells = {c}) (hd : U.cells \ B.cells = {d})
    (he : c.2 = d.2) : c = d := by
  apply Prod.ext
  · by_contra hne
    by_cases hlt : c.1 < d.1
    · obtain ⟨hdU, -⟩ := mem_one_cell hd
      have hdA : d ∈ A := by
        by_contra hnot
        have heq := eq_one_cell hc hdU hnot
        exact hne (congrArg Prod.fst heq.symm)
      have hcA : c ∈ A := A.isLowerSet (show c ≤ d by constructor <;> omega) hdA
      exact (mem_one_cell hc).2 hcA
    · have hlt' : d.1 < c.1 := by omega
      have hcU := (mem_one_cell hc).1
      have hcB : c ∈ B := by
        by_contra hnot
        have heq := eq_one_cell hd hcU hnot
        exact hne (congrArg Prod.fst heq)
      have hdB : d ∈ B := B.isLowerSet (show d ≤ c by constructor <;> omega) hcB
      exact (mem_one_cell hd).2 hdB
  · exact he

private theorem top_card_bound {n : ℕ} (C : Finset (Nat.Partition n))
    {U : YoungDiagram} (hU : U.card = n + 1)
    (hsub : ∀ p ∈ C, YoungDiagram.ofPartition p ≤ U) :
    C.card - 1 ≤ (support U).card - 1 := by
  classical
  have hm (p : C) : ∃ c : ℕ × ℕ,
      U.cells \ (YoungDiagram.ofPartition p.val).cells = {c} := by
    apply one_cell (hsub p.val p.property)
    rw [YoungDiagram.card_ofPartition, hU]
  let f (p : C) := Classical.choose (hm p)
  have hf (p : C) : U.cells \ (YoungDiagram.ofPartition p.val).cells = {f p} :=
    Classical.choose_spec (hm p)
  have hf_inj : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply diagram_injective
    apply YoungDiagram.ext
    rw [single_removal_cells (hsub p.val p.property) (hf p),
      single_removal_cells (hsub q.val q.property) (hf q), he]
  let f' (p : C) := (f p).2 + 1
  have hf'_inj : Function.Injective f' := by
    intro p q he
    have he' : (f p).2 = (f q).2 := by
      dsimp [f'] at he
      omega
    apply hf_inj
    exact top_corner_injective (hf p) (hf q) he'
  let G := (Finset.univ : Finset C).image f'
  have hGcard : G.card = C.card := by
    change ((Finset.univ : Finset C).image f').card = C.card
    rw [Finset.card_image_of_injective _ hf'_inj]
    simp
  have hGsub : G ⊆ support U := by
    intro z hz
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hz
    exact mem_support_iff.mpr ⟨by simp [f'], (f p).1, one_cell_row (hf p)⟩
  have hcard := Finset.card_le_card hGsub
  rw [hGcard] at hcard
  omega

private theorem clique_capacity {n : ℕ} (hn : 0 < n) (C : Finset (Nat.Partition n))
    (hC : (graph n).IsClique (C : Set (Nat.Partition n)))
    (hcard : 2 ≤ C.card) :
    (∃ X : YoungDiagram, X.card = n - 1 ∧
      (∀ p ∈ C, X ≤ YoungDiagram.ofPartition p) ∧
      C.card - 1 ≤ (support X).card) ∨
    (∃ U : YoungDiagram, U.card = n + 1 ∧
      (∀ p ∈ C, YoungDiagram.ofPartition p ≤ U) ∧
      C.card - 1 ≤ (support U).card - 1) := by
  rcases clique_star_or_top hn C hC hcard with ⟨X, hX, hsub⟩ | ⟨U, hU, hsub⟩
  · exact Or.inl ⟨X, hX, hsub, star_card_bound hn C hX hsub⟩
  · exact Or.inr ⟨U, hU, hsub, top_card_bound C hU hsub⟩

private theorem unchanged_row {D E : YoungDiagram} {c : ℕ × ℕ} (hDE : D ≤ E)
    (hc : E.cells \ D.cells = {c}) {i : ℕ} (hi : i ≠ c.1) :
    D.rowLen i = E.rowLen i := by
  rw [rowLen_eq_card, rowLen_eq_card]
  congr 1
  ext x
  simp only [mem_row_iff]
  constructor
  · exact fun ⟨hx, hxi⟩ => ⟨hDE hx, hxi⟩
  · rintro ⟨hx, hxi⟩
    refine ⟨?_, hxi⟩
    by_contra hn
    exact hi (hxi.symm.trans (congrArg Prod.fst (eq_one_cell hc hx hn)))

private theorem support_le_of_unchanged_rows {D E : YoungDiagram} {i : ℕ}
    (h : ∀ j ≠ i, D.rowLen j = E.rowLen j) :
    (support D).card ≤ (support E).card + 1 := by
  have hs : support D ⊆ insert (D.rowLen i) (support E) := by
    intro l hl
    obtain ⟨hpos, j, hj⟩ := mem_support_iff.mp hl
    by_cases he : j = i
    · exact Finset.mem_insert.mpr (Or.inl (he ▸ hj.symm))
    · exact Finset.mem_insert.mpr (Or.inr (mem_support_iff.mpr ⟨hpos, j, (h j he).symm.trans hj⟩))
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

private theorem support_comparison {D E : YoungDiagram} (hDE : D ≤ E)
    (hcard : E.card = D.card + 1) :
    (support D).card ≤ (support E).card + 1 ∧ (support E).card ≤ (support D).card + 1 := by
  obtain ⟨c, hc⟩ := one_cell hDE hcard
  exact ⟨support_le_of_unchanged_rows (fun _ => unchanged_row hDE hc),
    support_le_of_unchanged_rows (fun _ hj => (unchanged_row hDE hc hj).symm)⟩

private def addCorner (D : YoungDiagram) (c : ℕ × ℕ) (h : ∀ x ≤ c, x ≠ c → x ∈ D) :
    YoungDiagram where
  cells := insert c D.cells
  isLowerSet := by
    intro y x hxy hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · by_cases he : x = y
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert.mpr (Or.inr (h x hxy he))
    · exact Finset.mem_insert.mpr (Or.inr (D.isLowerSet hxy hy))

private def removeCorner (D : YoungDiagram) (c : ℕ × ℕ) (h : ∀ x ∈ D, c ≤ x → x = c) :
    YoungDiagram where
  cells := D.cells.erase c
  isLowerSet := by
    intro y x hxy hy
    obtain ⟨hne, hym⟩ := Finset.mem_erase.mp hy
    refine Finset.mem_erase.mpr ⟨?_, D.isLowerSet hxy hym⟩
    rintro rfl
    exact hne (h y hym hxy)

/-- The column of index l ends just before the first row of length l.
For l = 0 this selects the new bottom row. -/
private theorem firstOfLength (D : YoungDiagram) {l : ℕ} (hl : l ∈ insert 0 (support D)) :
    D.rowLen (D.colLen l) = l := by
  have hle : D.rowLen (D.colLen l) ≤ l := by
    by_contra! h
    exact (Nat.lt_irrefl _) (mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr h))
  refine le_antisymm hle ?_
  rcases Finset.mem_insert.mp hl with rfl | hl
  · exact Nat.zero_le _
  obtain ⟨_, i, hi⟩ := mem_support_iff.mp hl
  have hci : D.colLen l ≤ i := by
    by_contra! h
    have hm := mem_iff_lt_rowLen.mp (mem_iff_lt_colLen.mpr h : (i, l) ∈ D)
    omega
  calc
    l = D.rowLen i := hi.symm
    _ ≤ D.rowLen (D.colLen l) := D.rowLen_anti _ _ hci

private theorem firstOfLength_addable (D : YoungDiagram) {l : ℕ}
    (hl : l ∈ insert 0 (support D)) :
    ∀ x ≤ (D.colLen l, l), x ≠ (D.colLen l, l) → x ∈ D := by
  intro x h hx
  rcases x with ⟨i, j⟩
  obtain ⟨hi, hj⟩ := Prod.mk_le_mk.mp h
  rcases hi.lt_or_eq with hi | rfl
  · exact D.up_left_mem le_rfl hj (mem_iff_lt_colLen.mpr hi)
  · apply mem_iff_lt_rowLen.mpr
    rw [firstOfLength D hl]
    exact lt_of_le_of_ne hj (fun he => hx (by rw [he]))

/-- The last cell in column l - 1 ends the last row of positive length l. -/
private theorem lastOfLength_removable (D : YoungDiagram) {l : ℕ} (hl : l ∈ support D) :
    let c := (D.colLen (l - 1) - 1, l - 1)
    c ∈ D ∧ ∀ x ∈ D, c ≤ x → x = c := by
  obtain ⟨hlpos, i, hi⟩ := mem_support_iff.mp hl
  have hicol : i < D.colLen (l - 1) := by
    apply mem_iff_lt_colLen.mp
    apply mem_iff_lt_rowLen.mpr
    omega
  refine ⟨mem_iff_lt_colLen.mpr (by omega), ?_⟩
  rintro ⟨a, b⟩ hx h
  obtain ⟨ha, hb⟩ := Prod.mk_le_mk.mp h
  have hacol : a < D.colLen (l - 1) :=
    mem_iff_lt_colLen.mp (D.up_left_mem le_rfl hb hx)
  have hlen := D.rowLen_anti i a (by omega)
  have hbLen := mem_iff_lt_rowLen.mp hx
  exact Prod.ext (by omega) (by omega)

private theorem clique_dimension_upper {n bound : ℕ} {p : Nat.Partition n}
    (h : ∀ C : Finset (Nat.Partition n), (graph n).IsClique (C : Set _) →
      p ∈ C → C.card - 1 ≤ bound) : localDimension p ≤ bound := by
  classical
  unfold localDimension
  apply Finset.sup_le
  intro C hC
  have hc := Finset.mem_filter.mp hC
  apply h C _ hc.2
  exact (Finset.mem_filter.mp hc.1).2

private theorem inter_card_le_of_ne {n : ℕ} {p q : Nat.Partition n} (hne : p ≠ q) :
    (ofPartition p ⊓ ofPartition q).card ≤ n - 1 := by
  let I := ofPartition p ⊓ ofPartition q
  have hp : I ≤ ofPartition p := inf_le_left
  have hq : I ≤ ofPartition q := inf_le_right
  have hc := Finset.card_le_card (cells_subset_iff.mpr hp)
  change I.card ≤ (ofPartition p).card at hc
  rw [card_ofPartition] at hc
  change I.card ≤ n - 1
  by_contra! h
  have he : I.card = n := by omega
  have hEq (v : Nat.Partition n) (hv : I ≤ ofPartition v) : I = ofPartition v := by
    apply YoungDiagram.ext
    apply Finset.eq_of_subset_of_card_le (cells_subset_iff.mpr hv)
    change (ofPartition v).card ≤ I.card
    rw [card_ofPartition, he]
  exact hne (diagram_injective ((hEq p hp).symm.trans (hEq q hq)))

private theorem inter_card_add_union_card {n : ℕ} (p q : Nat.Partition n) :
    (ofPartition p ⊓ ofPartition q).card + (ofPartition p ⊔ ofPartition q).card = n + n := by
  have h := Finset.card_inter_add_card_union (ofPartition p).cells (ofPartition q).cells
  change (ofPartition p ⊓ ofPartition q).card + (ofPartition p ⊔ ofPartition q).card =
    (ofPartition p).card + (ofPartition q).card at h
  simpa only [card_ofPartition] using h

private theorem predecessor_capacity {n : ℕ} (hn : 0 < n) {X : YoungDiagram}
    (hX : X.card = n - 1) {p : Nat.Partition n} (hp : X ≤ ofPartition p) :
    (support X).card ≤ localDimension p := by
  classical
  let lengths := insert 0 (support X)
  let C := Finset.univ.filter (fun v : Nat.Partition n => X ≤ ofPartition v)
  have hpC : p ∈ C := by simp [C, hp]
  have hC : (graph n).IsClique (C : Set _) := by
    intro v hv w hw hne
    have hv' := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    have hw' := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
    have hlo := Finset.card_le_card (cells_subset_iff.mpr (le_inf hv' hw'))
    change X.card ≤ (ofPartition v ⊓ ofPartition w).card at hlo
    change UnitTransfer v w
    apply (transfer_iff_intersection hn v w).mpr
    exact le_antisymm (inter_card_le_of_ne hne) (hX ▸ hlo)
  let D (l : lengths) :=
    addCorner X (X.colLen l, l) (firstOfLength_addable X l.property)
  have hnot (l : lengths) : (X.colLen l, (l : ℕ)) ∉ X := by
    rw [mem_iff_lt_colLen]
    exact Nat.lt_irrefl _
  have hD (l : lengths) : (D l).card = n := by
    change (insert (X.colLen l, (l : ℕ)) X.cells).card = n
    rw [Finset.card_insert_of_notMem (hnot l)]
    change X.card + 1 = n
    omega
  let f (l : lengths) : Nat.Partition n := (D l).toPartition (hD l)
  have hf (l : lengths) : ofPartition (f l) = D l := ofPartition_toPartition (hD l)
  have hinj : Function.Injective f := by
    intro a b hab
    have he : D a = D b := (hf a).symm.trans ((congrArg ofPartition hab).trans (hf b))
    have hm : (X.colLen a, (a : ℕ)) ∈ (D a).cells :=
      Finset.mem_insert_self _ _
    rw [he] at hm
    rcases Finset.mem_insert.mp hm with h | h
    · exact Subtype.ext (congrArg Prod.snd h)
    · exact (hnot a h).elim
  have hsub : lengths.attach.image f ⊆ C := by
    intro v hv
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hf]
    exact cells_subset_iff.mp (Finset.subset_insert _ _)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_attach] at hc
  have hlen : lengths.card = (support X).card + 1 :=
    Finset.card_insert_of_notMem (fun h => Nat.lt_irrefl _ (mem_support_iff.mp h).1)
  have hlocal := clique_le_local C hC p hpC
  omega

private theorem successor_capacity {n : ℕ} (hn : 0 < n) {U : YoungDiagram}
    (hU : U.card = n + 1) {p : Nat.Partition n} (hp : ofPartition p ≤ U) :
    (support U).card - 1 ≤ localDimension p := by
  classical
  let C := Finset.univ.filter (fun v : Nat.Partition n => ofPartition v ≤ U)
  have hpC : p ∈ C := by simp [C, hp]
  have hC : (graph n).IsClique (C : Set _) := by
    intro v hv w hw hne
    have hv' := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    have hw' := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
    have hhi := Finset.card_le_card (cells_subset_iff.mpr (sup_le hv' hw'))
    change (ofPartition v ⊔ ofPartition w).card ≤ U.card at hhi
    have hsum := inter_card_add_union_card v w
    have hlo := inter_card_le_of_ne hne
    change UnitTransfer v w
    apply (transfer_iff_intersection hn v w).mpr
    omega
  let c (l : support U) := (U.colLen ((l : ℕ) - 1) - 1, (l : ℕ) - 1)
  let D (l : support U) := removeCorner U (c l) (lastOfLength_removable U l.property).2
  have hmem (l : support U) : c l ∈ U := (lastOfLength_removable U l.property).1
  have hD (l : support U) : (D l).card = n := by
    change (U.cells.erase (c l)).card = n
    rw [Finset.card_erase_of_mem (hmem l)]
    change U.card - 1 = n
    omega
  let f (l : support U) : Nat.Partition n := (D l).toPartition (hD l)
  have hf (l : support U) : ofPartition (f l) = D l := ofPartition_toPartition (hD l)
  have hinj : Function.Injective f := by
    intro a b hab
    have he : D a = D b := (hf a).symm.trans ((congrArg ofPartition hab).trans (hf b))
    have hc : c a = c b := by
      by_contra hne
      have hma : c a ∈ (D b).cells := Finset.mem_erase.mpr ⟨hne, hmem a⟩
      rw [← he] at hma
      exact Finset.notMem_erase _ _ hma
    have hcol : (a : ℕ) - 1 = (b : ℕ) - 1 := congrArg Prod.snd hc
    have ha := (mem_support_iff.mp a.property).1
    have hb := (mem_support_iff.mp b.property).1
    exact Subtype.ext (by omega)
  have hsub : (support U).attach.image f ⊆ C := by
    intro v hv
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hf]
    exact cells_subset_iff.mp (Finset.erase_subset _ _)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_attach] at hc
  have hlocal := clique_le_local C hC p hpC
  omega

private theorem localDimension_le_of_adj {n : ℕ} (hn : 0 < n)
    {p q : Nat.Partition n} (h : (graph n).Adj p q) :
    localDimension p ≤ localDimension q + 2 := by
  let A := ofPartition p
  let B := ofPartition q
  let X := A ⊓ B
  let U := A ⊔ B
  have hA : A.card = n := card_ofPartition p
  have hX : X.card = n - 1 := (transfer_iff_intersection hn p q).mp h
  have hU : U.card = n + 1 := by
    have hsum : X.card + U.card = n + n := inter_card_add_union_card p q
    omega
  have hstar := predecessor_capacity hn hX (p := q) inf_le_right
  have htop := successor_capacity hn hU (p := q) le_sup_right
  apply clique_dimension_upper
  intro C hC hp
  by_cases hc : 2 ≤ C.card
  · rcases clique_capacity hn C hC hc with ⟨Y, hY, hsub, hcap⟩ | ⟨V, hV, hsub, hcap⟩
    · have hYA : (support Y).card ≤ (support A).card + 1 :=
        (support_comparison (hsub p hp) (by omega : A.card = Y.card + 1)).1
      have hAX : (support A).card ≤ (support X).card + 1 :=
        (support_comparison (inf_le_left : X ≤ A) (by omega : A.card = X.card + 1)).2
      omega
    · have hVA : (support V).card ≤ (support A).card + 1 :=
        (support_comparison (hsub p hp) (by omega : V.card = A.card + 1)).2
      have hAU : (support A).card ≤ (support U).card + 1 :=
        (support_comparison (le_sup_left : A ≤ U) (by omega : U.card = A.card + 1)).1
      omega
  · omega

/-- The local dimensions at the two ends of any actual transfer edge differ by at most two. -/
private theorem local_dimension_jump {n : ℕ} (hn : 0 < n) {p q : Nat.Partition n}
    (h : (graph n).Adj p q) :
    localDimension p ≤ localDimension q + 2 ∧ localDimension q ≤ localDimension p + 2 :=
  ⟨localDimension_le_of_adj hn h, localDimension_le_of_adj hn h.symm⟩

private theorem support_eq_rowLens (D : YoungDiagram) : support D = D.rowLens.toFinset := by
  ext l
  change l ∈ (Finset.range (D.colLen 0)).image D.rowLen ↔ l ∈ D.rowLens.toFinset
  simp only [Finset.mem_image, Finset.mem_range, List.mem_toFinset, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, by simpa only [length_rowLens] using hi, get_rowLens.trans he⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, by simpa only [length_rowLens] using hi, get_rowLens.symm.trans he⟩

private theorem rowLen_ofRows {w : List ℕ} {hw : w.SortedGE} (i : ℕ) :
    (ofRowLens w hw).rowLen i = w[i]?.getD 0 := by
  by_cases hi : i < w.length
  · rw [List.getElem?_eq_getElem hi]
    exact rowLen_ofRowLens ⟨i, hi⟩
  · rw [List.getElem?_eq_none (by omega)]
    change (ofRowLens w hw).rowLen i = 0
    by_contra! h
    have hm : (i, 0) ∈ ofRowLens w hw := mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
    exact hi (mem_ofRowLens.mp hm).choose

private theorem diagram_le_of_rows {D E : YoungDiagram} (h : ∀ i, D.rowLen i ≤ E.rowLen i) :
    D ≤ E := by
  rintro ⟨i, j⟩ hij
  exact mem_iff_lt_rowLen.mpr ((mem_iff_lt_rowLen.mp hij).trans_le (h i))

private theorem card_ofRows {w : List ℕ} {hw : w.SortedGE} (hpos : ∀ l ∈ w, 0 < l) :
    (ofRowLens w hw).card = w.sum := by
  rw [← sum_rowLens_eq_card, rowLens_ofRowLens_eq_self hpos]

private theorem support_ofRows {w : List ℕ} {hw : w.SortedGE} (hpos : ∀ l ∈ w, 0 < l) :
    support (ofRowLens w hw) = w.toFinset := by
  rw [support_eq_rowLens, rowLens_ofRowLens_eq_self hpos]

private def rightDiagram (k : ℕ) : YoungDiagram :=
  ofRowLens [k, k, k - 1] (by simp [List.sortedGE_cons, List.sortedGE_nil])

private theorem right_rowLen (k i : ℕ) :
    (rightDiagram k).rowLen i = if i < 2 then k else if i = 2 then k - 1 else 0 := by
  unfold rightDiagram
  rw [rowLen_ofRows]
  by_cases hi : i < 3
  · interval_cases i <;> rfl
  · have hi₂ : ¬ i < 2 := by omega
    have hne : i ≠ 2 := by omega
    rw [List.getElem?_eq_none (by simpa using (Nat.le_of_not_gt hi)), ite_eq_right hi₂, ite_eq_right hne]
    rfl

private theorem right_support (k : ℕ) (hk : 4 ≤ k) : (support (rightDiagram k)).card = 2 := by
  unfold rightDiagram
  have hpos : ∀ l ∈ [k, k, k - 1], 0 < l := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro l (rfl | rfl | rfl) <;> omega
  rw [support_ofRows hpos]
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_idem]
  exact Finset.card_pair (by omega)

private theorem right_predecessor_support {k : ℕ} {D : YoungDiagram} (hD : D ≤ rightDiagram k)
    (hcard : (rightDiagram k).card = D.card + 1) : (support D).card ≤ 2 := by
  obtain ⟨c, hc⟩ := one_cell hD hcard
  obtain ⟨hcB, hcD⟩ := mem_one_cell hc
  have hlt : c.2 < (rightDiagram k).rowLen c.1 := mem_iff_lt_rowLen.mp hcB
  have hfirst : c.1 ≠ 0 := by
    intro he
    have hm : (1, c.2) ∈ rightDiagram k := by
      apply mem_iff_lt_rowLen.mpr
      rw [right_rowLen, ite_eq_left (by decide : 1 < 2)]
      simpa only [he, right_rowLen, ite_eq_left (by decide : 0 < 2)] using hlt
    have hd : (1, c.2) ∈ D := by
      by_contra hd
      have heq := congrArg Prod.fst (eq_one_cell hc hm hd)
      simp [he] at heq
    have hle : c ≤ (1, c.2) := by
      change c.1 ≤ 1 ∧ c.2 ≤ c.2
      simp [he]
    exact hcD (D.isLowerSet hle hd)
  have hc12 : c.1 = 1 ∨ c.1 = 2 := by
    rw [right_rowLen] at hlt
    split_ifs at hlt <;> omega
  rcases hc12 with h1 | h2
  · have hrow : (rightDiagram k).rowLen c.1 = D.rowLen c.1 + 1 := by
      rw [one_cell_row hc, one_cell_lower_row hc]
    rw [right_rowLen, ite_eq_left (by omega : c.1 < 2)] at hrow
    have hsub : support D ⊆ {k, k - 1} := by
      intro l hl
      obtain ⟨hpos, i, hi⟩ := mem_support_iff.mp hl
      by_cases he : i = c.1
      · have heq : l = k - 1 := by rw [he] at hi; omega
        simp [heq]
      · rw [unchanged_row hD hc he, right_rowLen] at hi
        split_ifs at hi <;> simp_all
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
  · have hsub : support D ⊆ {k, D.rowLen c.1} := by
      intro l hl
      obtain ⟨hpos, i, hi⟩ := mem_support_iff.mp hl
      by_cases he : i = c.1
      · rw [he] at hi
        simp [← hi]
      · have hine : i ≠ 2 := by omega
        rw [unchanged_row hD hc he, right_rowLen, ite_eq_right hine] at hi
        split_ifs at hi <;> simp_all
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))

private theorem right_dimension_upper {k n : ℕ} (hk : 4 ≤ k) (hn : 0 < n)
    {q : Nat.Partition n} (hq : ofPartition q = rightDiagram k) : localDimension q ≤ 2 := by
  have hB : (rightDiagram k).card = n := hq ▸ card_ofPartition q
  apply clique_dimension_upper
  intro C hC hqC
  by_cases hc : 2 ≤ C.card
  · rcases clique_capacity hn C hC hc with ⟨D, hD, hsub, hcap⟩ | ⟨U, hU, hsub, hcap⟩
    · have hle : D ≤ rightDiagram k := hq ▸ hsub q hqC
      exact hcap.trans (right_predecessor_support hle (by omega))
    · have hle : rightDiagram k ≤ U := hq ▸ hsub q hqC
      have hb := (support_comparison hle (by omega : U.card = (rightDiagram k).card + 1)).2
      rw [right_support k hk] at hb
      omega
  · omega

/-- For every k ≥ 4, the specified transfer edge has local dimensions exactly four and two. -/
private theorem local_dimension_sharp (k : ℕ) (hk : 4 ≤ k) :
    ∃ p q : Nat.Partition (3 * k - 1),
      (ofPartition p).rowLens = [k, k, k - 2, 1] ∧
      (ofPartition q).rowLens = [k, k, k - 1] ∧
      (graph (3 * k - 1)).Adj p q ∧ localDimension p = 4 ∧ localDimension q = 2 := by
  let A := ofRowLens [k, k, k - 2, 1] (by
    simp [List.sortedGE_cons, List.sortedGE_nil]
    omega)
  let B := rightDiagram k
  let X := ofRowLens [k, k, k - 2] (by simp [List.sortedGE_cons, List.sortedGE_nil])
  let Y := ofRowLens [k, k - 1, k - 2, 1] (by
    simp [List.sortedGE_cons, List.sortedGE_nil]
    omega)
  have hApos : ∀ l ∈ [k, k, k - 2, 1], 0 < l := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro l (rfl | rfl | rfl | rfl) <;> omega
  have hBpos : ∀ l ∈ [k, k, k - 1], 0 < l := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro l (rfl | rfl | rfl) <;> omega
  have hXpos : ∀ l ∈ [k, k, k - 2], 0 < l := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro l (rfl | rfl | rfl) <;> omega
  have hYpos : ∀ l ∈ [k, k - 1, k - 2, 1], 0 < l := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro l (rfl | rfl | rfl | rfl) <;> omega
  have hA : A.card = 3 * k - 1 := by
    dsimp only [A]
    rw [card_ofRows hApos]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have hB : B.card = 3 * k - 1 := by
    dsimp only [B, rightDiagram]
    rw [card_ofRows hBpos]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have hX : X.card = (3 * k - 1) - 1 := by
    dsimp only [X]
    rw [card_ofRows hXpos]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have hY : Y.card = (3 * k - 1) - 1 := by
    dsimp only [Y]
    rw [card_ofRows hYpos]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have hXA : X ≤ A := by
    apply diagram_le_of_rows
    intro i
    simp only [X, A, rowLen_ofRows]
    by_cases hi : i < 4
    · interval_cases i <;> simp
    · have h₃ : [k, k, k - 2].length ≤ i := by simpa using (show 3 ≤ i by omega)
      rw [List.getElem?_eq_none h₃]
      exact Nat.zero_le _
  have hXB : X ≤ B := by
    apply diagram_le_of_rows
    intro i
    simp only [X, B, rightDiagram, rowLen_ofRows]
    by_cases hi : i < 3
    · interval_cases i <;> simp
      omega
    · rw [List.getElem?_eq_none (by simpa using (Nat.le_of_not_gt hi))]
      exact Nat.zero_le _
  have hYA : Y ≤ A := by
    apply diagram_le_of_rows
    intro i
    simp only [Y, A, rowLen_ofRows]
    by_cases hi : i < 4
    · interval_cases i <;> simp
    · rw [List.getElem?_eq_none (by simpa using (Nat.le_of_not_gt hi))]
      exact Nat.zero_le _
  let p := A.toPartition hA
  let q := B.toPartition hB
  have hp : ofPartition p = A := ofPartition_toPartition hA
  have hq : ofPartition q = B := ofPartition_toPartition hB
  have hpq : p ≠ q := by
    intro he
    have hAB : A = B := hp.symm.trans ((congrArg ofPartition he).trans hq)
    have ha : (3, 0) ∈ A := by
      apply mem_iff_lt_rowLen.mpr
      simp [A, rowLen_ofRows]
    rw [hAB, mem_iff_lt_rowLen] at ha
    change 0 < (rightDiagram k).rowLen 3 at ha
    rw [right_rowLen] at ha
    simp at ha
  have hn : 0 < 3 * k - 1 := by omega
  have hadj : (graph (3 * k - 1)).Adj p q := by
    change UnitTransfer p q
    apply (transfer_iff_intersection hn p q).mpr
    have hle : X ≤ ofPartition p ⊓ ofPartition q := by
      rw [hp, hq]
      exact le_inf hXA hXB
    have hlo := Finset.card_le_card (cells_subset_iff.mpr hle)
    change X.card ≤ (ofPartition p ⊓ ofPartition q).card at hlo
    rw [hX] at hlo
    exact le_antisymm (inter_card_le_of_ne hpq) hlo
  have hYsupp : (support Y).card = 4 := by
    simp only [Y, support_ofRows hYpos, List.toFinset_cons, List.toFinset_nil]
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega)]
    simp
  have hXsupp : (support X).card = 2 := by
    simp only [X, support_ofRows hXpos, List.toFinset_cons, List.toFinset_nil,
      Finset.insert_idem]
    exact Finset.card_pair (by omega)
  have hpLow : 4 ≤ localDimension p := hYsupp ▸ predecessor_capacity hn hY (hp ▸ hYA)
  have hqLow : 2 ≤ localDimension q := hXsupp ▸ predecessor_capacity hn hX (hq ▸ hXB)
  have hqHigh := right_dimension_upper hk hn hq
  have hpHigh := (local_dimension_jump hn hadj).1
  refine ⟨p, q, ?_, ?_, hadj, by omega, by omega⟩
  · rw [hp]
    exact rowLens_ofRowLens_eq_self hApos
  · rw [hq]
    exact rowLens_ofRowLens_eq_self hBpos

/-- The absolute local-dimension jump is at most two, attained by the displayed
family of transfer edges for every k ≥ 4. -/
theorem result :
    (∀ (n : ℕ), 0 < n → ∀ p q : Nat.Partition n, (graph n).Adj p q →
      |(localDimension p : ℤ) - (localDimension q : ℤ)| ≤ 2) ∧
    (∀ (k : ℕ), 4 ≤ k → ∃ p q : Nat.Partition (3 * k - 1),
      (ofPartition p).rowLens = [k, k, k - 2, 1] ∧
      (ofPartition q).rowLens = [k, k, k - 1] ∧
      (graph (3 * k - 1)).Adj p q ∧ localDimension p = 4 ∧ localDimension q = 2) := by
  refine ⟨?_, local_dimension_sharp⟩
  intro n hn p q h
  obtain ⟨hp, hq⟩ := local_dimension_jump hn h
  rw [abs_le]
  constructor <;> omega

end D5.S3.Combinatorics.Partitions.LyudogovskiyDimensionJump
