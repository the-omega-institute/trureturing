/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Durfee
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Durfee
   mirror-E: none(waiver:formal-durfee-decomposition)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.Glaisher]
   utility: none
   digest: The maximal-square bijection proves the formal Durfee generating-series identity. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Euler
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Durfee

open InversionSeq207Euler
open Finset.HasAntidiagonal
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

set_option maxHeartbeats 800000 in
theorem durfee_square_normalization :
    letI : UniformSpace ℚ := ⊥
    letI : DiscreteUniformity ℚ := ⟨rfl⟩
    HasSum (fun size : ℕ => (PowerSeries.X : PowerSeries ℚ) ^ (size ^ 2) *
      (PowerSeries.invOfUnit (eulerDenominator size) 1) ^ 2)
        (PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1) := by
  classical
  let : UniformSpace ℚ := ⊥
  let : DiscreteUniformity ℚ := ⟨rfl⟩
  have missing (diagram : YoungDiagram) : ∃ index, (index, index) ∉ diagram := by
    obtain ⟨index, hindex⟩ := diagram.exists_notMem_row 0
    exact ⟨index, fun hcell => hindex (diagram.up_left_mem (Nat.zero_le _) le_rfl hcell)⟩
  let side (diagram : YoungDiagram) := Nat.find (missing diagram)
  have diagonal (diagram : YoungDiagram) (index : ℕ) :
      (index, index) ∈ diagram ↔ index < side diagram := by
    constructor
    · intro hcell
      by_contra hlarge
      have hle : side diagram ≤ index := by omega
      exact Nat.find_spec (missing diagram) (diagram.up_left_mem hle hle hcell)
    · intro hsmall
      exact not_not.mp (Nat.find_min (missing diagram) hsmall)
  let rightCells (diagram : YoungDiagram) :=
    (diagram.cells.filter fun cell => side diagram ≤ cell.2).image
      (fun cell => (cell.1, cell.2 - side diagram))
  let bottomCells (diagram : YoungDiagram) :=
    (diagram.cells.filter fun cell => side diagram ≤ cell.1).image
      (fun cell => (cell.1 - side diagram, cell.2))
  have rightMem (diagram : YoungDiagram) (row column : ℕ) :
      (row, column) ∈ rightCells diagram ↔ (row, column + side diagram) ∈ diagram := by
    simp only [rightCells, Finset.mem_image, Finset.mem_filter, YoungDiagram.mem_cells]
    constructor
    · rintro ⟨⟨earlierRow, earlierColumn⟩, ⟨hcell, hcolumn⟩, hequal⟩
      simp only [Prod.mk.injEq] at hequal
      have hrow : earlierRow = row := hequal.1
      have hcol : earlierColumn = column + side diagram := by omega
      simpa only [hrow, hcol] using hcell
    · intro hcell
      exact ⟨(row, column + side diagram), ⟨hcell, by omega⟩, by simp⟩
  have bottomMem (diagram : YoungDiagram) (row column : ℕ) :
      (row, column) ∈ bottomCells diagram ↔ (row + side diagram, column) ∈ diagram := by
    simp only [bottomCells, Finset.mem_image, Finset.mem_filter, YoungDiagram.mem_cells]
    constructor
    · rintro ⟨⟨earlierRow, earlierColumn⟩, ⟨hcell, hrow⟩, hequal⟩
      simp only [Prod.mk.injEq] at hequal
      have hr : earlierRow = row + side diagram := by omega
      simpa only [hr, hequal.2] using hcell
    · intro hcell
      exact ⟨(row + side diagram, column), ⟨hcell, by omega⟩, by simp⟩
  let rightPiece (diagram : YoungDiagram) : YoungDiagram :=
    { cells := rightCells diagram
      isLowerSet := by
        rintro ⟨lastRow, lastColumn⟩ ⟨firstRow, firstColumn⟩ hle hcell
        apply (rightMem diagram firstRow firstColumn).mpr
        exact diagram.up_left_mem hle.1 (Nat.add_le_add_right hle.2 _)
          ((rightMem diagram lastRow lastColumn).mp hcell) }
  let bottomPiece (diagram : YoungDiagram) : YoungDiagram :=
    { cells := bottomCells diagram
      isLowerSet := by
        rintro ⟨lastRow, lastColumn⟩ ⟨firstRow, firstColumn⟩ hle hcell
        apply (bottomMem diagram firstRow firstColumn).mpr
        exact diagram.up_left_mem (Nat.add_le_add_right hle.1 _) hle.2
          ((bottomMem diagram lastRow lastColumn).mp hcell) }
  have rightBound (diagram : YoungDiagram) :
      ∀ cell ∈ rightPiece diagram, cell.1 < side diagram := by
    rintro ⟨row, column⟩ hcell
    have hsource := (rightMem diagram row column).mp hcell
    by_contra hlarge
    have hdiagonal := diagram.up_left_mem (by omega : side diagram ≤ row)
      (by omega : side diagram ≤ column + side diagram) hsource
    exact (Nat.lt_irrefl _) ((diagonal diagram _).mp hdiagonal)
  have bottomBound (diagram : YoungDiagram) :
      ∀ cell ∈ bottomPiece diagram, cell.2 < side diagram := by
    rintro ⟨row, column⟩ hcell
    have hsource := (bottomMem diagram row column).mp hcell
    by_contra hlarge
    have hdiagonal := diagram.up_left_mem (by omega : side diagram ≤ row + side diagram)
      (by omega : side diagram ≤ column) hsource
    exact (Nat.lt_irrefl _) ((diagonal diagram _).mp hdiagonal)
  let pieces := Σ size : ℕ, {pair : YoungDiagram × YoungDiagram //
    (∀ cell ∈ pair.1, cell.1 < size) ∧ (∀ cell ∈ pair.2, cell.2 < size)}
  let cut (diagram : YoungDiagram) : pieces :=
    ⟨side diagram, ⟨(rightPiece diagram, bottomPiece diagram),
      rightBound diagram, bottomBound diagram⟩⟩
  let gluedCells (size : ℕ) (upper lower : YoungDiagram) :=
    (Finset.range size ×ˢ Finset.range size) ∪
      upper.cells.image (fun cell => (cell.1, cell.2 + size)) ∪
        lower.cells.image (fun cell => (cell.1 + size, cell.2))
  have gluedMem (size : ℕ) (upper lower : YoungDiagram) (row column : ℕ) :
      (row, column) ∈ gluedCells size upper lower ↔
        (row < size ∧ column < size) ∨
          (size ≤ column ∧ (row, column - size) ∈ upper) ∨
            (size ≤ row ∧ (row - size, column) ∈ lower) := by
    simp only [gluedCells, Finset.mem_union, Finset.mem_product, Finset.mem_range,
      Finset.mem_image, YoungDiagram.mem_cells]
    constructor
    · rintro ((hsquare | ⟨⟨earlierRow, earlierColumn⟩, hcell, hequal⟩) |
        ⟨⟨earlierRow, earlierColumn⟩, hcell, hequal⟩)
      · exact Or.inl hsquare
      · simp only [Prod.mk.injEq] at hequal
        right; left
        refine ⟨by omega, ?_⟩
        have hrow : row = earlierRow := hequal.1.symm
        have hcolumn : column - size = earlierColumn := by omega
        simpa only [hrow, hcolumn] using hcell
      · simp only [Prod.mk.injEq] at hequal
        right; right
        refine ⟨by omega, ?_⟩
        have hrow : row - size = earlierRow := by omega
        simpa only [hrow, hequal.2.symm] using hcell
    · rintro (hsquare | ⟨hcolumn, hcell⟩ | ⟨hrow, hcell⟩)
      · exact Or.inl (Or.inl hsquare)
      · left; right
        exact ⟨(row, column - size), hcell, by simp [Nat.sub_add_cancel hcolumn]⟩
      · right
        exact ⟨(row - size, column), hcell, by simp [Nat.sub_add_cancel hrow]⟩
  let glue (data : pieces) : YoungDiagram :=
    { cells := gluedCells data.1 data.2.val.1 data.2.val.2
      isLowerSet := by
        rintro ⟨lastRow, lastColumn⟩ ⟨firstRow, firstColumn⟩ hle hcell
        apply (gluedMem _ _ _ _ _).mpr
        rcases (gluedMem _ _ _ _ _).mp hcell with hsquare | ⟨hcolumn, hupper⟩ |
          ⟨hrow, hlower⟩
        · left
          exact ⟨lt_of_le_of_lt hle.1 hsquare.1, lt_of_le_of_lt hle.2 hsquare.2⟩
        · have hheight := data.2.property.1 _ hupper
          by_cases hfirst : firstColumn < data.1
          · left
            exact ⟨lt_of_le_of_lt hle.1 hheight, hfirst⟩
          · right; left
            exact ⟨by omega, data.2.val.1.up_left_mem hle.1
              (Nat.sub_le_sub_right hle.2 _) hupper⟩
        · have hwidth := data.2.property.2 _ hlower
          by_cases hfirst : firstRow < data.1
          · left
            exact ⟨hfirst, lt_of_le_of_lt hle.2 hwidth⟩
          · right; right
            exact ⟨by omega, data.2.val.2.up_left_mem
              (Nat.sub_le_sub_right hle.1 _) hle.2 hlower⟩ }
  have glueSide (data : pieces) : side (glue data) = data.1 := by
    have hdiagonal (index : ℕ) : (index, index) ∈ glue data ↔ index < data.1 := by
      change (index, index) ∈ gluedCells _ _ _ ↔ _
      rw [gluedMem]
      constructor
      · rintro (hsquare | ⟨_, hupper⟩ | ⟨_, hlower⟩)
        · exact hsquare.1
        · exact data.2.property.1 _ hupper
        · exact data.2.property.2 _ hlower
      · intro hsmall
        exact Or.inl ⟨hsmall, hsmall⟩
    apply Nat.le_antisymm
    · by_contra hlarge
      have hcell := (diagonal (glue data) data.1).mpr (by omega)
      exact Nat.lt_irrefl _ ((hdiagonal _).mp hcell)
    · by_contra hsmall
      have hcell := (hdiagonal (side (glue data))).mpr (by omega)
      exact Nat.lt_irrefl _ ((diagonal _ _).mp hcell)
  have uncut (diagram : YoungDiagram) : glue (cut diagram) = diagram := by
    apply YoungDiagram.ext
    apply Finset.ext
    rintro ⟨row, column⟩
    change (row, column) ∈ gluedCells _ _ _ ↔ (row, column) ∈ diagram
    rw [gluedMem]
    change (row < side diagram ∧ column < side diagram) ∨
      (side diagram ≤ column ∧ (row, column - side diagram) ∈ rightCells diagram) ∨
      (side diagram ≤ row ∧ (row - side diagram, column) ∈ bottomCells diagram) ↔ _
    rw [rightMem, bottomMem]
    constructor
    · rintro (hsquare | ⟨hcolumn, hcell⟩ | ⟨hrow, hcell⟩)
      · have hcell := (diagonal diagram (max row column)).mpr (by omega)
        exact diagram.up_left_mem (le_max_left _ _) (le_max_right _ _) hcell
      · simpa only [Nat.sub_add_cancel hcolumn] using hcell
      · simpa only [Nat.sub_add_cancel hrow] using hcell
    · intro hcell
      by_cases hcolumn : side diagram ≤ column
      · right; left
        exact ⟨hcolumn, by simpa only [Nat.sub_add_cancel hcolumn] using hcell⟩
      · by_cases hrow : side diagram ≤ row
        · right; right
          exact ⟨hrow, by simpa only [Nat.sub_add_cancel hrow] using hcell⟩
        · left
          exact ⟨by omega, by omega⟩
  have recut (data : pieces) : cut (glue data) = data := by
    have hsize := glueSide data
    have hright : rightPiece (glue data) = data.2.val.1 := by
      apply YoungDiagram.ext
      apply Finset.ext
      rintro ⟨row, column⟩
      change (row, column) ∈ rightCells (glue data) ↔ _
      rw [rightMem, hsize]
      change (row, column + data.1) ∈ gluedCells _ _ _ ↔ _
      rw [gluedMem]
      simp only [Nat.add_sub_cancel, Nat.le_add_left]
      constructor
      · rintro (hsquare | ⟨_, hcell⟩ | ⟨_, hcell⟩)
        · omega
        · exact hcell
        · have hwidth := data.2.property.2 _ hcell
          omega
      · exact fun hcell => Or.inr (Or.inl ⟨True.intro, hcell⟩)
    have hbottom : bottomPiece (glue data) = data.2.val.2 := by
      apply YoungDiagram.ext
      apply Finset.ext
      rintro ⟨row, column⟩
      change (row, column) ∈ bottomCells (glue data) ↔ _
      rw [bottomMem, hsize]
      change (row + data.1, column) ∈ gluedCells _ _ _ ↔ _
      rw [gluedMem]
      simp only [Nat.add_sub_cancel, Nat.le_add_left]
      constructor
      · rintro (hsquare | ⟨_, hcell⟩ | ⟨_, hcell⟩)
        · omega
        · have hheight := data.2.property.1 _ hcell
          omega
        · exact hcell
      · exact fun hcell => Or.inr (Or.inr ⟨True.intro, hcell⟩)
    apply Sigma.ext hsize
    apply (Subtype.heq_iff_coe_eq (by intro pair; dsimp only [cut]; rw [hsize])).mpr
    exact Prod.ext hright hbottom
  let decomposition : YoungDiagram ≃ pieces :=
    { toFun := cut
      invFun := glue
      left_inv := uncut
      right_inv := recut }
  have area (data : pieces) : (glue data).card =
      data.1 ^ 2 + data.2.val.1.card + data.2.val.2.card := by
    let square := Finset.range data.1 ×ˢ Finset.range data.1
    let upper := data.2.val.1.cells.image (fun cell => (cell.1, cell.2 + data.1))
    let lower := data.2.val.2.cells.image (fun cell => (cell.1 + data.1, cell.2))
    have hsquareUpper : Disjoint square upper := by
      apply Finset.disjoint_left.mpr
      rintro ⟨row, column⟩ hsquare hupper
      obtain ⟨⟨oldRow, oldColumn⟩, _, hequal⟩ := Finset.mem_image.mp hupper
      have hcolumn : column < data.1 := (Finset.mem_product.mp hsquare).2 |> Finset.mem_range.mp
      simp only [Prod.mk.injEq] at hequal
      omega
    have hsquareLower : Disjoint square lower := by
      apply Finset.disjoint_left.mpr
      rintro ⟨row, column⟩ hsquare hlower
      obtain ⟨⟨oldRow, oldColumn⟩, _, hequal⟩ := Finset.mem_image.mp hlower
      have hrow : row < data.1 := (Finset.mem_product.mp hsquare).1 |> Finset.mem_range.mp
      simp only [Prod.mk.injEq] at hequal
      omega
    have hupperLower : Disjoint upper lower := by
      apply Finset.disjoint_left.mpr
      rintro ⟨row, column⟩ hupper hlower
      obtain ⟨⟨upperRow, upperColumn⟩, hcell, hequal⟩ := Finset.mem_image.mp hupper
      obtain ⟨⟨lowerRow, lowerColumn⟩, _, hlowerEqual⟩ := Finset.mem_image.mp hlower
      have hheight := data.2.property.1 _ hcell
      simp only [Prod.mk.injEq] at hequal hlowerEqual
      omega
    have hupperCard : upper.card = data.2.val.1.card := by
      apply Finset.card_image_of_injective
      rintro ⟨firstRow, firstColumn⟩ ⟨lastRow, lastColumn⟩ hequal
      simp only [Prod.mk.injEq] at hequal ⊢
      omega
    have hlowerCard : lower.card = data.2.val.2.card := by
      apply Finset.card_image_of_injective
      rintro ⟨firstRow, firstColumn⟩ ⟨lastRow, lastColumn⟩ hequal
      simp only [Prod.mk.injEq] at hequal ⊢
      omega
    change ((square ∪ upper) ∪ lower).card = _
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨hsquareLower, hupperLower⟩), Finset.card_union_of_disjoint hsquareUpper,
      hupperCard, hlowerCard]
    simp only [square, Finset.card_product, Finset.card_range, pow_two]
  have preservesArea (diagram : YoungDiagram) : diagram.card =
      (decomposition diagram).1 ^ 2 + (decomposition diagram).2.val.1.card +
        (decomposition diagram).2.val.2.card := by
    simpa only [decomposition, Equiv.coe_fn_mk, uncut] using area (cut diagram)
  have cellBound (diagram : YoungDiagram) (cell : ℕ × ℕ) (hcell : cell ∈ diagram) :
      cell.1 < diagram.card ∧ cell.2 < diagram.card := by
    constructor
    · apply lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp hcell)
      rw [YoungDiagram.colLen_eq_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    · apply lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp hcell)
      rw [YoungDiagram.rowLen_eq_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)
  have finiteAtMost (bound : ℕ) : ({diagram : YoungDiagram |
      diagram.card ≤ bound} : Set YoungDiagram).Finite := by
    apply Set.Finite.of_injOn (t :=
      ((Finset.range bound ×ˢ Finset.range bound).powerset : Set (Finset (ℕ × ℕ))))
      (f := YoungDiagram.cells) _ _ (Finset.finite_toSet _)
    · intro diagram hdiagram
      apply Finset.mem_powerset.mpr
      intro cell hcell
      have hbound := cellBound diagram cell hcell
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le hbound.1 hdiagram),
        Finset.mem_range.mpr (lt_of_lt_of_le hbound.2 hdiagram)⟩
    · exact fun first _ second _ hequal => YoungDiagram.ext hequal
  let total (degree : ℕ) : Set YoungDiagram := {diagram | diagram.card = degree}
  let bounded (size degree : ℕ) : Set YoungDiagram :=
    {diagram | (∀ cell ∈ diagram, cell.2 < size) ∧ diagram.card = degree}
  let allSeries : PowerSeries ℚ := PowerSeries.mk fun degree => ((total degree).ncard : ℚ)
  let boundedSeries (size : ℕ) : PowerSeries ℚ :=
    PowerSeries.mk fun degree => ((bounded size degree).ncard : ℚ)
  have finiteTotal (degree : ℕ) : (total degree).Finite :=
    (finiteAtMost degree).subset (fun _ hdiagram => le_of_eq hdiagram)
  have finiteBounded (size degree : ℕ) : (bounded size degree).Finite :=
    (finiteTotal degree).subset (fun _ hdiagram => hdiagram.2)
  have rowArea (diagram : YoungDiagram) : diagram.rowLens.sum = diagram.card := by
    rw [YoungDiagram.rowLens, ← List.sum_toFinset _ List.nodup_range]
    rw [List.toFinset_range]
    simp_rw [diagram.rowLen_eq_card]
    symm
    apply Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    intro cell hcell
    apply Finset.mem_range.mpr
    apply YoungDiagram.mem_iff_lt_colLen.mp
    exact diagram.up_left_mem le_rfl (Nat.zero_le _) hcell
  have rowBound (diagram : YoungDiagram) (size : ℕ) :
      (∀ cell ∈ diagram, cell.2 < size) ↔ ∀ part ∈ diagram.rowLens, part ≤ size := by
    constructor
    · intro hbound part hpart
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hpart
      have hpositive : 0 < diagram.rowLen row :=
        diagram.pos_of_mem_rowLens _ (List.mem_map.mpr ⟨row, hrow, rfl⟩)
      have hcell : (row, diagram.rowLen row - 1) ∈ diagram :=
        YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have := hbound _ hcell
      omega
    · intro hbound cell hcell
      have hrow : cell.1 < diagram.colLen 0 :=
        YoungDiagram.mem_iff_lt_colLen.mp
          (diagram.up_left_mem le_rfl (Nat.zero_le _) hcell)
      have hpart : diagram.rowLen cell.1 ∈ diagram.rowLens :=
        List.mem_map.mpr ⟨cell.1, List.mem_range.mpr hrow, rfl⟩
      exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp hcell) (hbound _ hpart)
  have boundedCard (size degree : ℕ) : (bounded size degree).ncard =
      (Nat.Partition.restricted degree (fun part => part ≤ size)).card := by
    let encode (diagram : bounded size degree) :
        ↥(Nat.Partition.restricted degree (fun part => part ≤ size)) :=
      ⟨⟨diagram.val.rowLens, fun h => diagram.val.pos_of_mem_rowLens _ h,
          (rowArea diagram.val).trans diagram.property.2⟩, by
        simpa only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ,
          true_and, Multiset.mem_coe] using (rowBound diagram.val size).mp diagram.property.1⟩
    have hinjective : Function.Injective encode := by
      intro first second hequal
      have hparts := congrArg (fun p => p.val.parts) hequal
      have hperm : first.val.rowLens.Perm second.val.rowLens :=
        Quotient.exact hparts
      have hrows := hperm.eq_of_pairwise' first.val.rowLens_sorted.pairwise
        second.val.rowLens_sorted.pairwise
      apply Subtype.ext
      apply YoungDiagram.equivListRowLens.injective
      exact Subtype.ext hrows
    have hsurjective : Function.Surjective encode := by
      intro partition
      let rows := partition.val.parts.sort (· ≥ ·)
      have hsorted : rows.SortedGE := (Multiset.pairwise_sort _ _).sortedGE
      have hpos : ∀ part ∈ rows, 0 < part := by
        intro part hpart
        exact partition.val.parts_pos ((Multiset.mem_sort _).mp hpart)
      let diagram := YoungDiagram.ofRowLens rows hsorted
      have hrows : diagram.rowLens = rows := YoungDiagram.rowLens_ofRowLens_eq_self hpos
      have hparts : (diagram.rowLens : Multiset ℕ) = partition.val.parts := by
        rw [hrows, Multiset.sort_eq]
      have harea : diagram.card = degree := by
        rw [← rowArea, ← Multiset.sum_coe, hparts, partition.val.parts_sum]
      have hbound : ∀ cell ∈ diagram, cell.2 < size := by
        apply (rowBound diagram size).mpr
        intro part hpart
        have hrestricted := (Finset.mem_filter.mp partition.property).2
        exact hrestricted part (by simpa only [← hparts, Multiset.mem_coe] using hpart)
      refine ⟨⟨diagram, hbound, harea⟩, ?_⟩
      apply Subtype.ext
      exact Nat.Partition.ext hparts
    let equivalence := Equiv.ofBijective encode ⟨hinjective, hsurjective⟩
    let : Fintype (bounded size degree) := (finiteBounded size degree).fintype
    simpa only [Set.fintypeCard_eq_ncard, Fintype.card_coe] using
      Fintype.card_congr equivalence
  have boundedNormalization (size : ℕ) : boundedSeries size * eulerDenominator size = 1 := by
    let factor (index : ℕ) : PowerSeries ℚ :=
      if index + 1 ≤ size then ∑' j : ℕ, PowerSeries.X ^ ((index + 1) * j) else 1
    have hformula : HasProd factor (boundedSeries size) := by
      have h := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℚ (fun part => part ≤ size)
      simpa only [factor, boundedSeries, boundedCard] using h
    have hfinite : HasProd factor (∏ index ∈ Finset.range size, factor index) := by
      apply hasProd_prod_of_ne_finset_one
      intro index houtside
      simp only [factor]
      rw [if_neg (by
        simp only [Finset.mem_range] at houtside
        omega)]
    rw [hformula.unique hfinite]
    unfold eulerDenominator
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro index hindex
    have hsmall : index + 1 ≤ size := by simpa using hindex
    simp only [factor, if_pos hsmall]
    simp_rw [pow_mul]
    apply PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
    simp
  have boundedInverse (size : ℕ) : boundedSeries size =
      PowerSeries.invOfUnit (eulerDenominator size) 1 := by
    have hnormalize := boundedNormalization size
    change boundedSeries size * eulerDenominator size = 1 at hnormalize
    have hconstant : PowerSeries.constantCoeff (eulerDenominator size) = 1 := by
      simp [eulerDenominator]
    calc
      boundedSeries size = boundedSeries size *
          (eulerDenominator size * PowerSeries.invOfUnit (eulerDenominator size) 1) := by
            rw [PowerSeries.mul_invOfUnit _ _ hconstant, mul_one]
      _ = PowerSeries.invOfUnit (eulerDenominator size) 1 := by
        rw [← mul_assoc, hnormalize, one_mul]
  have boundedLimit : Filter.Tendsto boundedSeries Filter.atTop (nhds allSeries) := by
    apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℚ _ _ _).mpr
    intro degree
    apply tendsto_nhds_of_eventually_eq
    apply Filter.eventually_atTop.mpr
    refine ⟨degree + 1, fun size hsize => ?_⟩
    have hequal : bounded size degree = total degree := by
      ext diagram
      constructor
      · exact fun hdiagram => hdiagram.2
      · intro hdiagram
        refine ⟨fun cell hcell => ?_, hdiagram⟩
        have hbound := (cellBound diagram cell hcell).2
        change diagram.card = degree at hdiagram
        omega
    simp only [boundedSeries, allSeries, PowerSeries.coeff_mk, hequal]
  have denominatorLimit : Filter.Tendsto eulerDenominator Filter.atTop
      (nhds (PowerSeries.pentagonalSeries ℚ)) :=
    (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℚ).tendsto_prod_nat
  have normalized : allSeries * PowerSeries.pentagonalSeries ℚ = 1 := by
    apply tendsto_nhds_unique (boundedLimit.mul denominatorLimit)
    have hconstant : (fun size => boundedSeries size * eulerDenominator size) =
        fun _ : ℕ => (1 : PowerSeries ℚ) := by
      funext size
      exact boundedNormalization size
    rw [hconstant]
    exact tendsto_const_nhds
  have allInverse : allSeries = PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 := by
    have hconstant : PowerSeries.constantCoeff (PowerSeries.pentagonalSeries ℚ) = 1 := by
      have hcoeff := PowerSeries.coeff_pentagonalSeries_pentagonal ℚ 0
      rw [show pentagonal (0 : ℤ) = 0 from rfl,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, Int.negOnePow_zero]
        at hcoeff
      simpa only [Units.val_one, Int.cast_one] using hcoeff
    calc
      allSeries = allSeries * (PowerSeries.pentagonalSeries ℚ *
          PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1) := by
            rw [PowerSeries.mul_invOfUnit _ _ hconstant, mul_one]
      _ = PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 := by
        rw [← mul_assoc, normalized, one_mul]
  have transposeArea (diagram : YoungDiagram) : diagram.transpose.card = diagram.card := by
    simp [YoungDiagram.transpose, YoungDiagram.card]
  let residuals (size degree : ℕ) : Set (YoungDiagram × YoungDiagram) :=
    {pair | (∀ cell ∈ pair.1, cell.2 < size) ∧ (∀ cell ∈ pair.2, cell.2 < size) ∧
      size ^ 2 + pair.1.card + pair.2.card = degree}
  have finiteResiduals (size degree : ℕ) : (residuals size degree).Finite := by
    apply ((finiteAtMost degree).prod (finiteAtMost degree)).subset
    intro pair hpair
    have harea := hpair.2.2
    change pair.1.card ≤ degree ∧ pair.2.card ≤ degree
    exact ⟨by omega, by omega⟩
  have residualCard (size degree : ℕ) : (residuals size degree).ncard =
      if size ^ 2 ≤ degree then
        ∑ pair ∈ antidiagonal (degree - size ^ 2),
          (bounded size pair.1).ncard * (bounded size pair.2).ncard else 0 := by
    by_cases hsize : size ^ 2 ≤ degree
    · rw [if_pos hsize]
      let target := Σ pair : ↥(antidiagonal (degree - size ^ 2)),
        bounded size pair.val.1 × bounded size pair.val.2
      let splitResidual (pair : residuals size degree) : target :=
        ⟨⟨(pair.val.1.card, pair.val.2.card), mem_antidiagonal.mpr (by
          have harea := pair.property.2.2
          omega)⟩,
          (⟨pair.val.1, ⟨pair.property.1, rfl⟩⟩,
            ⟨pair.val.2, ⟨pair.property.2.1, rfl⟩⟩)⟩
      let joinResidual (data : target) : residuals size degree :=
        ⟨(data.2.1.val, data.2.2.val), data.2.1.property.1, data.2.2.property.1, by
          have harea := mem_antidiagonal.mp data.1.property
          rw [data.2.1.property.2, data.2.2.property.2]
          omega⟩
      let equivalence : residuals size degree ≃ target :=
        { toFun := splitResidual
          invFun := joinResidual
          left_inv := fun _ => rfl
          right_inv := by
            rintro ⟨⟨⟨firstArea, secondArea⟩, harea⟩,
              ⟨first, hfirstBound, hfirstArea⟩, ⟨second, hsecondBound, hsecondArea⟩⟩
            change first.card = firstArea at hfirstArea
            change second.card = secondArea at hsecondArea
            subst firstArea secondArea
            rfl }
      let : Fintype (residuals size degree) := (finiteResiduals size degree).fintype
      let : ∀ pair : ↥(antidiagonal (degree - size ^ 2)),
          Fintype (bounded size pair.val.1 × bounded size pair.val.2) := fun pair =>
        let := (finiteBounded size pair.val.1).fintype
        let := (finiteBounded size pair.val.2).fintype
        inferInstance
      have hcard := Fintype.card_congr equivalence
      dsimp only [target] at hcard
      simp only [Fintype.card_sigma, Fintype.card_prod, Set.fintypeCard_eq_ncard] at hcard
      rw [Finset.univ_eq_attach] at hcard
      exact hcard.trans (Finset.sum_attach _
        (fun pair : ℕ × ℕ => (bounded size pair.1).ncard * (bounded size pair.2).ncard))
    · rw [if_neg hsize]
      have hempty : residuals size degree = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro pair hpair
        have harea := hpair.2.2
        omega
      rw [hempty, Set.ncard_empty]
  have totalCard (degree : ℕ) : (total degree).ncard =
      ∑ size ∈ Finset.range (degree + 1), (residuals size degree).ncard := by
    let splitDiagram (diagram : total degree) :
        Σ size : Fin (degree + 1), residuals size.val degree :=
      let data := decomposition diagram.val
      ⟨⟨data.1, by
        have harea := preservesArea diagram.val
        rw [diagram.property] at harea
        nlinarith [sq_nonneg ((data.1 : ℤ) - 1)]⟩,
        ⟨(data.2.val.1.transpose, data.2.val.2),
          (fun cell hcell => data.2.property.1 cell.swap
            (YoungDiagram.mem_transpose.mp hcell)), data.2.property.2, by
              rw [transposeArea]
              exact (preservesArea diagram.val).symm.trans diagram.property⟩⟩
    let joinDiagram (data : Σ size : Fin (degree + 1), residuals size.val degree) :
        total degree :=
      ⟨decomposition.symm ⟨data.1.val, (data.2.val.1.transpose, data.2.val.2),
          (fun cell hcell => data.2.property.1 cell.swap
            (YoungDiagram.mem_transpose.mp hcell)), data.2.property.2.1⟩, by
        have harea := preservesArea (decomposition.symm
          ⟨data.1.val, (data.2.val.1.transpose, data.2.val.2),
            (fun cell hcell => data.2.property.1 cell.swap
              (YoungDiagram.mem_transpose.mp hcell)), data.2.property.2.1⟩)
        rw [Equiv.apply_symm_apply, transposeArea] at harea
        exact harea.trans data.2.property.2.2⟩
    let equivalence : total degree ≃
        Σ size : Fin (degree + 1), residuals size.val degree :=
      { toFun := splitDiagram
        invFun := joinDiagram
        left_inv := by
          intro diagram
          apply Subtype.ext
          dsimp only [joinDiagram, splitDiagram]
          simp only [YoungDiagram.transpose_transpose]
          apply Eq.trans ?_ (decomposition.symm_apply_apply diagram.val)
          apply congrArg decomposition.symm
          apply Sigma.ext rfl
          apply heq_of_eq
          apply Subtype.ext
          rfl
        right_inv := by
          rintro ⟨size, pair⟩
          let data : pieces := ⟨size.val, (pair.val.1.transpose, pair.val.2),
            (fun cell hcell => pair.property.1 cell.swap
              (YoungDiagram.mem_transpose.mp hcell)), pair.property.2.1⟩
          have hdata : decomposition (joinDiagram ⟨size, pair⟩).val = data :=
            decomposition.apply_symm_apply data
          have hside : (splitDiagram (joinDiagram ⟨size, pair⟩)).fst = size := by
            apply Fin.ext
            exact congrArg Sigma.fst hdata
          apply Sigma.ext hside
          apply (Subtype.heq_iff_coe_eq (by
            intro values
            change (values ∈ residuals
              (splitDiagram (joinDiagram ⟨size, pair⟩)).fst.val degree) ↔
                (values ∈ residuals size.val degree)
            rw [congrArg Fin.val hside])).mpr
          change (((decomposition (joinDiagram ⟨size, pair⟩).val).snd.val.1).transpose,
            (decomposition (joinDiagram ⟨size, pair⟩).val).snd.val.2) = pair.val
          rw [hdata]
          simp only [data, YoungDiagram.transpose_transpose] }
    let : Fintype (total degree) := (finiteTotal degree).fintype
    let : ∀ size : Fin (degree + 1), Fintype (residuals size.val degree) :=
      fun size => (finiteResiduals size.val degree).fintype
    have hcard := Fintype.card_congr equivalence
    simp only [Fintype.card_sigma, Set.fintypeCard_eq_ncard] at hcard
    exact hcard.trans (Fin.sum_univ_eq_sum_range
      (fun size => (residuals size degree).ncard) (degree + 1))
  have coefficient (size degree : ℕ) : PowerSeries.coeff degree
      (PowerSeries.X ^ (size ^ 2) * (PowerSeries.invOfUnit (eulerDenominator size) 1) ^ 2) =
        ((residuals size degree).ncard : ℚ) := by
    rw [← boundedInverse,
      show (boundedSeries size) ^ 2 = boundedSeries size * boundedSeries size from pow_two _,
      PowerSeries.coeff_X_pow_mul', residualCard]
    split_ifs
    · simp only [PowerSeries.coeff_mul, boundedSeries, PowerSeries.coeff_mk,
        Nat.cast_sum, Nat.cast_mul]
    · simp only [Nat.cast_zero]
  rw [← allInverse]
  apply (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ).mpr
  intro degree
  simp only [allSeries, PowerSeries.coeff_mk]
  have hsum : HasSum (fun size : ℕ => PowerSeries.coeff degree
      (PowerSeries.X ^ (size ^ 2) * (PowerSeries.invOfUnit (eulerDenominator size) 1) ^ 2))
      (∑ size ∈ Finset.range (degree + 1), PowerSeries.coeff degree
        (PowerSeries.X ^ (size ^ 2) * (PowerSeries.invOfUnit (eulerDenominator size) 1) ^ 2)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro size houtside
    rw [coefficient, residualCard]
    have hsize : degree < size := by
      simp only [Finset.mem_range, not_lt] at houtside
      omega
    rw [if_neg (by nlinarith : ¬size ^ 2 ≤ degree), Nat.cast_zero]
  have hcard := totalCard degree
  have hsumValue : (∑ size ∈ Finset.range (degree + 1), PowerSeries.coeff degree
      (PowerSeries.X ^ (size ^ 2) * (PowerSeries.invOfUnit (eulerDenominator size) 1) ^ 2)) =
        ((total degree).ncard : ℚ) := by
    simp only [coefficient, ← Nat.cast_sum]
    exact_mod_cast hcard.symm
  exact hsumValue ▸ hsum

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Durfee
