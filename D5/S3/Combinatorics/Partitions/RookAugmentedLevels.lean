/- GID: D5/S3/Combinatorics/Partitions/RookAugmentedLevels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/RookAugmentedLevels
   mirror-E: none(waiver:native-augmented-level-product)
   anchors: []
   utility: none
   digest: Actual Ferrers levels with auxiliary full columns have the level-total product count. -/

import D5.S3.Combinatorics.Partitions.RookLevelSelection
import Mathlib.Data.Fintype.CardEmbedding
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots

/-! A native combinatorial side of the level-total factorization. Auxiliary
    columns are distinguished from the original columns by a disjoint sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.RookAugmentedLevels

open D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
open D5.S3.Combinatorics.Partitions.RookLevelSelection
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Original source columns and t new full columns are disjoint. -/
abbrev Columns (b : PositiveColumns) (t : ℕ) := Fin b.val.length ⊕ Fin t

/-- Level p is counted from the top of N levels. An original cell retains its
    source column and within-level row; auxiliary columns contain all m rows. -/
def level (m N t : ℕ) (b : PositiveColumns) (p : Fin N) :
    Finset (Columns b t × Fin m) := by
  classical
  exact Finset.univ.filter fun x => Sum.elim
    (fun i : Fin b.val.length => m*(N-1-p.val)+x.2.val < b.val[i.val])
    (fun _ : Fin t => True) x.1

private theorem levels_nested (m N t : ℕ) (b : PositiveColumns) :
    NestedFull m (level m N t b) := by
  classical
  intro i j hij x hx r
  rcases x with ⟨c,s⟩
  cases c with
  | inr c => simp [level]
  | inl c =>
    have hx' : m*(N-1-i.val)+s.val < b.val[c.val] := by simpa [level] using hx
    have hq : N-1-j.val+1 ≤ N-1-i.val := by
      have hi := i.isLt
      have hj := j.isLt
      have hij' : i.val < j.val := hij
      omega
    have hmul := Nat.mul_le_mul_left m hq
    rw [Nat.mul_add, Nat.mul_one] at hmul
    have hr := r.isLt
    simp only [level, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inl]
    simp only [Nat.sub_sub] at hx' hmul ⊢
    omega

private theorem level_card (m N t : ℕ) (b : PositiveColumns) (p : Fin N) :
    (level m N t b p).card = columnLevel m b (N-1-p.val) + m*t := by
  classical
  unfold level columnLevel
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ↓reduceIte]
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [Finset.sum_comm]
  simp [Nat.mul_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h <;> simp [h]

/-- Count actual full placements on the augmented board by its level totals.
    This holds for arbitrary normalized original boards, with no singleton
    hypothesis. It is the product side of the native factorization route. -/
theorem augmented_selections_count (m N t : ℕ) (b : PositiveColumns) :
    Fintype.card (Selections m (level m N t b)) =
      ∏ i : Fin N, (columnLevel m b (N-1-i.val) + m*t - m*i.val) := by
  rw [selections_count m N _ (levels_nested m N t b)]
  exact Finset.prod_congr rfl (fun i _ => by rw [level_card])

/-- Original choices indexed by their actual top-down levels. Empty entries
    are exactly the levels to be completed by auxiliary columns. -/
abbrev Partial (m N : ℕ) (b : PositiveColumns) :=
  {f : Fin N → Option (Fin b.val.length × Fin m) //
    (∀ i x, f i = some x → m*(N-1-i.val)+x.2.val < b.val[x.1.val]) ∧
    (∀ i j x y, f i = some x → f j = some y → x.1 = y.1 → i = j)}

/-- Unoccupied levels of an original partial placement. -/
abbrev Vacant {m N : ℕ} {b : PositiveColumns} (p : Partial m N b) :=
  {i : Fin N // p.val i = none}

private def originalPart (m N t : ℕ) (b : PositiveColumns)
    (f : Selections m (level m N t b)) : Partial m N b :=
  ⟨fun i => match (f.val i).1 with
    | Sum.inl c => some (c, (f.val i).2)
    | Sum.inr _ => none, by
      constructor
      · intro i x hx
        have hi := f.property.1 i
        cases h : (f.val i).1 with
        | inl c =>
          simp only [h] at hx
          cases hx
          simpa [level, h] using hi
        | inr c => simp [h] at hx
      · intro i j x y hx hy hxy
        have hi : (f.val i).1 = Sum.inl x.1 := by
          cases h : (f.val i).1 with
          | inl c =>
            simp only [h, Option.some.injEq] at hx
            exact congrArg Sum.inl (congrArg Prod.fst hx)
          | inr c => simp [h] at hx
        have hj : (f.val j).1 = Sum.inl y.1 := by
          cases h : (f.val j).1 with
          | inl c =>
            simp only [h, Option.some.injEq] at hy
            exact congrArg Sum.inl (congrArg Prod.fst hy)
          | inr c => simp [h] at hy
        exact f.property.2 (hi.trans ((congrArg Sum.inl hxy).trans hj.symm))⟩

private def complete (m N t : ℕ) (b : PositiveColumns) (p : Partial m N b)
    (e : Vacant p ↪ Fin t) (r : Vacant p → Fin m) :
    Selections m (level m N t b) := by
  classical
  exact ⟨fun i => if h : p.val i = none then (Sum.inr (e ⟨i,h⟩), r ⟨i,h⟩)
    else let x := (p.val i).get (Option.isSome_iff_ne_none.mpr h)
         (Sum.inl x.1, x.2), by
      constructor
      · intro i
        dsimp only
        split_ifs with h
        · simp [level]
        · have hx := Option.some_get (Option.isSome_iff_ne_none.mpr h)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.property.1 i _ hx.symm⟩
      · intro i j hij
        dsimp only at hij
        by_cases hi : p.val i = none <;> by_cases hj : p.val j = none
        · simp only [hi, hj, ↓reduceDIte, Prod.fst, Sum.inr.injEq] at hij
          exact congrArg Subtype.val (e.injective hij)
        · simp [hi, hj] at hij
        · simp [hi, hj] at hij
        · simp only [hi, hj, ↓reduceDIte, Prod.fst, Sum.inl.injEq] at hij
          exact p.property.2 i j _ _
            (Option.some_get (Option.isSome_iff_ne_none.mpr hi)).symm
            (Option.some_get (Option.isSome_iff_ne_none.mpr hj)).symm hij⟩

private theorem originalPart_complete (m N t : ℕ) (b : PositiveColumns)
    (p : Partial m N b) (e : Vacant p ↪ Fin t) (r : Vacant p → Fin m) :
    originalPart m N t b (complete m N t b p e r) = p := by
  apply Subtype.ext
  funext i
  simp only [originalPart, complete]
  split_ifs with h
  · exact h.symm
  · exact Option.some_get (Option.isSome_iff_ne_none.mpr h)

/-- A reversible split into actual original level choices, distinct auxiliary
    columns on the vacant levels, and independent within-level rows. -/
def completionEquiv (m N t : ℕ) (b : PositiveColumns) :
    ((p : Partial m N b) × ((Vacant p ↪ Fin t) × (Vacant p → Fin m))) ≃
      Selections m (level m N t b) := by
  classical
  apply Equiv.ofBijective (fun z => complete m N t b z.1 z.2.1 z.2.2)
  constructor
  · rintro ⟨p,e,r⟩ ⟨q,e',r'⟩ h
    have hp : p = q := by
      simpa only [originalPart_complete] using congrArg (originalPart m N t b) h
    subst q
    have he : e = e' := by
      apply DFunLike.ext
      intro i
      have hh := congrArg (fun f : Selections m (level m N t b) => (f.val i.val).1) h
      simpa [complete, i.property] using hh
    have hr : r = r' := by
      funext i
      have hh := congrArg (fun f : Selections m (level m N t b) => (f.val i.val).2) h
      simpa [complete, i.property] using hh
    subst e'
    subst r'
    rfl
  · intro f
    let p := originalPart m N t b f
    have aux (i : Vacant p) : ∃ c, (f.val i.val).1 = Sum.inr c := by
      have hi := i.property
      dsimp only [p, originalPart] at hi
      cases h : (f.val i.val).1 with
      | inl c => simp [h] at hi
      | inr c => exact ⟨c,rfl⟩
    let e : Vacant p ↪ Fin t :=
      ⟨fun i => (aux i).choose, by
        intro i j hij
        apply Subtype.ext
        apply f.property.2
        exact (aux i).choose_spec.trans ((congrArg Sum.inr hij).trans (aux j).choose_spec.symm)⟩
    let r : Vacant p → Fin m := fun i => (f.val i.val).2
    refine ⟨⟨p,e,r⟩, ?_⟩
    apply Subtype.ext
    funext i
    dsimp only [complete]
    split_ifs with hi
    · apply Prod.ext
      · exact (aux ⟨i,hi⟩).choose_spec.symm
      · rfl
    · cases h : (f.val i).1 with
      | inl c =>
        have hp : p.val i = some (c, (f.val i).2) := by simp [p, originalPart, h]
        apply Prod.ext
        · simpa only [hp, Option.get_some] using h.symm
        · simp only [hp, Option.get_some]
      | inr c =>
        have hp : p.val i = none := by simp [p, originalPart, h]
        exact (hi hp).elim

/-- Count completions of every original partial placement, with no lower bound
    on the number of auxiliary columns and no positivity assumption on m. -/
private theorem partial_completion_count (m N t : ℕ) (b : PositiveColumns) :
    Fintype.card (Selections m (level m N t b)) =
      ∑ p : Partial m N b,
        m ^ Fintype.card (Vacant p) * Nat.descFactorial t (Fintype.card (Vacant p)) := by
  classical
  rw [← Fintype.card_congr (completionEquiv m N t b), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  simp [Fintype.card_fun, Nat.mul_comm]

open D5.S3.Combinatorics.Partitions.RookClassNative
open private column_cell columns_row_bound from D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
open private cell_bound cells_card from D5.S3.Combinatorics.Partitions.RookClassNative

/-- Coordinates in the genuine Young-diagram carrier, including the required
    horizontal reflection of the source column index. -/
def nativeCoord (m N : ℕ) (b : PositiveColumns)
    (z : Fin N × (Fin b.val.length × Fin m)) : ℕ × ℕ :=
  (m*(N-1-z.1.val)+z.2.2.val, z.2.1.rev.val)

private theorem coord_div (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (z : Fin N × (Fin b.val.length × Fin m)) :
    (nativeCoord m N b z).1 / m = N-1-z.1.val := by
  simp [nativeCoord, Nat.mul_add_div hm, Nat.div_eq_of_lt z.2.2.isLt]

private theorem coord_injective (m N : ℕ) (hm : 0 < m) (b : PositiveColumns) :
    Function.Injective (nativeCoord m N b) := by
  intro z w h
  have hd := congrArg (fun x : ℕ × ℕ => x.1 / m) h
  rw [coord_div m N hm b, coord_div m N hm b] at hd
  have hi : z.1 = w.1 := by
    apply Fin.ext
    have hz := z.1.isLt
    have hw := w.1.isLt
    omega
  have hc : z.2.1 = w.2.1 := by
    apply Fin.rev_injective
    exact Fin.ext (congrArg Prod.snd h)
  have hr : z.2.2 = w.2.2 := by
    apply Fin.ext
    have hh := congrArg Prod.fst h
    dsimp only [nativeCoord] at hh
    rw [hi] at hh
    omega
  exact Prod.ext hi (Prod.ext hc hr)

private theorem coord_mem (m N : ℕ) (b : PositiveColumns)
    (z : Fin N × (Fin b.val.length × Fin m)) :
    nativeCoord m N b z ∈ cells b ↔
      m*(N-1-z.1.val)+z.2.2.val < b.val[z.2.1.val] := by
  exact (YoungDiagram.mem_iff_lt_rowLen).trans (column_cell b _ z.2.1).symm

private theorem coord_onto (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) (x : ℕ × ℕ) (hx : x ∈ cells b) :
    ∃ z : Fin N × (Fin b.val.length × Fin m), nativeCoord m N b z = x := by
  have hb := cell_bound b x hx
  have hl : x.1 / m < N := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hc : x.2 < b.val.length := lt_of_lt_of_le
    (YoungDiagram.mem_iff_lt_rowLen.mp hx) (columns_row_bound b x.1)
  let i : Fin N := (⟨x.1/m,hl⟩ : Fin N).rev
  let c : Fin b.val.length := (⟨x.2,hc⟩ : Fin b.val.length).rev
  let r : Fin m := ⟨x.1 % m,Nat.mod_lt _ hm⟩
  refine ⟨(i,c,r), ?_⟩
  apply Prod.ext
  · have hi : N-1-i.val = x.1/m := by
      have h := congrArg Fin.val (Fin.rev_rev (⟨x.1/m,hl⟩ : Fin N))
      simpa only [i, Fin.val_rev, Nat.sub_sub, Nat.add_comm] using h
    dsimp only [nativeCoord]
    rw [hi]
    exact Nat.div_add_mod _ _
  · simp [nativeCoord, c]

private def nativeSet (m N : ℕ) (b : PositiveColumns) (p : Partial m N b) :
    Finset (ℕ × ℕ) := by
  classical
  exact (Finset.univ.filter fun z : Fin N × (Fin b.val.length × Fin m) =>
    p.val z.1 = some z.2).image (nativeCoord m N b)

private theorem mem_nativeSet (m N : ℕ) (b : PositiveColumns) (p : Partial m N b)
    (x : ℕ × ℕ) : x ∈ nativeSet m N b p ↔
      ∃ z, p.val z.1 = some z.2 ∧ nativeCoord m N b z = x := by
  classical
  simp [nativeSet]

private theorem coord_mem_nativeSet (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (p : Partial m N b) (z : Fin N × (Fin b.val.length × Fin m)) :
    nativeCoord m N b z ∈ nativeSet m N b p ↔ p.val z.1 = some z.2 := by
  rw [mem_nativeSet]
  constructor
  · rintro ⟨w,hw,he⟩
    exact coord_injective m N hm b he ▸ hw
  · intro h
    exact ⟨z,h,rfl⟩

/-- All genuine nonattacking subsets, before stratification by their size. -/
abbrev NativePlacements (m : ℕ) (b : PositiveColumns) :=
  ↥((cells b).powerset.filter (Nonattacking m))

private theorem nativeSet_valid (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (p : Partial m N b) : nativeSet m N b p ∈
      (cells b).powerset.filter (Nonattacking m) := by
  classical
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_powerset.mpr
    intro x hx
    obtain ⟨z,hz,rfl⟩ := (mem_nativeSet m N b p x).mp hx
    exact (coord_mem m N b z).mpr (p.property.1 z.1 z.2 hz)
  · intro x hx y hy hxy
    obtain ⟨z,hz,rfl⟩ := (mem_nativeSet m N b p x).mp hx
    obtain ⟨w,hw,rfl⟩ := (mem_nativeSet m N b p y).mp hy
    constructor
    · intro hc
      have hcol : z.2.1 = w.2.1 := Fin.rev_injective (Fin.ext hc)
      have hi := p.property.2 z.1 w.1 z.2 w.2 hz hw hcol
      have hrow : z.2 = w.2 := Option.some.inj ((hz.symm.trans (congrArg p.val hi)).trans hw)
      exact hxy (congrArg (nativeCoord m N b) (Prod.ext hi hrow))
    · intro hl
      rw [coord_div m N hm b, coord_div m N hm b] at hl
      have hi : z.1 = w.1 := by
        apply Fin.ext
        have hz := z.1.isLt
        have hw := w.1.isLt
        omega
      have hrow : z.2 = w.2 := Option.some.inj ((hz.symm.trans (congrArg p.val hi)).trans hw)
      exact hxy (congrArg (nativeCoord m N b) (Prod.ext hi hrow))

private theorem native_unique_level (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (p : NativePlacements m b) (i : Fin N) (x y : Fin b.val.length × Fin m)
    (hx : nativeCoord m N b (i,x) ∈ p.val)
    (hy : nativeCoord m N b (i,y) ∈ p.val) : x = y := by
  have hn := (Finset.mem_filter.mp p.property).2
  by_cases he : nativeCoord m N b (i,x) = nativeCoord m N b (i,y)
  · exact congrArg Prod.snd (coord_injective m N hm b he)
  · exact ((hn hx hy he).2 (by rw [coord_div m N hm b, coord_div m N hm b])).elim

private def ofNative (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (p : NativePlacements m b) : Partial m N b := by
  classical
  let f := fun i : Fin N => if h : ∃ x, nativeCoord m N b (i,x) ∈ p.val
    then some h.choose else none
  refine ⟨f, ?_, ?_⟩
  · intro i x hx
    dsimp only [f] at hx
    split_ifs at hx with h
    · have he := Option.some.inj hx
      have hp : nativeCoord m N b (i,x) ∈ p.val := he ▸ h.choose_spec
      exact (coord_mem m N b (i,x)).mp
        ((Finset.mem_powerset.mp (Finset.mem_filter.mp p.property).1) hp)
  · intro i j x y hx hy hcol
    have mem (i : Fin N) (x : Fin b.val.length × Fin m) (hx : f i = some x) :
        nativeCoord m N b (i,x) ∈ p.val := by
      dsimp only [f] at hx
      split_ifs at hx with h
      · exact Option.some.inj hx ▸ h.choose_spec
    have hn := (Finset.mem_filter.mp p.property).2
    by_cases he : nativeCoord m N b (i,x) = nativeCoord m N b (j,y)
    · exact congrArg Prod.fst (coord_injective m N hm b he)
    · exact ((hn (mem i x hx) (mem j y hy) he).1
        (by simp only [nativeCoord, hcol])).elim

private theorem ofNative_spec (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (p : NativePlacements m b) (i : Fin N) (x : Fin b.val.length × Fin m) :
    (ofNative m N hm b p).val i = some x ↔ nativeCoord m N b (i,x) ∈ p.val := by
  classical
  dsimp only [ofNative]
  split_ifs with h
  · constructor
    · intro he
      exact Option.some.inj he ▸ h.choose_spec
    · intro hx
      exact congrArg some (native_unique_level m N hm b p i _ _ h.choose_spec hx)
  · constructor
    · intro he
      contradiction
    · intro hx
      exact (h ⟨x,hx⟩).elim

/-- Exact transport to native subsets, with both row division/remainder and
    reflected columns. No singleton hypothesis occurs. -/
def nativePartialEquiv (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) : Partial m N b ≃ NativePlacements m b where
  toFun p := ⟨nativeSet m N b p,nativeSet_valid m N hm b p⟩
  invFun := ofNative m N hm b
  left_inv p := by
    apply Subtype.ext
    funext i
    apply Option.ext
    intro x
    rw [ofNative_spec, coord_mem_nativeSet m N hm b]
  right_inv p := by
    apply Subtype.ext
    apply Finset.ext
    intro x
    rw [mem_nativeSet]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (ofNative_spec m N hm b p z.1 z.2).mp hz
    · intro hx
      have hb := (Finset.mem_powerset.mp (Finset.mem_filter.mp p.property).1) hx
      obtain ⟨z,rfl⟩ := coord_onto m N hm b hN x hb
      exact ⟨z,(ofNative_spec m N hm b p z.1 z.2).mpr hx,rfl⟩

private theorem nativeSet_card (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (p : Partial m N b) :
    (nativeSet m N b p).card = Fintype.card {i : Fin N // p.val i ≠ none} := by
  classical
  let f : {i : Fin N // p.val i ≠ none} → ↥(nativeSet m N b p) := fun i =>
    ⟨nativeCoord m N b (i.val,(p.val i.val).get (Option.isSome_iff_ne_none.mpr i.property)),
      (coord_mem_nativeSet m N hm b p _).mpr
        (Option.some_get (Option.isSome_iff_ne_none.mpr i.property)).symm⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      apply Subtype.ext
      exact congrArg Prod.fst (coord_injective m N hm b (congrArg Subtype.val h))
    · intro x
      obtain ⟨z,hz,he⟩ := (mem_nativeSet m N b p x.val).mp x.property
      have hn : p.val z.1 ≠ none := by rw [hz]; simp
      refine ⟨⟨z.1,hn⟩, ?_⟩
      apply Subtype.ext
      dsimp only [f]
      simpa only [hz, Option.get_some] using he
  simpa only [Fintype.card_coe] using (Fintype.card_congr (Equiv.ofBijective f hf)).symm

private theorem vacant_card (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (p : Partial m N b) : Fintype.card (Vacant p) = N-(nativeSet m N b p).card := by
  classical
  rw [nativeSet_card m N hm b]
  simpa only [not_not, Fintype.card_fin] using
    Fintype.card_subtype_compl (fun i : Fin N => p.val i ≠ none)

private def placementSizeEquiv (m N : ℕ) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) :
    NativePlacements m b ≃ ((k : Fin (N+1)) × ↥(placements m b k.val)) where
  toFun p := ⟨⟨p.val.card, by
    have hc := Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp p.property).1)
    have harea := cells_card b
    omega⟩, ⟨p.val, by
      classical
      exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp p.property).1,rfl⟩,
        (Finset.mem_filter.mp p.property).2⟩⟩⟩
  invFun z := ⟨z.2.val, by
    classical
    obtain ⟨hp,hn⟩ := Finset.mem_filter.mp z.2.property
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hp).1,hn⟩⟩
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨k,hk⟩,⟨p,hp⟩⟩
    have he : p.card = k := (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hp).1).2
    subst k
    rfl

/-- The native completion bridge counts the same augmented selections by
    original nonattacking cell subsets and auxiliary completions. -/
theorem native_completion_count (m N t : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) :
    Fintype.card (Selections m (level m N t b)) =
      ∑ k ∈ Finset.range (N+1),
        rookCount m b k * m^(N-k) * Nat.descFactorial t (N-k) := by
  classical
  rw [partial_completion_count]
  simp_rw [vacant_card m N hm b]
  let g : NativePlacements m b → ℕ := fun p =>
    m^(N-p.val.card) * Nat.descFactorial t (N-p.val.card)
  have h₁ : (∑ p : Partial m N b, g (nativePartialEquiv m N hm b hN p)) =
      ∑ p : NativePlacements m b, g p :=
    Equiv.sum_comp (nativePartialEquiv m N hm b hN) g
  change (∑ p : Partial m N b, g (nativePartialEquiv m N hm b hN p)) = _
  rw [h₁]
  let e := placementSizeEquiv m N b hN
  rw [← Equiv.sum_comp e.symm g, Fintype.sum_sigma]
  change (∑ k : Fin (N+1), ∑ p : ↥(placements m b k.val),
    m^(N-p.val.card) * Nat.descFactorial t (N-p.val.card)) = _
  have hc (k : Fin (N+1)) (p : ↥(placements m b k.val)) : p.val.card = k.val :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp p.property).1).2
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  simp only [← Nat.mul_assoc]
  change (∑ k : Fin (N+1), rookCount m b k.val * m^(N-k.val) *
    Nat.descFactorial t (N-k.val)) = _
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    rookCount m b k * m^(N-k) * Nat.descFactorial t (N-k)) (N+1)

/-- The native rook polynomial in the auxiliary-column variable. -/
def rookPolynomial (m N : ℕ) (b : PositiveColumns) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (N+1),
    Polynomial.C ((rookCount m b k : ℤ) * (m : ℤ)^(N-k)) *
      descPochhammer ℤ (N-k)

/-- The level-total product on the same variable and the same original board. -/
def levelPolynomial (m N : ℕ) (b : PositiveColumns) : Polynomial ℤ :=
  ∏ i : Fin N, (Polynomial.C (columnLevel m b (N-1-i.val) : ℤ) +
    Polynomial.C (m : ℤ) * Polynomial.X - Polynomial.C ((m : ℤ) * (i.val : ℤ)))

private theorem eval_rookPolynomial (m N t : ℕ) (b : PositiveColumns) :
    (rookPolynomial m N b).eval (t : ℤ) =
      ((∑ k ∈ Finset.range (N+1),
        rookCount m b k * m^(N-k) * Nat.descFactorial t (N-k) : ℕ) : ℤ) := by
  simp only [rookPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, mul_assoc]

private theorem eval_levelPolynomial (m N t : ℕ) (b : PositiveColumns) (ht : N ≤ t) :
    (levelPolynomial m N b).eval (t : ℤ) =
      ((∏ i : Fin N, (columnLevel m b (N-1-i.val) + m*t - m*i.val) : ℕ) : ℤ) := by
  simp only [levelPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
    Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  have hi : m*i.val ≤ columnLevel m b (N-1-i.val) + m*t :=
    (Nat.mul_le_mul_left m (le_trans (Nat.le_of_lt i.isLt) ht)).trans (Nat.le_add_left _ _)
  rw [Nat.cast_sub hi, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]

/-- Same-board factorization follows from the two counts of literal augmented
    selections and polynomial equality on infinitely many large integers. -/
theorem native_factorization (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) : rookPolynomial m N b = levelPolynomial m N b := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => ((N+n : ℕ) : ℤ)) := by
    intro i j h
    exact Nat.add_left_cancel (Int.ofNat_inj.mp h)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n,rfl⟩
  rw [Set.mem_ofPred_eq, eval_rookPolynomial,
    eval_levelPolynomial m N (N+n) b (by omega)]
  congr 1
  exact (native_completion_count m N (N+n) hm b hN).symm.trans
    (augmented_selections_count m N (N+n) b)

end D5.S3.Combinatorics.Partitions.RookAugmentedLevels

