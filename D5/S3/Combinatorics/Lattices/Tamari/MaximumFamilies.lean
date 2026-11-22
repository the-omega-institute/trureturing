/- GID: D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Lattices/Tamari/MaximumFamilies
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Maximum Boolean antichains carry the next smaller Tamari order. -/

/-
admission_basis: escape-witness (registered maximum attainment and induced order)
Direct frozen dependencies: none.
proof_shape: maximumTamari_card: content; escape_witness: booleanFamily_maximum
proof_shape: orderIso_atomCard: bind-only; consumers: no_tamari_noncrossing_iso, tamari_atom_card_le
proof_shape: tamari_atom_card_le: content; escape_witness: atom_is_increment
proof_shape: tamari_two_coatoms: content; escape_witness: tamari_two_coatoms
-/

import D5.S3.Combinatorics.Lattices.Tamari.BooleanRows
import D5.S3.Combinatorics.Lattices.Tamari.TreeRotations
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.Atoms

/-! # The order of maximum Boolean antichains -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Lattices.Tamari

open scoped BinaryTree

noncomputable section

/-- Families with the extremal cardinality, ordered below by their generated lower sets. -/
@[ext] structure MaximumFamilies (α : Type*) [CompleteLattice α] (n : ℕ) where
  carrier : Set α
  boolean : IsBooleanFamily carrier
  card : carrier.ncard = n

variable {α β : Type*}

instance maximumFamiliesOrder [CompleteLattice α] (n : ℕ) : PartialOrder (MaximumFamilies α n) :=
  PartialOrder.lift (fun C => lowerClosure C.carrier) (by
    intro C D h
    change lowerClosure C.carrier = lowerClosure D.carrier at h
    ext x
    rw [← C.boolean.1.maximal_mem_lowerClosure_iff_mem, h,
      D.boolean.1.maximal_mem_lowerClosure_iff_mem])

private abbrev LeftArrays (n : ℕ) := {A : (s : RowIndex n) → LeftEndpoint s // Laminar A}

private def appendRows {n : ℕ} (A : LeftArrays n) : MaximumFamilies (Brackets n) n :=
  ⟨Set.range (rowFamily A.val),
    (boolean_rowFamily_iff_laminar A.val).2 A.property, rowFamily_ncard A.val⟩

/-- Lower-set inclusion becomes the pointwise order on the left endpoints. -/
private def rowFamilyOrderIso (n : ℕ) : LeftArrays n ≃o MaximumFamilies (Brackets n) n where
  toEquiv := Equiv.ofBijective appendRows (by
    constructor
    · intro A B h
      apply le_antisymm
      · exact (lowerClosure_rowFamily_le_iff _ _).mp (show appendRows A ≤ appendRows B from h.le)
      · exact (lowerClosure_rowFamily_le_iff _ _).mp (show appendRows B ≤ appendRows A from h.ge)
    · intro C
      obtain ⟨A, hA, hC⟩ :=
        (maximum_boolean_iff_laminar_rows C.carrier).mp ⟨C.boolean, C.card⟩
      exact ⟨⟨A, hA⟩, MaximumFamilies.ext hC.symm⟩)
  map_rel_iff' := lowerClosure_rowFamily_le_iff _ _

variable {n : ℕ}

/-- Reflection from the one-based left coordinate to the zero-based right coordinate. -/
private def reflectedIndex (n : ℕ) : RowIndex n ≃ Fin n where
  toFun s := ⟨n - s.val, by have := s.property; omega⟩
  invFun i := ⟨n - i.val, by have := i.isLt; omega, Nat.sub_le _ _⟩
  left_inv s := Subtype.ext (by change n - (n - s.val) = s.val; have := s.property; omega)
  right_inv i := Fin.ext (by change n - (n - i.val) = i.val; have := i.isLt; omega)

private theorem reflected_le {s t : RowIndex n} :
    reflectedIndex n s ≤ reflectedIndex n t ↔ t.val ≤ s.val := by
  change n - s.val ≤ n - t.val ↔ _
  have := s.property
  have := t.property
  omega

private theorem reflected_lt {s t : RowIndex n} :
    reflectedIndex n s < reflectedIndex n t ↔ t.val < s.val := by
  simp only [lt_iff_not_ge, reflected_le]

private def leftAt (A : LeftArrays n) (s : RowIndex n) : RowIndex n :=
  ⟨(A.val s).val, (A.val s).property.1, (A.val s).property.2.trans s.property.2⟩

private def reflectArray (A : LeftArrays n) : BracketingFunctions n :=
  ⟨fun i => reflectedIndex n (leftAt A ((reflectedIndex n).symm i)), by
    let e := reflectedIndex n
    change (∀ i, i ≤ e (leftAt A (e.symm i))) ∧
      (∀ i j, i ≤ j → j ≤ e (leftAt A (e.symm i)) →
        e (leftAt A (e.symm j)) ≤ e (leftAt A (e.symm i)))
    constructor
    · intro i
      conv_lhs => rw [← e.apply_symm_apply i]
      exact reflected_le.mpr (A.val (e.symm i)).property.2
    · intro i j hij hj
      by_cases he : i = j
      · subst j
        exact le_rfl
      have hlt := lt_of_le_of_ne hij he
      have hst : (e.symm j).val < (e.symm i).val := by
        apply reflected_lt.mp
        change e (e.symm i) < e (e.symm j)
        simpa only [e.apply_symm_apply] using hlt
      have hreach : (leftAt A (e.symm i)).val ≤ (e.symm j).val := by
        apply reflected_le.mp
        change e (e.symm j) ≤ e (leftAt A (e.symm i))
        simpa only [e.apply_symm_apply] using hj
      exact reflected_le.mpr (A.property _ _ hst hreach)⟩

private def unreflectArray (b : BracketingFunctions n) : LeftArrays n :=
  ⟨fun s => ⟨((reflectedIndex n).symm (b.val (reflectedIndex n s))).val,
    ((reflectedIndex n).symm (b.val (reflectedIndex n s))).property.1, by
      let e := reflectedIndex n
      exact reflected_le.mp (show e s ≤ e (e.symm (b.val (e s))) by
        rw [e.apply_symm_apply]; exact b.property.1 _)⟩, by
    intro s t hst ht
    let e := reflectedIndex n
    change (e.symm (b.val (e t))).val ≤ s.val at ht
    change (e.symm (b.val (e t))).val ≤ (e.symm (b.val (e s))).val
    apply reflected_le.mp
    change e (e.symm (b.val (e s))) ≤ e (e.symm (b.val (e t)))
    simp only [e.apply_symm_apply]
    apply b.property.2 _ _ (reflected_le.mpr hst.le)
    have h : e s ≤ e (e.symm (b.val (e t))) := reflected_le.mpr ht
    rwa [e.apply_symm_apply] at h⟩

/-- Reflecting the intervals reverses comparison. -/
private def leftArrayReflect (n : ℕ) : LeftArrays n ≃o (BracketingFunctions n)ᵒᵈ where
  toEquiv :=
    { toFun := reflectArray
      invFun := unreflectArray
      left_inv := fun A => Subtype.ext (funext fun s => Subtype.ext (by
        let e := reflectedIndex n
        change (e.symm (e (leftAt A (e.symm (e s))))).val = (A.val s).val
        simp only [e.symm_apply_apply]
        rfl))
      right_inv := fun b => Subtype.ext (funext fun i => by
        let e := reflectedIndex n
        have h : leftAt (unreflectArray b) (e.symm i) = e.symm (b.val (e (e.symm i))) := rfl
        change e (leftAt (unreflectArray b) (e.symm i)) = b.val i
        rw [h, e.apply_symm_apply, e.apply_symm_apply]) }
  map_rel_iff' := by
    intro A B
    let e := reflectedIndex n
    change (∀ i, e (leftAt B (e.symm i)) ≤ e (leftAt A (e.symm i))) ↔
      ∀ s, (A.val s).val ≤ (B.val s).val
    constructor
    · intro h s
      have h' := reflected_le.mp (h (e s))
      rw [e.symm_apply_apply] at h'
      exact h' 
    · intro h i
      exact reflected_le.mpr (h (e.symm i))

private def mirror : FullTree → FullTree
  | .nil => .nil
  | .node _ l r => mirror r △ mirror l

@[simp] private theorem mirror_size (t : FullTree) : (mirror t).numNodes = t.numNodes := by
  induction t using BinaryTree.unitRecOn <;> simp [mirror, *, Nat.add_comm]

@[simp] private theorem mirror_mirror (t : FullTree) : mirror (mirror t) = t := by
  induction t using BinaryTree.unitRecOn <;> simp [mirror, *]

private theorem rotation_mirror {t u : FullTree} (h : RightRotation t u) :
    RightRotation (mirror u) (mirror t) := by
  induction h with
  | root a b c => exact .root (mirror c) (mirror b) (mirror a)
  | left r _ ih => exact ih.right (mirror r)
  | right l _ ih => exact ih.left (mirror l)

private theorem reach_mirror {t u : FullTree} (h : RotationReach t u) :
    RotationReach (mirror u) (mirror t) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact (Relation.ReflTransGen.single (rotation_mirror h)).trans ih

/-- Mirroring reverses contextual right rotation order. -/
private def mirrorOrderIso (n : ℕ) : (Trees n)ᵒᵈ ≃o Trees n where
  toEquiv :=
    { toFun := fun t => ⟨mirror t.val, (mirror_size _).trans t.property⟩
      invFun := fun t => ⟨mirror t.val, (mirror_size _).trans t.property⟩
      left_inv := fun t => Subtype.ext (mirror_mirror _)
      right_inv := fun t => Subtype.ext (mirror_mirror _) }
  map_rel_iff' := by
    intro t u
    change RotationReach (mirror t.val) (mirror u.val) ↔ RotationReach u.val t.val
    exact ⟨fun h => by simpa only [mirror_mirror] using reach_mirror h, reach_mirror⟩

private def bracketMaximumTamari (n : ℕ) : MaximumFamilies (Brackets n) n ≃o Trees n :=
  (rowFamilyOrderIso n).symm.trans
    ((leftArrayReflect n).trans ((treeBracketOrderIso n).symm.dual.trans (mirrorOrderIso n)))

/-- Transport the lattice to the contextual right-rotation order itself. -/
instance tamariCompleteLattice (n : ℕ) : CompleteLattice (Trees (n + 1)) := by
  let e := treeBracketOrderIso (n + 1)
  letI : InfSet (Trees (n + 1)) := ⟨fun C => e.symm (sInf (e '' C))⟩
  apply completeLatticeOfInf
  intro C
  refine ⟨?_, ?_⟩
  · intro z hz
    change e.symm (sInf (e '' C)) ≤ z
    exact e.symm_apply_le.mpr (sInf_le (Set.mem_image_of_mem _ hz))
  · intro z hz
    change z ≤ e.symm (sInf (e '' C))
    apply e.le_symm_apply.mpr
    apply le_sInf
    rintro _ ⟨w, hw, rfl⟩
    exact e.monotone (hz hw)

private theorem boolean_image [CompleteLattice α] [CompleteLattice β]
    (e : α ≃o β) {C : Set α} (h : IsBooleanFamily C) : IsBooleanFamily (e '' C) := by
  refine ⟨h.1.image e (fun {_ _} h' => e.le_iff_le.mp h'), ?_, ?_⟩
  · rintro ⟨x, hx, hx'⟩
    exact h.2.1 ((e.injective (hx'.trans (map_top e).symm)) ▸ hx)
  · intro S T hS hT
    have hs : e ⁻¹' S ⊆ C := fun x hx =>
      (Set.preimage_image_eq C e.injective) ▸ hS hx
    have ht : e ⁻¹' T ⊆ C := fun x hx =>
      (Set.preimage_image_eq C e.injective) ▸ hT hx
    have heq := congrArg e (h.2.2 _ _ hs ht)
    simpa only [map_sup, map_sInf, ← Set.preimage_inter, Set.image_preimage_eq _ e.surjective]
      using heq

private def mapFamily [CompleteLattice α] [CompleteLattice β]
    (e : α ≃o β) {n : ℕ} (C : MaximumFamilies α n) : MaximumFamilies β n :=
  ⟨e '' C.carrier, boolean_image e C.boolean,
    (Set.ncard_image_of_injective _ e.injective).trans C.card⟩

private def maximumFamiliesCongr [CompleteLattice α] [CompleteLattice β]
    (e : α ≃o β) (n : ℕ) : MaximumFamilies α n ≃o MaximumFamilies β n where
  toEquiv :=
    { toFun := mapFamily e
      invFun := mapFamily e.symm
      left_inv := fun C => MaximumFamilies.ext (e.left_inv.image_image C.carrier)
      right_inv := fun C => MaximumFamilies.ext (e.right_inv.image_image C.carrier) }
  map_rel_iff' := by
    intro C D
    change lowerClosure (e '' C.carrier) ≤ lowerClosure (e '' D.carrier) ↔
      lowerClosure C.carrier ≤ lowerClosure D.carrier
    simp only [lowerClosure_le]
    constructor
    · intro h x hx
      obtain ⟨_, ⟨y, hy, rfl⟩, he⟩ := mem_lowerClosure.mp (h (Set.mem_image_of_mem e hx))
      exact mem_lowerClosure.mpr ⟨y, hy, e.le_iff_le.mp he⟩
    · rintro h _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, he⟩ := mem_lowerClosure.mp (h hx)
      exact mem_lowerClosure.mpr ⟨e y, Set.mem_image_of_mem e hy, e.monotone he⟩

/-- Maximum Boolean antichains of the source Tamari lattice of rank `n + 1`,
ordered by inclusion of their generated ideals, form exactly the Tamari order at `n`. -/
def maximumTamariOrderIso (n : ℕ) : MaximumFamilies (Trees (n + 1)) n ≃o Trees n :=
  (maximumFamiliesCongr (treeBracketOrderIso (n + 1)) n).trans (bracketMaximumTamari n)

theorem maximumTamari_card (n : ℕ) :
    IsGreatest {k : ℕ | ∃ C : Set (Trees (n + 1)), IsBooleanFamily C ∧ C.ncard = k} n := by
  have h := booleanFamily_maximum n
  let e := treeBracketOrderIso (n + 1)
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, hcard⟩ := h.1
    exact ⟨e.symm '' C, boolean_image e.symm hC,
      (Set.ncard_image_of_injective _ e.symm.injective).trans hcard⟩
  · rintro k ⟨C, hC, hcard⟩
    exact h.2 ⟨e '' C, boolean_image e hC, (Set.ncard_image_of_injective _ e.injective).trans hcard⟩

end

end D5.S3.Combinatorics.Lattices.Tamari

/-! # Atoms and coatoms of the bracket order -/

namespace D5.S3.Combinatorics.Lattices.Tamari

noncomputable section

variable {n : ℕ}

private theorem bot_coord (i : Fin (n + 1)) : (⊥ : Brackets n).val i = i := by
  let b : Brackets n := ⟨id, ⟨fun _ => le_rfl, fun _ _ _ h => h⟩⟩
  exact le_antisymm ((bot_le : (⊥ : Brackets n) ≤ b) i) ((⊥ : Brackets n).property.1 i)

private def increment (i : Fin n) (j : Fin (n + 1)) : Fin (n + 1) :=
  if j = i.castSucc then i.succ else j

private def atomAt (i : Fin n) : Brackets n :=
  ⟨increment i, by
    constructor
    · intro j
      by_cases h : j = i.castSucc
      · subst j
        simp [increment, Fin.le_def]
      · simp [increment, h]
    · intro j k hj hk
      by_cases h : j = i.castSucc
      · subst j
        have hk' : k.val ≤ i.val + 1 := by simpa [increment, Fin.le_def] using hk
        have hj' : i.val ≤ k.val := hj
        have he : k = i.castSucc ∨ k = i.succ := by
          by_cases h : k.val = i.val
          · left; exact Fin.ext h
          · right; exact Fin.ext (by simp; omega)
        rcases he with rfl | rfl
        · exact le_rfl
        · simp [increment]
      · rw [show increment i j = j from ite_eq_right h] at hk ⊢
        rw [le_antisymm hk hj, show increment i j = j from ite_eq_right h]⟩

private theorem atomAt_ne_bot (i : Fin n) : atomAt i ≠ ⊥ := by
  intro h
  have hh := congrArg (fun b : Brackets n => b.val i.castSucc) h
  rw [bot_coord] at hh
  have hh' : i.succ = i.castSucc := by simpa [atomAt, increment] using hh
  have := congrArg Fin.val hh'
  simp at this

private theorem atom_is_increment {b : Brackets n} (hb : IsAtom b) :
    ∃ i : Fin n, atomAt i = b := by
  have hex : ∃ j : Fin (n + 1), j < b.val j := by
    by_contra! h
    apply hb.1
    exact Subtype.ext (funext fun j => by
      rw [bot_coord]
      exact le_antisymm (h j) (b.property.1 j))
  obtain ⟨j, hj⟩ := hex
  have hj' : j.val < n := hj.trans_le (Fin.le_last _)
  let i : Fin n := ⟨j.val, hj'⟩
  have hi : i.castSucc = j := Fin.ext rfl
  have hle : atomAt i ≤ b := by
    intro k
    change increment i k ≤ b.val k
    by_cases h : k = i.castSucc
    · subst k
      rw [increment, ite_eq_left rfl, hi]
      exact Nat.succ_le_of_lt hj
    · rw [increment, ite_eq_right h]
      exact b.property.1 k
  exact ⟨i, le_antisymm hle ((isAtom_iff_le_of_ge.mp hb).2 _ (atomAt_ne_bot _) hle)⟩

private theorem bracket_atom_card_le (n : ℕ) : Nat.card {b : Brackets n // IsAtom b} ≤ n := by
  let select (b : {b : Brackets n // IsAtom b}) : Fin n := (atom_is_increment b.property).choose
  have hs (b : {b : Brackets n // IsAtom b}) : atomAt (select b) = b.val :=
    (atom_is_increment b.property).choose_spec
  have hinj : Function.Injective select := fun b c h =>
    Subtype.ext ((hs b).symm.trans (h ▸ hs c))
  exact (Nat.card_le_card_of_injective select hinj).trans_eq (Nat.card_fin n)

theorem orderIso_atomCard {α β : Type*} [PartialOrder α] [PartialOrder β]
    [OrderBot α] [OrderBot β] (e : α ≃o β) :
    Nat.card {a : α // IsAtom a} = Nat.card {b : β // IsAtom b} :=
  Nat.card_congr
    { toFun := fun a => ⟨e a.val, (e.isAtom_iff _).2 a.property⟩
      invFun := fun b => ⟨e.symm b.val, (e.symm.isAtom_iff _).2 b.property⟩
      left_inv := fun a => Subtype.ext (e.symm_apply_apply a.val)
      right_inv := fun b => Subtype.ext (e.apply_symm_apply b.val) }

theorem tamari_atom_card_le (n : ℕ) : Nat.card {t : Trees (n + 1) // IsAtom t} ≤ n :=
  (orderIso_atomCard (treeBracketOrderIso (n + 1))).trans_le (bracket_atom_card_le n)

private def coatomAt (s : RowIndex n) : Brackets n :=
  row s ⟨s.val, s.property.1, le_rfl⟩

private theorem isCoatom_at (s : RowIndex n) : IsCoatom (coatomAt s) := by
  let i := ((rowIndexEquiv n).symm s).castSucc
  have his : i.val + 1 = s.val := Nat.sub_add_cancel s.property.1
  have hi : ((coatomAt s).val i).val + 1 = s.val := by
    unfold coatomAt
    rw [row_value_oneBased, his]
    exact ite_eq_left ⟨le_rfl, le_rfl⟩
  have htop {j : Fin (n + 1)} (hj : j ≠ i) : (coatomAt s).val j = Fin.last n := by
    apply Fin.ext
    have hval := row_value_oneBased s (⟨s.val, s.property.1, le_rfl⟩ : LeftEndpoint s) j
    have hneq : j.val + 1 ≠ s.val := fun h => hj (Fin.ext (by omega))
    rw [ite_eq_right (fun h => hneq (le_antisymm h.2 h.1))] at hval
    change ((coatomAt s).val j).val + 1 = n + 1 at hval
    exact Nat.succ.inj hval
  constructor
  · intro h
    rw [h, top_coord, Fin.val_last] at hi
    have := s.property.2
    omega
  · intro b hb
    have hle := hb.le
    have ho (j : Fin (n + 1)) (hj : j ≠ i) : b.val j = Fin.last n := by
      have hj' := hle j
      change (coatomAt s).val j ≤ b.val j at hj'
      rw [htop hj] at hj'
      exact le_antisymm (Fin.le_last _) hj'
    have hieq : (coatomAt s).val i = i := Fin.ext (by omega)
    have hi' : i < b.val i := by
      by_contra! hi'
      apply hb.ne
      apply Subtype.ext
      funext j
      by_cases hj : j = i
      · subst j
        rw [hieq, le_antisymm hi' (b.property.1 i)]
      · rw [htop hj, ho j hj]
    have hfix := b.property.2 i (b.val i) hi'.le le_rfl
    rw [ho (b.val i) hi'.ne'] at hfix
    apply Subtype.ext
    funext j
    rw [top_coord]
    by_cases hj : j = i
    · subst j
      exact le_antisymm (Fin.le_last _) hfix
    · exact ho j hj

theorem tamari_two_coatoms (n : ℕ) (hn : 2 ≤ n) :
    ∃ a b : Trees (n + 1), IsCoatom a ∧ IsCoatom b ∧ a ≠ b := by
  let s : RowIndex n := ⟨1, le_rfl, by omega⟩
  let t : RowIndex n := ⟨2, by omega, hn⟩
  let e := (treeBracketOrderIso (n + 1)).symm
  refine ⟨e (coatomAt s), e (coatomAt t),
    (e.isCoatom_iff _).2 (isCoatom_at _), (e.isCoatom_iff _).2 (isCoatom_at _), ?_⟩
  intro he
  have hh := e.injective he
  have hs := ((row_le_row_iff s t _ _).mp hh.le).1
  exact (by decide : (1 : ℕ) ≠ 2) (congrArg Subtype.val hs)

end

end D5.S3.Combinatorics.Lattices.Tamari
