/- GID: D5/S1/Recurrence/Invariants/PopovDirectUrnShift
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/PopovDirectUrnShift
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Powerset]
   utility: none
   digest: Chronological first-urn deletion and reinsertion give Popov’s shift identity. -/

import D5.S1.Recurrence.Invariants.PopovUrnNormalization
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Popov's first-urn shift

A chronological deletion and reinsertion proof of Problem 9.1 of
Vencislav Popov, arXiv:2608.12011v1.
-/

namespace PopovUrnShift

set_option autoImplicit false

/-! ## Chronological deletion and reinsertion -/

private theorem used_val (t : ℕ) : used (fun i : Fin t => i.val) = Finset.range t := by
  ext a
  simp only [mem_used, Finset.mem_range]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ i.isLt, fun h => ⟨⟨a,h⟩, rfl⟩⟩

/-- Before the first urn fills, the only legal ranks are the successive fresh ranks. -/
private theorem forced_word {m t : ℕ} (ht : t ≤ m) {x : Fin t → ℕ} (hx : Legal m x) :
    x = fun i => i.val := by
  induction t with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ t ih =>
    have hp := ih (Nat.le_of_succ_le ht) hx.1
    have hcard : (used (Fin.init x)).card = t := by rw [hp, used_val, Finset.card_range]
    have hl := hx.2
    rw [hcard] at hl
    have he : x (Fin.last t) = t := by
      simpa [Move, threshold, Nat.div_eq_of_lt (show t < m by omega)] using hl
    exact funext (Fin.lastCases he (fun i => congrFun hp i))

theorem forced_prefix {m n : ℕ} {x : Fin (m+n) → ℕ} (hx : Legal m x) (i : Fin m) :
    x (i.castAdd n) = i.val :=
  congrFun (forced_word (le_refl m) (legal_prefix hx (Nat.le_add_right m n))) i

/-- The increasing enumeration of selected tail positions. -/
def selectedOrder {n : ℕ} (J : Finset (Fin n)) : Fin J.card ≃o J :=
  J.orderIsoOfFin rfl

abbrev Colors (m n : ℕ) (J : Finset (Fin n)) := {i : Fin n // i ∉ J} → Fin m

/-- The first-urn colors and the shifted-down ranks of the marbles outside the first urn. -/
abbrev TailData (m n : ℕ) :=
  Σ J : Finset (Fin n), Colors m n J × (Fin J.card → ℕ)

/-- Reinsert in chronological order, using the selected positions to read the residual word. -/
def assemble {m n : ℕ} (d : TailData m n) : Fin (m+n) → ℕ :=
  Fin.addCases (fun i : Fin m => i.val) (fun i : Fin n =>
    if hi : i ∈ d.1 then m + d.2.2 ((selectedOrder d.1).symm ⟨i,hi⟩)
    else (d.2.1 ⟨i,hi⟩).val)

@[simp] private theorem assemble_prefix {m n : ℕ} (d : TailData m n) (i : Fin m) :
    assemble d (i.castAdd n) = i.val := by
  simp [assemble]

theorem assemble_color {m n : ℕ} (d : TailData m n) (i : Fin n) (hi : i ∉ d.1) :
    assemble d (Fin.natAdd m i) = (d.2.1 ⟨i,hi⟩).val := by
  simp [assemble, Fin.addCases_right, hi]

theorem assemble_selected {m n : ℕ} (d : TailData m n) (j : Fin d.1.card) :
    assemble d (Fin.natAdd m ((selectedOrder d.1) j).val) = m + d.2.2 j := by
  simp [assemble, Fin.addCases_right]

private theorem assemble_ge {m n : ℕ} (d : TailData m n) (i : Fin n) :
    m ≤ assemble d (Fin.natAdd m i) ↔ i ∈ d.1 := by
  by_cases h : i ∈ d.1
  · let j := (selectedOrder d.1).symm ⟨i,h⟩
    have hj : ((selectedOrder d.1) j).val = i :=
      congrArg Subtype.val ((selectedOrder d.1).apply_symm_apply ⟨i,h⟩)
    rw [← hj, assemble_selected]
    exact iff_of_true (Nat.le_add_right _ _) ((selectedOrder d.1) j).property
  · rw [assemble_color d i h]
    exact iff_of_false (not_le_of_gt (d.2.1 ⟨i,h⟩).isLt) h

/-- Delete exactly the first-urn tail placements, retaining their colors at their original positions. -/
def splitTail {m n : ℕ} (x : Fin (m+n) → ℕ) : TailData m n :=
  let J := Finset.univ.filter (fun i : Fin n => m ≤ x (Fin.natAdd m i))
  ⟨J, (fun i => ⟨x (Fin.natAdd m i.val), by simpa [J] using i.property⟩),
    (fun j => x (Fin.natAdd m ((selectedOrder J) j).val) - m)⟩

private theorem assemble_split {m n : ℕ} (x : Fin (m+n) → ℕ)
    (hp : ∀ i : Fin m, x (i.castAdd n) = i.val) :
    assemble (splitTail x) = x := by
  funext i
  refine Fin.addCases (motive := fun i => assemble (splitTail x) i = x i)
    (fun j => by rw [assemble_prefix, hp]) (fun j => ?_) i
  simp only [assemble, Fin.addCases_right]
  split
  next h =>
    have hj : ((selectedOrder (splitTail x).1) ((selectedOrder (splitTail x).1).symm
        ⟨j,h⟩)).val = j := congrArg Subtype.val ((selectedOrder _).apply_symm_apply ⟨j,h⟩)
    have hbound : m ≤ x (Fin.natAdd m j) := by simpa [splitTail] using h
    change m + (x (Fin.natAdd m (((selectedOrder (splitTail x).1)
      ((selectedOrder (splitTail x).1).symm ⟨j,h⟩)).val)) - m) = x (Fin.natAdd m j)
    rw [hj]
    omega
  next => rfl

private theorem assemble_injective {m n : ℕ} :
    Function.Injective (assemble (m := m) (n := n)) := by
  rintro ⟨J, c, r⟩ ⟨K, b, s⟩ he
  have hJK : J = K := by
    ext i
    rw [← assemble_ge ⟨J,c,r⟩, ← assemble_ge ⟨K,b,s⟩, he]
  subst K
  have hc : c = b := by
    funext i
    apply Fin.ext
    have h := congrFun he (Fin.natAdd m i.val)
    rw [assemble_color ⟨J,c,r⟩ i.val i.property, assemble_color ⟨J,b,s⟩ i.val i.property] at h
    exact h
  have hr : r = s := by
    funext j
    have h := congrFun he (Fin.natAdd m ((selectedOrder J) j).val)
    rw [assemble_selected ⟨J,c,r⟩ j, assemble_selected ⟨J,b,s⟩ j] at h
    exact Nat.add_left_cancel h
  subst c
  subst r
  rfl

private theorem split_assemble {m n : ℕ} (d : TailData m n) :
    splitTail (assemble d) = d :=
  assemble_injective (assemble_split _ (assemble_prefix d))


/-- Every tail prefix consists of the full first urn and the shifted residual prefix. -/
private theorem mem_before_assemble {m n : ℕ} (d : TailData m n) (i a : ℕ) :
    a ∈ before (assemble d) (m+i) ↔
      a < m ∨ ∃ j : Fin d.1.card,
        ((selectedOrder d.1) j).val.val < i ∧ m + d.2.2 j = a := by
  rw [mem_before]
  constructor
  · rintro ⟨p, hp, rfl⟩
    revert hp
    refine Fin.addCases (motive := fun p => p.val < m+i →
      assemble d p < m ∨ ∃ j : Fin d.1.card, ((selectedOrder d.1) j).val.val < i ∧
        m + d.2.2 j = assemble d p) ?_ ?_ p
    · intro j _
      rw [assemble_prefix]
      exact .inl j.isLt
    · intro j hj
      by_cases h : j ∈ d.1
      · let k := (selectedOrder d.1).symm ⟨j,h⟩
        have hk : ((selectedOrder d.1) k).val = j :=
          congrArg Subtype.val ((selectedOrder d.1).apply_symm_apply ⟨j,h⟩)
        have hji : j.val < i := Nat.lt_of_add_lt_add_left hj
        refine .inr ⟨k, by rw [hk]; exact hji, ?_⟩
        exact (assemble_selected d k).symm.trans (congrArg (assemble d ∘ Fin.natAdd m) hk)
      · rw [assemble_color d j h]
        exact .inl (d.2.1 ⟨j,h⟩).isLt
  · rintro (h | ⟨j,hj,hr⟩)
    · let p : Fin m := ⟨a,h⟩
      exact ⟨p.castAdd n, h.trans_le (Nat.le_add_right _ _), assemble_prefix d p⟩
    · exact ⟨Fin.natAdd m ((selectedOrder d.1) j).val, Nat.add_lt_add_left hj m,
        (assemble_selected d j).trans hr⟩

private theorem before_assemble_selected {m n : ℕ} (d : TailData m n) (j : Fin d.1.card) :
    before (assemble d) (m+((selectedOrder d.1) j).val.val) =
      Finset.range m ∪ (before d.2.2 j.val).image (m + ·) := by
  ext a
  rw [mem_before_assemble]
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, mem_before]
  constructor
  · rintro (h | ⟨k,hk,rfl⟩)
    · exact .inl h
    · have hh : (selectedOrder d.1) k < (selectedOrder d.1) j := hk
      exact .inr ⟨d.2.2 k, ⟨k, (selectedOrder d.1).lt_iff_lt.mp hh, rfl⟩, rfl⟩
  · rintro (h | ⟨_,⟨k,hk,rfl⟩,rfl⟩)
    · exact .inl h
    · exact .inr ⟨k, (selectedOrder d.1).strictMono hk, rfl⟩

/-- The actual occupied set after assembly, with a disjoint full and shifted part. -/
theorem used_assemble {m n : ℕ} (d : TailData m n) :
    used (assemble d) = Finset.range m ∪ (used d.2.2).image (m + ·) := by
  rw [← before_end]
  ext a
  simp only [mem_before_assemble, Finset.mem_union, Finset.mem_range, Finset.mem_image, mem_used]
  constructor
  · rintro (h | ⟨k,_,rfl⟩)
    · exact .inl h
    · exact .inr ⟨d.2.2 k, ⟨k,rfl⟩, rfl⟩
  · rintro (h | ⟨_,⟨k,rfl⟩,rfl⟩)
    · exact .inl h
    · exact .inr ⟨k, ((selectedOrder d.1) k).val.isLt, rfl⟩

private theorem card_range_union_shift (m : ℕ) (s : Finset ℕ) :
    (Finset.range m ∪ s.image (m + ·)).card = m + s.card := by
  rw [Finset.card_union_of_disjoint, Finset.card_range, Finset.card_image_of_injective]
  · exact fun _ _ => Nat.add_left_cancel
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_range, Finset.mem_image]
    rintro _ ha ⟨b,_,rfl⟩
    omega

private theorem threshold_shift (m p : ℕ) (hm : 0 < m) :
    threshold m (m+p) = m + threshold m p := by
  unfold threshold
  rw [show m+p = m*1+p by simp, Nat.mul_add_div hm, Nat.mul_add, Nat.mul_one]

private theorem move_shift {m p a : ℕ} (hm : 0 < m) :
    Move m (m+p) (m+a) ↔ Move m p a := by
  simp only [Move, threshold_shift _ _ hm, Nat.add_left_cancel_iff, Nat.add_lt_add_iff_left]

private theorem before_assemble_prefix {m n : ℕ} (d : TailData m n) (i : Fin m) :
    before (assemble d) i.val = Finset.range i.val := by
  ext a
  rw [mem_before, Finset.mem_range]
  constructor
  · rintro ⟨p,hp,rfl⟩
    revert hp
    refine Fin.addCases (motive := fun p => p.val < i.val → assemble d p < i.val)
        (fun j hj => ?_) (fun j hj => ?_) p
    · rwa [assemble_prefix]
    · have hi := i.isLt
      change m + j.val < i.val at hj
      omega
  · intro h
    let j : Fin m := ⟨a,h.trans i.isLt⟩
    exact ⟨j.castAdd n,h,assemble_prefix d j⟩

/-- Inserting any first-urn color is legal throughout the tail. -/
private theorem assemble_color_move {m n : ℕ} (hm : 0 < m) (d : TailData m n) (i : Fin n)
    (hi : i ∉ d.1) : Move m (before (assemble d) (m+i.val)).card (assemble d (Fin.natAdd m i)) := by
  have hsub : Finset.range m ⊆ before (assemble d) (m+i.val) :=
    fun _ ha => (mem_before_assemble _ _ _).2 (.inl (Finset.mem_range.mp ha))
  have hmle : m ≤ (before (assemble d) (m+i.val)).card := by
    simpa using Finset.card_le_card hsub
  have hdiv : 1 ≤ (before (assemble d) (m+i.val)).card / m :=
    (Nat.le_div_iff_mul_le hm).2 (by simpa using hmle)
  have hthr : m ≤ threshold m (before (assemble d) (m+i.val)).card := by
    simpa [threshold] using Nat.mul_le_mul_left m hdiv
  rw [assemble_color d i hi]
  exact .inr ((d.2.1 ⟨i,hi⟩).isLt.trans_le hthr)

theorem assemble_legal_iff {m n : ℕ} (hm : 0 < m) (d : TailData m n) :
    Legal m (assemble d) ↔ Legal m d.2.2 := by
  rw [legal_iff_moves, legal_iff_moves]
  have hsel (j : Fin d.1.card) :
      Move m (before (assemble d) (Fin.natAdd m ((selectedOrder d.1) j).val).val).card
          (assemble d (Fin.natAdd m ((selectedOrder d.1) j).val)) ↔
        Move m (before d.2.2 j.val).card (d.2.2 j) := by
    change Move m (before (assemble d) (m+((selectedOrder d.1) j).val.val)).card _ ↔ _
    rw [before_assemble_selected, card_range_union_shift, assemble_selected, move_shift hm]
  constructor
  · exact fun h j => (hsel j).1 (h _)
  · intro h i
    refine Fin.addCases (motive := fun i => Move m (before (assemble d) i.val).card (assemble d i))
      (fun j => ?_) (fun j => ?_) i
    · change Move m (before (assemble d) j.val).card (assemble d (j.castAdd n))
      rw [before_assemble_prefix, Finset.card_range, assemble_prefix]
      exact .inl rfl
    · by_cases hj : j ∈ d.1
      · let k := (selectedOrder d.1).symm ⟨j,hj⟩
        have hk : ((selectedOrder d.1) k).val = j :=
          congrArg Subtype.val ((selectedOrder d.1).apply_symm_apply ⟨j,hj⟩)
        rw [← hk]
        exact (hsel k).2 (h k)
      · exact assemble_color_move hm d j hj


abbrev WordPayload (m n r : ℕ) :=
  Σ J : Finset (Fin n), Colors m n J × WordFiber m J.card r

abbrev Payload (m n r : ℕ) :=
  Σ J : Finset (Fin n), Colors m n J × U m J.card r

def TailData.forget {m n r : ℕ} (d : WordPayload m n r) : TailData m n :=
  ⟨d.1, d.2.1, d.2.2.val.val⟩

private theorem TailData.forget_injective {m n r : ℕ} :
    Function.Injective (TailData.forget (m := m) (n := n) (r := r)) := by
  rintro ⟨J,c,⟨⟨w,hw⟩,hk⟩⟩ ⟨K,b,⟨⟨v,hv⟩,hl⟩⟩ h
  change (⟨J,c,w⟩ : TailData m n) = ⟨K,b,v⟩ at h
  have hJK : J = K := congrArg Sigma.fst h
  subst K
  have hdata : (c,w) = (b,v) := eq_of_heq (Sigma.mk.inj h).2
  have hcb : c = b := congrArg Prod.fst hdata
  have hwv : w = v := congrArg Prod.snd hdata
  subst b
  subst v
  rfl

/-- Delete the first urn from the word and record the original positions and colors. -/
def deleteWord {m n r : ℕ} (hm : 0 < m) (w : WordFiber m (m+n) (m+r)) :
    WordPayload m n r := by
  let d := splitTail w.val.val
  have ha : assemble d = w.val.val := assemble_split _ (forced_prefix w.val.property)
  have hl : Legal m d.2.2 := (assemble_legal_iff hm d).1 (ha ▸ w.val.property)
  have hcnt := w.property
  rw [← ha, used_assemble, card_range_union_shift] at hcnt
  exact ⟨d.1, d.2.1, ⟨⟨d.2.2, hl⟩, Nat.add_left_cancel hcnt⟩⟩

/-- Prepend the full first urn and reinsert the two kinds of tail placements in order. -/
def reinsertWord {m n r : ℕ} (hm : 0 < m) (d : WordPayload m n r) :
    WordFiber m (m+n) (m+r) :=
  ⟨⟨assemble (TailData.forget d), (assemble_legal_iff hm _).2 d.2.2.val.property⟩, by
    rw [used_assemble, card_range_union_shift]
    exact congrArg (m + ·) d.2.2.property⟩

/-- Reinsertion after deletion recovers the forced prefix and each tail position. -/
theorem reinsert_delete_word {m n r : ℕ} (hm : 0 < m) (w : WordFiber m (m+n) (m+r)) :
    reinsertWord hm (deleteWord hm w) = w :=
  Subtype.ext (Subtype.ext (assemble_split _ (forced_prefix w.val.property)))

/-- Deletion after reinsertion recovers the selected positions, each color, and each residual rank. -/
theorem delete_reinsert_word {m n r : ℕ} (hm : 0 < m) (d : WordPayload m n r) :
    deleteWord hm (reinsertWord hm d) = d :=
  TailData.forget_injective (split_assemble (TailData.forget d))

def wordShift {m n r : ℕ} (hm : 0 < m) : WordFiber m (m+n) (m+r) ≃ WordPayload m n r :=
  ⟨deleteWord hm, reinsertWord hm, reinsert_delete_word hm, delete_reinsert_word hm⟩

noncomputable def payloadEquivWord {m n r : ℕ} (hm : 0 < m) :
    Payload m n r ≃ WordPayload m n r :=
  Equiv.sigmaCongrRight (fun J =>
    Equiv.prodCongr (Equiv.refl (Colors m n J)) (fiberEquivWord hm (le_refl J.card)))

private noncomputable def sourceEquivWord {m n r : ℕ} (hm : 0 < m) :
    U m (n + m) (m + r) ≃ WordFiber m (m + n) (m + r) :=
  (Equiv.cast (congrArg (fun length => U m length (m + r)) (Nat.add_comm n m))).trans
    (fiberEquivWord hm (le_refl (m + n)))

/-- Chronological deletion on raw orbits, with the original complement colors. -/
noncomputable def deleteFirstUrn {m n r : ℕ} (hm : 0 < m) :
    U m (n + m) (m + r) → Payload m n r :=
  fun q => (payloadEquivWord hm).symm (wordShift hm (sourceEquivWord hm q))

/-- Chronological reinsertion on raw orbits. -/
noncomputable def reinsertFirstUrn {m n r : ℕ} (hm : 0 < m) :
    Payload m n r → U m (n + m) (m + r) :=
  fun d => (sourceEquivWord hm).symm ((wordShift hm).symm (payloadEquivWord hm d))

theorem reinsert_delete {m n r : ℕ} (hm : 0 < m) (q : U m (n + m) (m + r)) :
    reinsertFirstUrn hm (deleteFirstUrn hm q) = q := by
  simp only [reinsertFirstUrn, deleteFirstUrn, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem delete_reinsert {m n r : ℕ} (hm : 0 < m) (d : Payload m n r) :
    deleteFirstUrn hm (reinsertFirstUrn hm d) = d := by
  simp only [reinsertFirstUrn, deleteFirstUrn, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Popov's first-urn shift on the literal occupied-count orbit quotients. -/
noncomputable def firstUrnEquiv {m n r : ℕ} (hm : 0 < m) :
    U m (n + m) (m + r) ≃ Payload m n r :=
  ⟨deleteFirstUrn hm, reinsertFirstUrn hm, reinsert_delete hm, delete_reinsert hm⟩

/-- The signed column is empty at every negative index. -/
def SignedU (m t : ℕ) (k : ℤ) := if k < 0 then Empty else U m t k.toNat

theorem signed_negative_empty {m t : ℕ} {k : ℤ} (hn : k < 0) : IsEmpty (SignedU m t k) := by
  rw [SignedU, ite_eq_left hn]
  infer_instance

private theorem word_card_ge_m {m n : ℕ} (w : Word m (m+n)) : m ≤ (used w.val).card := by
  have ha := assemble_split _ (forced_prefix w.property)
  rw [← ha, used_assemble, card_range_union_shift]
  exact Nat.le_add_right _ _

theorem below_first_urn {m n k : ℕ} (hm : 0 < m) (hk : k < m) :
    IsEmpty (U m (n+m) k) := by
  refine ⟨fun q => ?_⟩
  let q' : U m (m+n) k :=
    (Equiv.cast (congrArg (fun length => U m length k) (Nat.add_comm n m))) q
  let w := fiberEquivWord hm (le_refl (m+n)) q'
  exact (not_le_of_gt hk) (w.property ▸ word_card_ge_m w.val)

private theorem word_card_le_length {m t k : ℕ} (w : WordFiber m t k) : k ≤ t :=
  w.property ▸ used_card_le w.val.val

private theorem beyond_length {m t k : ℕ} (hm : 0 < m) (hk : t < k) : IsEmpty (U m t k) :=
  ⟨fun q => (not_le_of_gt hk) (word_card_le_length (fiberEquivWord hm (le_refl t) q))⟩


/-! ## Finite counting -/

/-- Recurrence (7.1), with the zero column separated from the positive columns. -/
def stirling (m : ℕ) : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | _+1, 0 => 0
  | t+1, k+1 => threshold m (k+1) * stirling m t (k+1) + stirling m t k

/-- Definition 7.1 with the paper's negative-column convention. -/
def S (m t : ℕ) (k : ℤ) : ℕ :=
  if k < 0 then 0 else stirling m t k.toNat

@[simp] private theorem S_nat (m t k : ℕ) : S m t k = stirling m t k := by simp [S]

instance wordFinite (m t : ℕ) : Finite (Word m t) :=
  Finite.of_injective (fun w : Word m t => fun i : Fin t =>
    (⟨w.val i, (word_rank_le w.property i).trans_lt i.isLt⟩ : Fin t))
    (fun _ _ h => Subtype.ext (funext (fun i => congrArg Fin.val (congrFun h i))))

noncomputable instance wordFiberFintype (m t k : ℕ) : Fintype (WordFiber m t k) :=
  Fintype.ofFinite _

instance arrangementsFinite (A m t : ℕ) : Finite (Arrangements A m t) :=
  Finite.of_surjective (Quotient.mk (orbitSetoid A m t)) (by
    intro q
    exact Quotient.inductionOn q (fun x => ⟨x,rfl⟩))

noncomputable instance rawFiberFintype (A m t k : ℕ) : Fintype (Fiber A m t k) :=
  Fintype.ofFinite _

private theorem used_snoc {t : ℕ} {α : Type} [DecidableEq α] (x : Fin t → α) (a : α) :
    used (Fin.snoc (α := fun _ => α) x a) = insert a (used x) := by
  rw [used_init, Fin.init_snoc, Fin.snoc_last]

private def appendOld {m t k : ℕ} (a : Fin (threshold m k)) (w : WordFiber m t k) :
    WordFiber m (t+1) k :=
  ⟨⟨Fin.snoc (α := fun _ => ℕ) w.val.val a.val, legal_snoc w.val a.val
    (.inr (w.property.symm ▸ a.isLt))⟩, by
    have ha : a.val ∈ used w.val.val := by
      rw [used_range w.val.property, Finset.mem_range, w.property]
      exact a.isLt.trans_le (threshold_le _ _)
    rw [used_snoc, Finset.insert_eq_of_mem ha]
    exact w.property⟩

private def appendFresh {m t k : ℕ} (w : WordFiber m t k) :
    WordFiber m (t+1) (k+1) :=
  ⟨⟨Fin.snoc (α := fun _ => ℕ) w.val.val k, legal_snoc w.val k (.inl w.property.symm)⟩, by
    have hk : k ∉ used w.val.val := by
      rw [used_range w.val.property, Finset.mem_range, w.property]
      exact Nat.lt_irrefl _
    rw [used_snoc, Finset.card_insert_of_notMem hk, w.property]⟩

private theorem old_prefix_count {m t k : ℕ} (a : Fin (threshold m k)) (w : WordFiber m t k) :
    (used (Fin.init (appendOld a w).val.val)).card = k := by
  change (used (Fin.init (Fin.snoc (α := fun _ => ℕ) w.val.val a.val))).card = k
  rw [Fin.init_snoc]
  exact w.property

private theorem fresh_prefix_count {m t k : ℕ} (w : WordFiber m t k) :
    (used (Fin.init (appendFresh w).val.val)).card = k := by
  change (used (Fin.init (Fin.snoc (α := fun _ => ℕ) w.val.val k))).card = k
  rw [Fin.init_snoc]
  exact w.property

/-- The last move is one of the available old compartments, or the unique fresh compartment. -/
noncomputable def lastMoveEquiv (m t k : ℕ) :
    (Fin (threshold m (k+1)) × WordFiber m t (k+1) ⊕ WordFiber m t k) ≃
      WordFiber m (t+1) (k+1) := by
  let go : (Fin (threshold m (k+1)) × WordFiber m t (k+1) ⊕ WordFiber m t k) →
      WordFiber m (t+1) (k+1) :=
    Sum.elim (fun d => appendOld d.1 d.2) appendFresh
  refine Equiv.ofBijective go ⟨?_, ?_⟩
  · rintro (⟨a,u⟩ | u) (⟨b,v⟩ | v) h
    · have hh := congrArg (fun w : WordFiber m (t+1) (k+1) => w.val.val) h
      change Fin.snoc (α := fun _ => ℕ) u.val.val a.val =
        Fin.snoc (α := fun _ => ℕ) v.val.val b.val at hh
      have huv := congrArg Fin.init hh
      rw [Fin.init_snoc, Fin.init_snoc] at huv
      have hab := congrFun hh (Fin.last t)
      rw [Fin.snoc_last, Fin.snoc_last] at hab
      exact congrArg Sum.inl (Prod.ext (Fin.ext hab) (Subtype.ext (Subtype.ext huv)))
    · change appendOld a u = appendFresh v at h
      have he := congrArg (fun w : WordFiber m (t+1) (k+1) => (used (Fin.init w.val.val)).card) h
      change (used (Fin.init (appendOld a u).val.val)).card =
        (used (Fin.init (appendFresh v).val.val)).card at he
      rw [old_prefix_count, fresh_prefix_count] at he
      omega
    · change appendFresh u = appendOld b v at h
      have he := congrArg (fun w : WordFiber m (t+1) (k+1) => (used (Fin.init w.val.val)).card) h
      change (used (Fin.init (appendFresh u).val.val)).card =
        (used (Fin.init (appendOld b v).val.val)).card at he
      rw [fresh_prefix_count, old_prefix_count] at he
      omega
    · have hh := congrArg (fun w : WordFiber m (t+1) (k+1) => Fin.init w.val.val) h
      change Fin.init (Fin.snoc (α := fun _ => ℕ) u.val.val k) =
        Fin.init (Fin.snoc (α := fun _ => ℕ) v.val.val k) at hh
      rw [Fin.init_snoc, Fin.init_snoc] at hh
      exact congrArg Sum.inr (Subtype.ext (Subtype.ext hh))
  · intro w
    let v := Fin.init w.val.val
    let a := w.val.val (Fin.last t)
    have hl : Legal m v := w.val.property.1
    have ha : Move m (used v).card a := w.val.property.2
    have hw : (insert a (used v)).card = k+1 := by
      change (insert (w.val.val (Fin.last t)) (used (Fin.init w.val.val))).card = _
      rw [← used_init]
      exact w.property
    rcases ha with hf | ho
    · have hn : a ∉ used v := by
        rw [used_range hl, Finset.mem_range, hf]
        exact Nat.lt_irrefl _
      rw [Finset.card_insert_of_notMem hn] at hw
      have hp : (used v).card = k := Nat.succ.inj hw
      refine ⟨Sum.inr ⟨⟨v,hl⟩,hp⟩, Subtype.ext (Subtype.ext ?_)⟩
      change Fin.snoc (α := fun _ => ℕ) v k = w.val.val
      have he : k = a := hp.symm.trans hf.symm
      calc
        Fin.snoc (α := fun _ => ℕ) v k = Fin.snoc (α := fun _ => ℕ) v a :=
          congrArg (Fin.snoc (α := fun _ => ℕ) v) he
        _ = w.val.val := Fin.snoc_init_self _
    · have hn : a ∈ used v := by
        rw [used_range hl, Finset.mem_range]
        exact ho.trans_le (threshold_le _ _)
      rw [Finset.insert_eq_of_mem hn] at hw
      refine ⟨Sum.inl (⟨a, hw ▸ ho⟩, ⟨⟨v,hl⟩,hw⟩), Subtype.ext (Subtype.ext ?_)⟩
      exact Fin.snoc_init_self w.val.val

private theorem word_nonempty_count {m t k : ℕ} (w : WordFiber m (t+1) k) : 0 < k :=
  w.property ▸ Finset.card_pos.mpr ⟨_, mem_used.mpr ⟨Fin.last t,rfl⟩⟩

def emptyWord (m : ℕ) : WordFiber m 0 0 :=
  ⟨⟨Fin.elim0, trivial⟩, by simp⟩

private theorem word_zero_unique (m : ℕ) (w : WordFiber m 0 0) : w = emptyWord m :=
  Subtype.ext (Subtype.ext (funext (fun i => Fin.elim0 i)))

private theorem word_zero_length_empty {m k : ℕ} (hk : 0 < k) : IsEmpty (WordFiber m 0 k) :=
  ⟨fun w => (Nat.lt_irrefl 0) (hk.trans_le (word_card_le_length w))⟩

/-- Counting canonical words by the actual last move gives the printed Stirling recurrence. -/
private theorem card_word_eq_stirling (m t k : ℕ) :
    Fintype.card (WordFiber m t k) = stirling m t k := by
  induction t generalizing k with
  | zero =>
    cases k with
    | zero =>
      let : Unique (WordFiber m 0 0) := ⟨⟨emptyWord m⟩, word_zero_unique m⟩
      rw [Fintype.card_unique]
      rfl
    | succ k =>
      let := word_zero_length_empty (m := m) (Nat.zero_lt_succ k)
      rw [Fintype.card_of_isEmpty]
      rfl
  | succ t ih =>
    cases k with
    | zero =>
      let : IsEmpty (WordFiber m (t+1) 0) := ⟨fun w => (Nat.lt_irrefl 0) (word_nonempty_count w)⟩
      rw [Fintype.card_of_isEmpty]
      rfl
    | succ k =>
      rw [← Fintype.card_congr (lastMoveEquiv m t k), Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin, ih, ih]
      rfl

theorem card_urn_eq_stirling {m : ℕ} (hm : 0 < m) (t k : ℕ) :
    Fintype.card (U m t k) = stirling m t k :=
  (Fintype.card_congr (fiberEquivWord hm (le_refl t))).trans (card_word_eq_stirling m t k)


open scoped BigOperators

private theorem card_colors (m n : ℕ) (J : Finset (Fin n)) :
    Fintype.card (Colors m n J) = m^(n-J.card) := by
  rw [Fintype.card_fun, Fintype.card_subtype_compl (fun i => i ∈ J),
    Fintype.card_fin, Fintype.card_fin, Fintype.card_coe J]

private theorem group_subsets_by_card (n : ℕ) (f : ℕ → ℕ) :
    (∑ J : Finset (Fin n), f J.card) =
      ∑ j ∈ Finset.range (n+1), n.choose j * f j := by
  classical
  rw [← Finset.powerset_univ, Finset.sum_powerset]
  simp only [Finset.sum_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

/-- Taking cardinalities of the exhibited first-urn equivalence and grouping its payload. -/
private theorem shift_nat {m : ℕ} (hm : 0 < m) (n r : ℕ) :
    stirling m (n+m) (m+r) =
      ∑ j ∈ Finset.range (n+1), n.choose j * m^(n-j) * stirling m j r := by
  classical
  have h := Fintype.card_congr (firstUrnEquiv (m := m) (n := n) (r := r) hm)
  change Fintype.card (U m (n+m) (m+r)) =
    Fintype.card (Σ J : Finset (Fin n), Colors m n J × U m J.card r) at h
  rw [card_urn_eq_stirling hm, Fintype.card_sigma] at h
  calc
    stirling m (n+m) (m+r) =
        ∑ J : Finset (Fin n), m^(n-J.card) * stirling m J.card r := by
      simpa only [Fintype.card_prod, card_colors, card_urn_eq_stirling hm] using h
    _ = _ := by
      simpa only [mul_assoc] using group_subsets_by_card n (fun j => m^(n-j) * stirling m j r)

/-- Equation (7.2), including the negative residual columns of Definition 7.1. -/
theorem shift_7_2 {m : ℕ} (hm : 0 < m) (n k : ℕ) :
    S m (n+m) k =
      ∑ j ∈ Finset.range (n+1), n.choose j * m^(n-j) * S m j ((k : ℤ) - m) := by
  by_cases h : k < m
  · let : IsEmpty (U m (n+m) k) := below_first_urn hm h
    have hzero := card_urn_eq_stirling hm (n+m) k
    rw [Fintype.card_of_isEmpty] at hzero
    rw [S_nat, ← hzero]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hneg : (k : ℤ) - m < 0 := by omega
    simp [S, hneg]
  · let r := k - m
    have hk : k = m+r := by dsimp [r]; omega
    have hr : (k : ℤ) - m = (r : ℤ) := by omega
    rw [hr, S_nat, hk]
    simp only [S_nat]
    exact shift_nat hm n r


/-! ## Boundary cases -/

/-- At capacity one, the legal move is exactly the ordinary zero-based restricted-growth rule. -/
theorem capacity_one_legal {t : ℕ} (x : Fin t → ℕ) :
    Legal 1 x ↔ ∀ i : Fin t, x i ≤ (before x i.val).card := by
  rw [legal_iff_moves]
  simp only [Move, threshold, Nat.div_one, Nat.one_mul, le_iff_eq_or_lt]

/-- At capacity one, the first urn is the block containing the initial marble. -/
private theorem capacity_one_first_block {n : ℕ} (w : Word 1 (1+n)) (i : Fin (1+n)) :
    w.val i / 1 = w.val ((0 : Fin 1).castAdd n) / 1 ↔ w.val i = 0 := by
  let first : Fin (1 + n) := (0 : Fin 1).castAdd n
  have h := (capacity_one_legal w.val).1 w.property first
  have hbefore : before w.val first.val = ∅ := by
    ext a
    simp [mem_before, first]
  rw [hbefore, Finset.card_empty] at h
  have hfirst : w.val first = 0 := Nat.eq_zero_of_le_zero h
  change w.val i / 1 = w.val first / 1 ↔ w.val i = 0
  simp [hfirst]

private theorem capacity_one_color_unique {n : ℕ} (J : Finset (Fin n)) :
    Subsingleton (Colors 1 n J) :=
  inferInstance

theorem capacity_one_stirling (t k : ℕ) : stirling 1 t k = Nat.stirlingSecond t k := by
  induction t generalizing k with
  | zero =>
    cases k <;> rfl
  | succ t ih =>
    cases k with
    | zero => rw [stirling, Nat.stirlingSecond_succ_zero]
    | succ k =>
      rw [stirling, Nat.stirlingSecond_succ_succ, ih, ih]
      simp [threshold, Nat.add_comm]

/-- With no tail positions, the payload index and the color function have empty domains. -/
private theorem zero_tail_selected (J : Finset (Fin 0)) : J = ∅ := by
  ext i
  exact Fin.elim0 i

@[instance_reducible] def zero_tail_colors (m : ℕ) (J : Finset (Fin 0)) :
    Unique (Colors m 0 J) :=
  ⟨⟨fun i => Fin.elim0 i.val⟩, fun _ => funext (fun i => Fin.elim0 i.val)⟩

@[instance_reducible] noncomputable def zero_length_quotient_unique {m : ℕ} (hm : 0 < m) : Unique (U m 0 0) := by
  letI : Unique (WordFiber m 0 0) := ⟨⟨emptyWord m⟩, word_zero_unique m⟩
  exact (fiberEquivWord hm (le_refl 0)).unique

@[instance_reducible] noncomputable def zero_tail_source_unique {m : ℕ} (hm : 0 < m) : Unique (U m (0+m) m) := by
  letI : Unique (Payload m 0 0) := by
    let c := zero_tail_colors m (∅ : Finset (Fin 0))
    let u : Unique (U m (∅ : Finset (Fin 0)).card 0) := by
      rw [Finset.card_empty]
      exact zero_length_quotient_unique hm
    refine ⟨⟨⟨∅, c.default, u.default⟩⟩, ?_⟩
    rintro ⟨J, d⟩
    have hJ := zero_tail_selected J
    subst J
    exact congrArg (Sigma.mk ∅) (Prod.ext (c.uniq _) (u.uniq _))
  have e := firstUrnEquiv (n := 0) (r := 0) hm
  exact e.unique

theorem zero_tail_source_empty {m k : ℕ} (hm : 0 < m) (hk : k ≠ m) :
    IsEmpty (U m (0+m) k) := by
  rcases lt_or_gt_of_ne hk with h | h
  · exact below_first_urn hm h
  · exact beyond_length hm (by simpa using h)

theorem zero_tail_residual_empty {m r : ℕ} (hm : 0 < m) (hr : 0 < r) :
    IsEmpty (Payload m 0 r) := by
  refine ⟨fun d => ?_⟩
  have hc : d.1.card = 0 := by rw [zero_tail_selected d.1, Finset.card_empty]
  exact (beyond_length (k := r) hm (by rwa [hc])).false d.2.2

theorem beyond_length_payload_empty {m n r : ℕ} (hm : 0 < m) (hr : n < r) :
    IsEmpty (Payload m n r) := by
  refine ⟨fun d => ?_⟩
  have hJ : d.1.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ d.1)
  exact (beyond_length hm (hJ.trans_lt hr)).false d.2.2

theorem below_first_urn_payload_empty {m n k : ℕ} (hk : k < m) :
    IsEmpty (Σ J : Finset (Fin n), Colors m n J × SignedU m J.card ((k : ℤ) - m)) :=
  ⟨fun d => (signed_negative_empty (by omega)).false d.2.2⟩

/-- Old slots of any full urn remain legal, even if another urn has only started. -/
theorem full_urn_reuse {A m : ℕ} (s : Finset (Address A m)) (a : Address A m)
    (hf : Full s a.1) : RawMove s a :=
  ⟨fun _ => hf, fun h => (h ⟨a.2, hf a.2⟩).elim⟩

private def decideLegal (m : ℕ) : {t : ℕ} → (x : Fin t → ℕ) → Decidable (Legal m x)
  | 0, _ => isTrue trivial
  | t+1, x => by
    change Decidable (Legal m (Fin.init x) ∧
      Move m (used (Fin.init x)).card (x (Fin.last t)))
    letI := decideLegal m (Fin.init x)
    unfold Move
    infer_instance

/-- At capacity two, the fourth move can revisit urn zero while urn one is incomplete. -/
theorem partial_example :
    Legal 2 (![0,1,2,0,3] : Fin 5 → ℕ) ∧
      before (![0,1,2,0,3] : Fin 5 → ℕ) 3 = Finset.range 3 := by
  constructor
  · exact @of_decide_eq_true _ (decideLegal 2 (![0,1,2,0,3] : Fin 5 → ℕ)) rfl
  · decide

/-! ## Actual raw addresses retained by deletion -/

/-- In column `m`, every tail marble goes back to the first urn. -/
theorem zero_residual_selected {m n : ℕ} (hm : 0 < m) (d : Payload m n 0) :
    d.1 = ∅ := by
  apply Finset.card_eq_zero.mp
  by_contra h
  let w := fiberEquivWord hm (le_refl d.1.card) d.2.2
  let i : Fin d.1.card := ⟨0, Nat.pos_of_ne_zero h⟩
  have hp : 0 < (used w.val.val).card := Finset.card_pos.mpr ⟨_, mem_used.mpr ⟨i,rfl⟩⟩
  have h0 : (used w.val.val).card = 0 := w.property
  rw [h0] at hp
  exact (Nat.lt_irrefl 0) hp

/-- Selection for deletion is exactly avoidance of the raw urn containing marble one. -/
theorem selected_iff_avoids_first_urn {A m n : ℕ} (hm : 0 < m) (ht : m+n ≤ A)
    (x : Raw A m (m+n)) (i : Fin n) :
    i ∈ (splitTail (normalize hm ht x).val).1 ↔
      (x.val (Fin.natAdd m i)).1 ≠ (x.val ((⟨0,hm⟩ : Fin m).castAdd n)).1 := by
  let w := normalize hm ht x
  have he := normalize_urn_eq_iff hm ht x (Fin.natAdd m i) ((⟨0,hm⟩ : Fin m).castAdd n)
  have hn : (¬ w.val (Fin.natAdd m i) / m = w.val ((⟨0, hm⟩ : Fin m).castAdd n) / m) ↔
      _ := not_congr he
  refine Iff.trans ?_ hn
  rw [forced_prefix w.property]
  simp [splitTail, Nat.div_eq_zero_iff_lt hm]
  rfl


/-- The first `m` raw marbles use exactly all the slots of their common urn. -/
theorem raw_forced_used {A m n : ℕ} (hm : 0 < m) (ht : m+n ≤ A)
    (x : Raw A m (m+n)) :
    used (fun i : Fin m => x.val (i.castAdd n)) =
      Finset.univ.image (fun c : Fin m => ((x.val ((⟨0,hm⟩ : Fin m).castAdd n)).1, c)) := by
  let w := normalize hm ht x
  let i₀ : Fin m := ⟨0,hm⟩
  obtain ⟨e, he⟩ := replay_normalize_orbit hm ht x
  have hrep (i : Fin m) :
      replay hm ht w (i.castAdd n) = ((replay hm ht w (i₀.castAdd n)).1, i) := by
    apply Prod.ext
    · apply Fin.ext
      change w.val (i.castAdd n) / m = w.val (i₀.castAdd n) / m
      rw [forced_prefix w.property, forced_prefix w.property]
      exact (Nat.div_eq_of_lt i.isLt).trans (Nat.div_eq_of_lt i₀.isLt).symm
    · apply Fin.ext
      change w.val (i.castAdd n) % m = i.val
      rw [forced_prefix w.property, Nat.mod_eq_of_lt i.isLt]
  ext a
  rw [mem_used, Finset.mem_image]
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨(x.val (i.castAdd n)).2, Finset.mem_univ _, Prod.ext ?_ rfl⟩
    rw [← he (i.castAdd n), ← he (i₀.castAdd n)]
    exact (congrArg (fun b => (e.apply b).1) (hrep i)).symm
  · rintro ⟨c,_,rfl⟩
    let u := (replay hm ht w (i₀.castAdd n)).1
    obtain ⟨d, hd⟩ := (e.slot u).surjective c
    refine ⟨d, ?_⟩
    rw [← he (d.castAdd n), hrep d, ← he (i₀.castAdd n)]
    exact Prod.ext rfl hd

/-- The retained tail has exactly the distinct raw addresses outside the first urn. -/
theorem retained_raw_used {A m n : ℕ} (hm : 0 < m) (ht : m+n ≤ A)
    (x : Raw A m (m+n)) :
    let J := (splitTail (normalize hm ht x).val).1
    let first := (x.val ((⟨0,hm⟩ : Fin m).castAdd n)).1
    used (fun j : Fin J.card => x.val (Fin.natAdd m ((selectedOrder J) j).val)) =
      (used x.val).filter (fun a => a.1 ≠ first) := by
  dsimp only
  let J := (splitTail (normalize hm ht x).val).1
  let i₀ : Fin m := ⟨0,hm⟩
  let first := (x.val (i₀.castAdd n)).1
  have hfirst (i : Fin m) : (x.val (i.castAdd n)).1 = first := by
    apply (normalize_urn_eq_iff hm ht x _ _).1
    rw [forced_prefix (normalize hm ht x).property, forced_prefix (normalize hm ht x).property]
    exact (Nat.div_eq_of_lt i.isLt).trans (Nat.div_eq_of_lt i₀.isLt).symm
  ext a
  rw [Finset.mem_filter, mem_used, mem_used]
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨⟨_, rfl⟩, (selected_iff_avoids_first_urn hm ht x _).1 ((selectedOrder J) j).property⟩
  · rintro ⟨⟨i,hi⟩,hna⟩
    revert hi
    refine Fin.addCases
      (motive := fun i => x.val i = a →
        ∃ j : Fin J.card, x.val (Fin.natAdd m ((selectedOrder J) j).val) = a) ?_ ?_ i
    · intro j hj
      exact (hna ((congrArg Prod.fst hj).symm.trans (hfirst j))).elim
    · intro j hj
      have hJ : j ∈ J := (selected_iff_avoids_first_urn hm ht x j).2
        (fun he => hna ((congrArg Prod.fst hj).symm.trans he))
      let k := (selectedOrder J).symm ⟨j,hJ⟩
      have hk : ((selectedOrder J) k).val = j :=
        congrArg Subtype.val ((selectedOrder J).apply_symm_apply ⟨j,hJ⟩)
      exact ⟨k, (congrArg (x.val ∘ Fin.natAdd m) hk).trans hj⟩

/-- Removing the first urn removes exactly `m` distinct raw addresses. -/
theorem retained_raw_count {A m n : ℕ} (hm : 0 < m) (ht : m+n ≤ A)
    (x : Raw A m (m+n)) :
    let J := (splitTail (normalize hm ht x).val).1
    m + (used (fun j : Fin J.card => x.val (Fin.natAdd m ((selectedOrder J) j).val))).card =
      (used x.val).card := by
  dsimp only
  rw [retained_raw_used hm ht x]
  let first := (x.val ((⟨0,hm⟩ : Fin m).castAdd n)).1
  let f := fun c : Fin m => (first,c)
  have hf : Function.Injective f := fun _ _ h => congrArg Prod.snd h
  have hfull : (used x.val).filter (fun a => a.1 = first) = Finset.univ.image f := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨a.2, Prod.ext h.2.symm rfl⟩
    · rintro ⟨c,rfl⟩
      refine ⟨?_,rfl⟩
      have hc : f c ∈ Finset.univ.image f := Finset.mem_image_of_mem _ (Finset.mem_univ c)
      have hpre := raw_forced_used hm ht x
      change used (fun i : Fin m => x.val (i.castAdd n)) = Finset.univ.image f at hpre
      rw [← hpre, mem_used] at hc
      obtain ⟨i,hi⟩ := hc
      exact mem_used.mpr ⟨i.castAdd n, hi⟩
  let s := (used x.val).filter (fun a => a.1 = first)
  let t := (used x.val).filter (fun a => a.1 ≠ first)
  have hd : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2
  have hu : s ∪ t = used x.val := by
    ext a
    by_cases ha : a.1 = first <;> simp [s, t, ha]
  have hc : s.card = m := by
    change ((used x.val).filter (fun a => a.1 = first)).card = m
    rw [hfull, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  calc
    m + t.card = s.card + t.card := congrArg (· + t.card) hc.symm
    _ = (s ∪ t).card := (Finset.card_union_of_disjoint hd).symm
    _ = (used x.val).card := congrArg Finset.card hu

end PopovUrnShift
