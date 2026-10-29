/- GID: D5/S3/Combinatorics/Partitions/FerrersLevelGluing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/FerrersLevelGluing
   mirror-E: none(waiver:ordered-level-gluing-bijection)
   anchors: [D5/S3/Combinatorics/Partitions/FerrersLevelCounting]
   utility: none
   digest: Compatible level paths reconstruct exactly the bounded flat row fibers. -/

import D5.S3.Combinatorics.Partitions.FerrersLevelCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048

noncomputable section
namespace D5.S3.Combinatorics.Partitions.FerrersLevelGluing
open D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
open D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open scoped BigOperators

private def headIndex (r : ℕ) (as : List ℕ) (j : Fin (r+1)) :
    Fin ((r+1)*(as.length+1)) := ⟨j.val, by nlinarith [j.isLt]⟩
private def tailIndex (r : ℕ) (as : List ℕ) (j : Fin ((r+1)*as.length)) :
    Fin ((r+1)*(as.length+1)) := ⟨r+1+j.val, by nlinarith [j.isLt]⟩

private def split (r U a : ℕ) (as : List ℕ) (u : Fin (U+1))
    (x : FlatFiber r U (a::as) u) :
    (v : Fin (U+1)) × (Level r U u.val v.val a × FlatFiber r U as v) := by
  let h : Fin (r+1) → Fin (U+1) := fun j => x.val (headIndex r as j)
  let t : Fin ((r+1)*as.length) → Fin (U+1) := fun j => x.val (tailIndex r as j)
  refine ⟨h (Fin.last r), ⟨h, ?_, ?_, rfl, ?_⟩, ⟨t, ?_, ?_, ?_⟩⟩
  · intro i j hij
    apply x.property.1
    exact Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hij)
  · intro j
    exact Fin.le_iff_val_le_val.mp (x.property.2.1 _)
  · simpa [h,headIndex] using x.property.2.2 (0 : Fin (a::as).length)
  · intro i j hij
    apply x.property.1
    apply Fin.le_iff_val_le_val.mpr
    dsimp [tailIndex]
    exact Nat.add_le_add_left (Fin.le_iff_val_le_val.mp hij) (r+1)
  · intro j
    apply x.property.1
    apply Fin.le_iff_val_le_val.mpr
    dsimp [headIndex,tailIndex]
    omega
  · intro p
    have hh := x.property.2.2 p.succ
    simpa [t,tailIndex, Nat.mul_add, Nat.mul_succ, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hh

private def assemble (r U : ℕ) (as : List ℕ)
    (h : Fin (r+1) → Fin (U+1)) (t : Fin ((r+1)*as.length) → Fin (U+1))
    (i : Fin ((r+1)*(as.length+1))) : Fin (U+1) :=
  if hi : i.val < r+1 then h ⟨i.val,hi⟩
  else t ⟨i.val-(r+1), by have := i.isLt; nlinarith⟩

private theorem assemble_head (r U : ℕ) (as : List ℕ)
    (h : Fin (r+1) → Fin (U+1)) (t : Fin ((r+1)*as.length) → Fin (U+1))
    (j : Fin (r+1)) : assemble r U as h t (headIndex r as j) = h j := by
  simp only [assemble, headIndex, dif_pos j.isLt]

private theorem assemble_tail (r U : ℕ) (as : List ℕ)
    (h : Fin (r+1) → Fin (U+1)) (t : Fin ((r+1)*as.length) → Fin (U+1))
    (j : Fin ((r+1)*as.length)) : assemble r U as h t (tailIndex r as j) = t j := by
  have hn : ¬r+1+j.val < r+1 := by omega
  simp only [assemble, tailIndex, dif_neg hn, Nat.add_sub_cancel_left]

private def join (r U a : ℕ) (as : List ℕ) (u : Fin (U+1))
    (z : (v : Fin (U+1)) × (Level r U u.val v.val a × FlatFiber r U as v)) :
    FlatFiber r U (a::as) u := by
  let h := z.2.1
  let t := z.2.2
  refine ⟨assemble r U as h.val t.val, ?_, ?_, ?_⟩
  · intro i j hij
    dsimp [assemble]
    split_ifs with hi hj hj
    · exact h.property.1 (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hij))
    · apply Fin.le_iff_val_le_val.mpr
      have ht := Fin.le_iff_val_le_val.mp (t.property.2.1 ⟨j.val-(r+1),by nlinarith [j.isLt]⟩)
      have hh := Fin.le_iff_val_le_val.mp (h.property.1 (Fin.le_last ⟨i.val,hi⟩))
      have he := h.property.2.2.1
      omega
    · have := Fin.le_iff_val_le_val.mp hij
      omega
    · exact t.property.1 (Fin.le_iff_val_le_val.mpr
        (Nat.sub_le_sub_right (Fin.le_iff_val_le_val.mp hij) (r+1)))
  · intro i
    dsimp [assemble]
    split_ifs with hi
    · exact Fin.le_iff_val_le_val.mpr (h.property.2.1 _)
    · apply Fin.le_iff_val_le_val.mpr
      have ht := Fin.le_iff_val_le_val.mp (t.property.2.1 ⟨i.val-(r+1),by nlinarith [i.isLt]⟩)
      have hh := h.property.2.1 (Fin.last r)
      have he := h.property.2.2.1
      omega
  · intro p
    cases p using Fin.cases with
    | zero =>
        simpa only [List.getElem_cons_zero] using
          (show (∑ j : Fin (r+1), (assemble r U as h.val t.val (headIndex r as j)).val) = a by
            simp only [assemble_head]; exact h.property.2.2.2)
    | succ p =>
        have hs := t.property.2.2 p
        simpa only [List.getElem_cons_succ] using
          (show (∑ j : Fin (r+1), (assemble r U as h.val t.val
            (tailIndex r as ⟨(r+1)*p.val+j.val, by
              have hp := Nat.mul_le_mul_left (r+1) (Nat.succ_le_of_lt p.isLt)
              rw [Nat.mul_succ] at hp
              omega⟩)).val) = as[p.val] by
            simp only [assemble_tail]; exact hs)

private def splitEquiv (r U a : ℕ) (as : List ℕ) (u : Fin (U+1)) :
    FlatFiber r U (a::as) u ≃
      ((v : Fin (U+1)) × (Level r U u.val v.val a × FlatFiber r U as v)) where
  toFun := split r U a as u
  invFun := join r U a as u
  left_inv x := by
    apply Subtype.ext
    funext i
    change assemble r U as _ _ i = x.val i
    unfold assemble
    split_ifs with hi
    · congr 1
    · congr 1
      apply Fin.ext
      dsimp [tailIndex]
      omega
  right_inv z := by
    rcases z with ⟨v,h,t⟩
    have he : (h.val (Fin.last r)) = v := Fin.ext h.property.2.2.1
    apply Sigma.ext he
    apply heq_of_eq
    apply Prod.ext
    · apply Subtype.ext
      funext j
      exact assemble_head r U as h.val t.val j
    · apply Subtype.ext
      funext j
      exact assemble_tail r U as h.val t.val j

/-- Every flat row profile is exactly one compatible sequence of levels. -/
def flatPathsEquiv (r U : ℕ) (as : List ℕ) (u : Fin (U+1)) :
    FlatFiber r U as u ≃ Paths r U as u := by
  induction as generalizing u with
  | nil =>
      refine { toFun := fun _ => PUnit.unit
               invFun := fun _ => ⟨Fin.elim0, ?_, ?_, ?_⟩
               left_inv := ?_
               right_inv := fun _ => rfl }
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
      · intro x; apply Subtype.ext; funext i; exact Fin.elim0 i
  | cons a as ih =>
      exact (splitEquiv r U a as u).trans
        (Equiv.sigmaCongrRight (fun v => Equiv.prodCongr (Equiv.refl _) (ih v)))

/-- Explicit finite Gaussian evaluation of the entire flat row fiber. -/
theorem flat_card (r U : ℕ) (as : List ℕ) (u : Fin (U+1)) :
    (Fintype.card (FlatFiber r U as u) : ℤ) = count r U as u := by
  classical
  rw [Fintype.card_congr (flatPathsEquiv r U as u), paths_card]

end D5.S3.Combinatorics.Partitions.FerrersLevelGluing
