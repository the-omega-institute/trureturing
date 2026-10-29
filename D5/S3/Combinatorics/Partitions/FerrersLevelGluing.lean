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
  · simpa [h,headIndex,rowIndex] using x.property.2.2 (0 : Fin (a::as).length)
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
    simpa [t,tailIndex,rowIndex, Nat.mul_add, Nat.mul_succ, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hh

private def assemble (r U : ℕ) (as : List ℕ)
    (h : Fin (r+1) → Fin (U+1)) (t : Fin ((r+1)*as.length) → Fin (U+1))
    (i : Fin ((r+1)*(as.length+1))) : Fin (U+1) :=
  if hi : i.val < r+1 then h ⟨i.val,hi⟩
  else t ⟨i.val-(r+1), by have hi := i.isLt; simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hi; omega⟩

private theorem assemble_head (r U : ℕ) (as : List ℕ)
    (h : Fin (r+1) → Fin (U+1)) (t : Fin ((r+1)*as.length) → Fin (U+1))
    (j : Fin (r+1)) : assemble r U as h t (headIndex r as j) = h j := by
  simp [assemble, headIndex, j.isLt]

private theorem assemble_tail (r U : ℕ) (as : List ℕ)
    (h : Fin (r+1) → Fin (U+1)) (t : Fin ((r+1)*as.length) → Fin (U+1))
    (j : Fin ((r+1)*as.length)) : assemble r U as h t (tailIndex r as j) = t j := by
  have hn : ¬r+1+j.val < r+1 := by omega
  simp [assemble, tailIndex, hn]

private def join (r U a : ℕ) (as : List ℕ) (u : Fin (U+1))
    (z : (v : Fin (U+1)) × (Level r U u.val v.val a × FlatFiber r U as v)) :
    FlatFiber r U (a::as) u := by
  let h := z.2.1
  let t := z.2.2
  refine ⟨assemble r U as h.val t.val, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val < r+1
    · by_cases hj : j.val < r+1
      · simp only [assemble, dif_pos hi, dif_pos hj]
        exact h.property.1 (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hij))
      · simp only [assemble, dif_pos hi, dif_neg hj]
        apply Fin.le_iff_val_le_val.mpr
        have ht := Fin.le_iff_val_le_val.mp
          (t.property.2.1 ⟨j.val-(r+1),by have hj' := j.isLt; simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hj'; omega⟩)
        have hh := Fin.le_iff_val_le_val.mp (h.property.1 (Fin.le_last ⟨i.val,hi⟩))
        have he := h.property.2.2.1
        omega
    · have hn : ¬j.val < r+1 := by have := Fin.le_iff_val_le_val.mp hij; omega
      simp only [assemble, dif_neg hi, dif_neg hn]
      exact t.property.1 (Fin.le_iff_val_le_val.mpr
        (Nat.sub_le_sub_right (Fin.le_iff_val_le_val.mp hij) (r+1)))
  · intro i
    dsimp [assemble]
    split_ifs with hi
    · exact Fin.le_iff_val_le_val.mpr (h.property.2.1 _)
    · apply Fin.le_iff_val_le_val.mpr
      have ht := Fin.le_iff_val_le_val.mp (t.property.2.1 ⟨i.val-(r+1),by have hi := i.isLt; simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hi; omega⟩)
      have hh := h.property.2.1 (Fin.last r)
      have he := h.property.2.2.1
      omega
  · intro p
    cases p using Fin.cases with
    | zero =>
        simpa only [rowIndex, Nat.mul_zero, Nat.zero_add, headIndex, Fin.val_zero, List.getElem_cons_zero] using
          (show (∑ j : Fin (r+1), (assemble r U as h.val t.val (headIndex r as j)).val) = a by
            simp only [assemble_head]; exact h.property.2.2.2)
    | succ p =>
        have hs := t.property.2.2 p
        simpa [rowIndex, tailIndex, Nat.mul_add, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (show (∑ j : Fin (r+1), (assemble r U as h.val t.val
            (tailIndex r as ⟨(r+1)*p.val+j.val, by
              have hp := Nat.mul_le_mul_left (r+1) (Nat.succ_le_of_lt p.isLt)
              rw [Nat.mul_succ] at hp
              omega⟩)).val) = as[p.val] by
            simp only [assemble_tail]; exact hs)

private theorem pair_heq (r U a : ℕ) (as : List ℕ) (u v w : Fin (U+1))
    (hv : v = w)
    (x : Level r U u.val v.val a × FlatFiber r U as v)
    (y : Level r U u.val w.val a × FlatFiber r U as w)
    (hh : x.1.val = y.1.val) (ht : x.2.val = y.2.val) : HEq x y := by
  subst w
  exact heq_of_eq (Prod.ext (Subtype.ext hh) (Subtype.ext ht))

private def splitEquiv (r U a : ℕ) (as : List ℕ) (u : Fin (U+1)) :
    FlatFiber r U (a::as) u ≃
      ((v : Fin (U+1)) × (Level r U u.val v.val a × FlatFiber r U as v)) where
  toFun := split r U a as u
  invFun := join r U a as u
  left_inv x := by
    apply Subtype.ext
    funext i
    dsimp only [join, split]
    unfold assemble
    split_ifs with hi
    · rfl
    · apply congrArg x.val
      apply Fin.ext
      dsimp [tailIndex]
      omega
  right_inv z := by
    rcases z with ⟨v,h,t⟩
    have hv : (split r U a as u (join r U a as u ⟨v,h,t⟩)).fst = v := by
      change assemble r U as h.val t.val (headIndex r as (Fin.last r)) = v
      rw [assemble_head]
      exact Fin.ext h.property.2.2.1
    apply Sigma.ext hv
    apply pair_heq r U a as u _ _ hv
    · change (fun j => assemble r U as h.val t.val (headIndex r as j)) = h.val
      funext j
      exact assemble_head r U as h.val t.val j
    · change (fun j => assemble r U as h.val t.val (tailIndex r as j)) = t.val
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
