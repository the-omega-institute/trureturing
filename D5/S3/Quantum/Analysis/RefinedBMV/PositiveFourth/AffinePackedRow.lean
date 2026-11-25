/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffinePackedRow
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Merge increasing group indices with their packed affine factors. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.GroupedAffineMasks

/-! A sorted column can consume the factor list in one pass. This avoids
restarting a list traversal for every index during kernel reduction. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

open private uFactors packedRow Certificate.packedColumns radix magnitude sweep masked
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.GroupedAffineMasks

private def increasing : List (ℕ × ℤ) → Bool
  | a :: b :: gs => decide (a.1 < b.1) && increasing (b :: gs)
  | _ => true

private theorem pairwise_of_increasing : ∀ gs : List (ℕ × ℤ),
    increasing gs = true → gs.Pairwise (fun a b => a.1 < b.1)
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: gs, h => by
    obtain ⟨hab, htail⟩ := Bool.and_eq_true_iff.mp h
    have hab' : a.1 < b.1 := of_decide_eq_true hab
    have hb := pairwise_of_increasing (b :: gs) htail
    refine List.pairwise_cons.mpr ⟨?_, hb⟩
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hab'
    · exact hab'.trans ((List.pairwise_cons.mp hb).1 g hg)

private def mergeDot (cursor : ℕ) : List ℤ → List (ℕ × ℤ) → ℤ
  | [], _ => 0
  | _, [] => 0
  | f :: fs, (i, w) :: gs =>
    if i = cursor then
      w * f + mergeDot (cursor + 1) fs gs
    else
      mergeDot (cursor + 1) fs ((i, w) :: gs)

private theorem cons_lookup_advance (f : ℤ) (fs : List ℤ) (cursor i : ℕ)
    (h : cursor < i) :
    ((f :: fs)[i - cursor]?).getD 0 = (fs[i - (cursor + 1)]?).getD 0 := by
  rw [show i - cursor = (i - (cursor + 1)) + 1 by omega, List.getElem?_cons_succ]

private theorem sum_lookup_advance (f : ℤ) (fs : List ℤ) (cursor : ℕ)
    (gs : List (ℕ × ℤ)) (h : ∀ g ∈ gs, cursor < g.1) :
    (gs.map fun g => g.2 * ((f :: fs)[g.1 - cursor]?).getD 0).sum =
      (gs.map fun g => g.2 * (fs[g.1 - (cursor + 1)]?).getD 0).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro g hg
  rw [cons_lookup_advance _ _ _ _ (h g hg)]

private theorem mergeDot_eq (fs : List ℤ) (cursor : ℕ) (gs : List (ℕ × ℤ))
    (horder : gs.Pairwise (fun a b => a.1 < b.1))
    (hcursor : ∀ g ∈ gs, cursor ≤ g.1) :
    mergeDot cursor fs gs = (gs.map fun g => g.2 * (fs[g.1 - cursor]?).getD 0).sum := by
  induction fs generalizing cursor gs with
  | nil => simp [mergeDot]
  | cons f fs ih =>
    cases gs with
    | nil => rfl
    | cons g gs =>
      obtain ⟨i, w⟩ := g
      obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp horder
      have hi : cursor ≤ i := hcursor (i, w) (by simp)
      by_cases heq : i = cursor
      · subst i
        have hlt (g : ℕ × ℤ) (hg : g ∈ gs) : cursor < g.1 := hfirst g hg
        simp only [mergeDot, if_true, List.map_cons, List.sum_cons, Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
        rw [ih (cursor + 1) gs htail (fun g hg => hlt g hg),
          sum_lookup_advance f fs cursor gs hlt]
      · have hlt (g : ℕ × ℤ) (hg : g ∈ (i, w) :: gs) : cursor < g.1 := by
          rcases List.mem_cons.mp hg with rfl | hg
          · omega
          · exact hi.trans_lt (hfirst g hg)
        rw [mergeDot, ite_eq_right heq, ih (cursor + 1) _ horder (fun g hg => hlt g hg),
          sum_lookup_advance f fs cursor _ hlt]

private theorem uFactors_zero (roots : List ℤ) (k i : ℕ) (hi : i < k) :
    ((uFactors roots k)[i]?).getD 0 = 0 := by
  unfold uFactors
  rw [List.getElem?_toArray, List.getElem?_mapIdx]
  cases roots[i]? <;> simp [hi]

private def columnDot (factors : Array ℤ) (k : ℕ) (gs : List (ℕ × ℤ)) : ℤ :=
  if increasing gs then mergeDot 0 factors.toList gs
  else (gs.map fun g => if g.1 < k then 0 else g.2 * (factors[g.1]?).getD 0).sum

private theorem columnDot_eq (roots : List ℤ) (k : ℕ) (gs : List (ℕ × ℤ)) :
    columnDot (uFactors roots k) k gs =
      (gs.map fun g => if g.1 < k then 0 else g.2 * ((uFactors roots k)[g.1]?).getD 0).sum := by
  unfold columnDot
  split
  next h =>
    rw [mergeDot_eq _ _ _ (pairwise_of_increasing gs h) (fun g _ => Nat.zero_le g.1)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro g _
    simp only [Nat.sub_zero, Array.getElem?_toList]
    split
    · rw [uFactors_zero roots k g.1 (by assumption), mul_zero]
    · rfl
  next _ => rfl

private def mergedRow (roots : List ℤ) (columns : List (ℤ × List (ℕ × ℤ))) (k : ℕ) :
    List (ℤ × ℤ) :=
  let factors := uFactors roots k
  columns.map fun col => (col.1, columnDot factors k col.2)

private theorem mergedRow_eq (roots : List ℤ) (columns : List (ℤ × List (ℕ × ℤ))) (k : ℕ) :
    mergedRow roots columns k = packedRow roots columns k := by
  unfold mergedRow packedRow
  apply List.map_congr_left
  intro col _
  simp only [columnDot_eq]

def Certificate.checkMergedRow (c : Certificate) (width digits k : ℕ) : Bool :=
  let x := radix width
  let mask := DimThree.PackedCheck.polynomialMask width digits
  sweep (masked mask) c.rootsV.length
    (mergedRow (c.rootsU.map (magnitude x)) (Certificate.packedColumns c x) k)

theorem Certificate.checkMergedRow_eq (c : Certificate) (width digits k : ℕ) :
    c.checkMergedRow width digits k = c.checkRow width digits k := by
  simp only [Certificate.checkMergedRow, Certificate.checkRow, Certificate.checkRowPrefix, mergedRow_eq]

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
