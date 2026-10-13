/- GID: D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetAlternatingHistories
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Finite-window reset tables and whole-ray images retain all numbered boundaries for every positive even carrier. -/

import D5.S3.ConceptDynamics.Coding.ResetAlternatingSquares

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetNumberedHistories

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (History)
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity (expandedGraph groupHistory)
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat Edge)
open Multiplicative

namespace Alternating

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion

theorem source_typed {q : ℕ} (hq : 0 < q)
    (p : Edge (resetMatrix q) × Sign) :
    sourceB (typedEdge p) = (expandedGraph (resetMatrix q)).source p := by
  rw [← actual_source hq, original_typed]

theorem target_typed {q : ℕ} (hq : 0 < q)
    (p : Edge (resetMatrix q) × Sign) :
    targetB hq (typedEdge p) = (expandedGraph (resetMatrix q)).target p := by
  rw [← actual_target hq, original_typed]

private def wordList {q N : ℕ}
    (w : LegalWord (expandedGraph (resetMatrix q)) N) : List (B q) :=
  List.ofFn (fun j => typedEdge (w.edge j))

private theorem wordList_length {q N : ℕ}
    (w : LegalWord (expandedGraph (resetMatrix q)) N) : (wordList w).length = N := by
  simp [wordList]

private theorem wordList_pick {q N : ℕ} (hq : 0 < q)
    (w : LegalWord (expandedGraph (resetMatrix q)) N) (k : ℕ) (hk : k < N) :
    pick hq (wordList w) k = typedEdge (w.edge ⟨k, hk⟩) := by
  rw [pick_eq hq _ k (by simpa [wordList] using hk)]
  simp [wordList]

private theorem wordList_slice {q N : ℕ}
    (w : LegalWord (expandedGraph (resetMatrix q)) N) (a n : ℕ) (ha : a + n ≤ N) :
    wordList (sliceWord (expandedGraph (resetMatrix q)) w a n ha) =
      ((wordList w).drop a).take n := by
  apply List.ext_getElem
  · simp [wordList] <;> omega
  · intro j hj hj'
    simp [wordList, sliceWord]

private theorem ofFn_path {q : ℕ} (hq : 0 < q) {n : ℕ}
    (f : Fin (n + 1) → B q)
    (hf : ∀ j : Fin (n + 1), ∀ hj : j.val + 1 < n + 1,
      targetB hq (f j) = sourceB (f ⟨j.val + 1, hj⟩)) :
    ListPath hq (sourceB (f 0)) (List.ofFn f) (targetB hq (f (Fin.last n))) := by
  induction n with
  | zero =>
      simpa [List.ofFn_succ] using
        ListPath.cons (hq := hq) (x := f 0) rfl (ListPath.nil (targetB hq (f 0)))
  | succ n ih =>
      let g : Fin (n + 1) → B q := fun j => f j.succ
      have hg : ∀ j : Fin (n + 1), ∀ hj : j.val + 1 < n + 1,
          targetB hq (g j) = sourceB (g ⟨j.val + 1, hj⟩) := by
        intro j hj
        simpa [g, Fin.succ] using hf j.succ (by simp only [Fin.val_succ]; omega)
      have hp := ih g hg
      have hh : targetB hq (f 0) = sourceB (g 0) := hf 0 (by simp)
      rw [← hh] at hp
      simpa [List.ofFn_succ, g, Fin.last, Fin.succ] using ListPath.cons rfl hp

private theorem wordList_path {q n : ℕ} (hq : 0 < q)
    (w : LegalWord (expandedGraph (resetMatrix q)) (n + 1)) :
    ListPath hq ((expandedGraph (resetMatrix q)).source (w.edge 0))
      (wordList w) ((expandedGraph (resetMatrix q)).target (w.edge (Fin.last n))) := by
  have hp := ofFn_path hq (fun j => typedEdge (w.edge j)) (by
    intro j hj
    rw [target_typed hq, source_typed hq]
    exact w.legal j hj)
  simpa [wordList, source_typed hq, target_typed hq] using hp

private theorem strip_input_adjacent {q : ℕ} {hq : 0 < q}
    {xs ys : List (B q)} {r s : R q} (hs : Strip hq xs r s ys)
    (k : ℕ) (hk : k + 1 < xs.length) :
    targetB hq (pick hq xs k) = sourceB (pick hq xs (k + 1)) := by
  induction hs generalizing k with
  | nil => simp at hk
  | @cons xs ys r m s x y sq tail ih =>
      cases k with
      | zero =>
          cases tail with
          | nil => simp at hk
          | cons sq' tail' =>
              simpa [pick] using
                (square_endpoints sq).2.2.1.trans (square_endpoints sq').1
      | succ k => simpa [pick] using ih k (by simpa using hk)

private theorem strip_output_adjacent {q : ℕ} {hq : 0 < q}
    {xs ys : List (B q)} {r s : R q} (hs : Strip hq xs r s ys)
    (k : ℕ) (hk : k + 1 < ys.length) :
    targetB hq (pick hq ys k) = sourceB (pick hq ys (k + 1)) := by
  induction hs generalizing k with
  | nil => simp at hk
  | @cons xs ys r m s x y sq tail ih =>
      cases k with
      | zero =>
          cases tail with
          | nil => simp at hk
          | cons sq' tail' =>
              simpa [pick] using
                (square_endpoints sq).2.2.2.symm.trans (square_endpoints sq').2.1
      | succ k => simpa [pick] using ih k (by simpa using hk)

/- The table algorithms use q+1 squares, with the identity R edge at the
   prescribed end.  The first/last output is exactly the additional central
   square after the q forgetting squares. -/
private def forwardTable {q : ℕ} (hq : 0 < q)
    (w : LegalWord (expandedGraph (resetMatrix q)) (q + 1)) :
    Edge (resetMatrix q) × Sign :=
  let xs := wordList w
  let s := identityR ((expandedGraph (resetMatrix q)).target (w.edge ⟨q, by omega⟩))
  let ys := (sweepLeft hq xs s).2
  actualEdgeEquiv hq (pick hq ys 0)

private def backwardTable {q : ℕ} (hq : 0 < q)
    (w : LegalWord (expandedGraph (resetMatrix q)) (q + 1)) :
    Edge (resetMatrix q) × Sign :=
  let ys := wordList w
  let r := identityR ((expandedGraph (resetMatrix q)).source (w.edge ⟨0, by omega⟩))
  let xs := (sweepRight hq r ys).1
  actualEdgeEquiv hq (pick hq xs q)

private theorem forwardTable_of_strip {q : ℕ} {hq : 0 < q} (he : Even q)
    (w : LegalWord (expandedGraph (resetMatrix q)) (q + 1))
    {ys : List (B q)} {r s : R q} (hs : Strip hq (wordList w) r s ys) :
    forwardTable hq w = originalEdge hq (pick hq ys 0) := by
  let s0 := identityR ((expandedGraph (resetMatrix q)).target (w.edge (Fin.last q)))
  have hc : sourceR s0 = (expandedGraph (resetMatrix q)).target (w.edge (Fin.last q)) := rfl
  have ht := (sweepLeft_sound (wordList_path hq w) s0 hc).1
  have hi := first_output_independent he ht hs (wordList_length w)
  exact congrArg (originalEdge hq) hi

private theorem backwardTable_of_strip {q : ℕ} {hq : 0 < q} (he : Even q)
    (w : LegalWord (expandedGraph (resetMatrix q)) (q + 1))
    {xs : List (B q)} {r s : R q} (hs : Strip hq xs r s (wordList w)) :
    backwardTable hq w = originalEdge hq (pick hq xs q) := by
  let r0 := identityR ((expandedGraph (resetMatrix q)).source (w.edge 0))
  have hc : targetR hq r0 = (expandedGraph (resetMatrix q)).source (w.edge 0) := rfl
  have ht := (sweepRight_sound (wordList_path hq w) r0 hc).1
  have hi := last_input_independent he ht hs (wordList_length w)
  exact congrArg (originalEdge hq) hi

private theorem pick_window {q : ℕ} (hq : 0 < q) (xs : List (B q))
    (a n k : ℕ) (ha : a + n ≤ xs.length) (hk : k < n) :
    pick hq ((xs.drop a).take n) k = pick hq xs (a + k) := by
  have hl : ((xs.drop a).take n).length = n := by simp <;> omega
  rw [pick_eq hq _ k (by omega), pick_eq hq xs (a + k) (by omega)]
  simp

private theorem forward_slice {q N : ℕ} {hq : 0 < q} (he : Even q)
    (w : LegalWord (expandedGraph (resetMatrix q)) N)
    {ys : List (B q)} {r s : R q} (hs : Strip hq (wordList w) r s ys)
    (a : ℕ) (ha : a + (q + 1) ≤ N) :
    forwardTable hq (sliceWord (expandedGraph (resetMatrix q)) w a (q + 1) ha) =
      originalEdge hq (pick hq ys a) := by
  obtain ⟨u, v, ht⟩ := strip_window hs a (q + 1)
  rw [← wordList_slice w a (q + 1) ha] at ht
  rw [forwardTable_of_strip he _ ht]
  have hlen : ys.length = N := (strip_length hs).symm.trans (wordList_length w)
  rw [pick_window hq ys a (q + 1) 0 (by omega) (by omega), Nat.add_zero]

private theorem backward_slice {q N : ℕ} {hq : 0 < q} (he : Even q)
    (w : LegalWord (expandedGraph (resetMatrix q)) N)
    {xs : List (B q)} {r s : R q} (hs : Strip hq xs r s (wordList w))
    (a : ℕ) (ha : a + (q + 1) ≤ N) :
    backwardTable hq (sliceWord (expandedGraph (resetMatrix q)) w a (q + 1) ha) =
      originalEdge hq (pick hq xs (a + q)) := by
  obtain ⟨u, v, ht⟩ := strip_window hs a (q + 1)
  rw [← wordList_slice w a (q + 1) ha] at ht
  rw [backwardTable_of_strip he _ ht]
  have hlen : xs.length = N := (strip_length hs).trans (wordList_length w)
  rw [pick_window hq xs a (q + 1) q (by omega) (by omega)]

private theorem forward_seam {q : ℕ} (hq : 0 < q) (he : Even q) :
    Seam (expandedGraph (resetMatrix q)) (expandedGraph (resetMatrix q))
      (forwardTable hq) := by
  intro w
  let s0 := identityR ((expandedGraph (resetMatrix q)).target (w.edge (Fin.last (q + 1))))
  have ht := (sweepLeft_sound (wordList_path hq w) s0 rfl).1
  rw [forward_slice he w ht 0 (by omega), forward_slice he w ht 1 (by omega)]
  rw [actual_target, actual_source]
  have hy : (sweepLeft hq (wordList w) s0).2.length = q + 1 + 1 := by
    rw [sweepLeft_length, wordList_length]
  exact strip_output_adjacent ht 0 (by omega)

private theorem backward_seam {q : ℕ} (hq : 0 < q) (he : Even q) :
    Seam (expandedGraph (resetMatrix q)) (expandedGraph (resetMatrix q))
      (backwardTable hq) := by
  intro w
  let r0 := identityR ((expandedGraph (resetMatrix q)).source (w.edge 0))
  have ht := (sweepRight_sound (wordList_path hq w) r0 rfl).1
  rw [backward_slice he w ht 0 (by omega), backward_slice he w ht 1 (by omega)]
  rw [actual_target, actual_source]
  have hx : (sweepRight hq r0 (wordList w)).1.length = q + 1 + 1 := by
    rw [sweepRight_length, wordList_length]
  simpa only [Nat.zero_add, Nat.add_zero, Nat.add_comm] using strip_input_adjacent ht q (by omega)

private theorem forward_roundtrip {q : ℕ} (hq : 0 < q) (he : Even q)
    (hf : Seam (expandedGraph (resetMatrix q)) (expandedGraph (resetMatrix q))
      (forwardTable hq))
    (w : LegalWord (expandedGraph (resetMatrix q)) (q + q + 1)) :
    backwardTable hq
      (mapBlock (expandedGraph (resetMatrix q)) (expandedGraph (resetMatrix q))
        (forwardTable hq) hf w (by omega) (by omega)) = w.edge ⟨q, by omega⟩ := by
  let s0 := identityR ((expandedGraph (resetMatrix q)).target (w.edge (Fin.last (q + q))))
  let ys := (sweepLeft hq (wordList w) s0).2
  have ht := (sweepLeft_sound (wordList_path hq w) s0 rfl).1
  have hy : ys.length = q + q + 1 := by
    dsimp [ys]
    rw [sweepLeft_length, wordList_length]
  let out := mapBlock (expandedGraph (resetMatrix q)) (expandedGraph (resetMatrix q))
    (forwardTable hq) hf w (L := q + 1) (by omega) (by omega)
  have hout : wordList out = ys.take (q + 1) := by
    apply List.ext_getElem
    · simp [wordList, hy] <;> omega
    · intro j hj hj'
      have hjq : j < q + 1 := by simpa [wordList] using hj
      have heval := forward_slice he w ht j (by omega)
      simp only [wordList, List.getElem_ofFn]
      change typedEdge (forwardTable hq
        (sliceWord (expandedGraph (resetMatrix q)) w j (q + 1) _)) = _
      rw [heval, typed_original]
      rw [pick_eq hq ys j (by omega)]
      simp
  obtain ⟨m, hp, _⟩ := strip_split ht (q + 1)
  change Strip hq ((wordList w).take (q + 1)) _ m (ys.take (q + 1)) at hp
  rw [← hout] at hp
  change backwardTable hq out = _
  rw [backwardTable_of_strip he out hp]
  have hpick : pick hq ((wordList w).take (q + 1)) q =
      typedEdge (w.edge ⟨q, by omega⟩) := by
    have hi := pick_window hq (wordList w) 0 (q + 1) q
      (by rw [wordList_length]; omega) (by omega)
    simpa only [List.drop_zero, Nat.zero_add, wordList_pick hq w q (by omega)] using hi
  rw [hpick, original_typed]

private theorem backward_roundtrip {q : ℕ} (hq : 0 < q) (he : Even q)
    (hg : Seam (expandedGraph (resetMatrix q)) (expandedGraph (resetMatrix q))
      (backwardTable hq))
    (w : LegalWord (expandedGraph (resetMatrix q)) (q + q + 1)) :
    forwardTable hq
      (mapBlock (expandedGraph (resetMatrix q)) (expandedGraph (resetMatrix q))
        (backwardTable hq) hg w (by omega) (by omega)) = w.edge ⟨q, by omega⟩ := by
  let r0 := identityR ((expandedGraph (resetMatrix q)).source (w.edge 0))
  let xs := (sweepRight hq r0 (wordList w)).1
  have ht := (sweepRight_sound (wordList_path hq w) r0 rfl).1
  have hx : xs.length = q + q + 1 := by
    dsimp [xs]
    rw [sweepRight_length, wordList_length]
  let out := mapBlock (expandedGraph (resetMatrix q)) (expandedGraph (resetMatrix q))
    (backwardTable hq) hg w (L := q + 1) (by omega) (by omega)
  have hout : wordList out = xs.drop q := by
    apply List.ext_getElem
    · simp [wordList, hx] <;> omega
    · intro j hj hj'
      have hjq : j < q + 1 := by simpa [wordList] using hj
      have heval := backward_slice he w ht j (by omega)
      simp only [wordList, List.getElem_ofFn]
      change typedEdge (backwardTable hq
        (sliceWord (expandedGraph (resetMatrix q)) w j (q + 1) _)) = _
      rw [heval, typed_original]
      rw [pick_eq hq xs (j + q) (by omega)]
      simp [Nat.add_comm]
  obtain ⟨m, _, hp⟩ := strip_split ht q
  change Strip hq (xs.drop q) m _ ((wordList w).drop q) at hp
  rw [← hout] at hp
  change forwardTable hq out = _
  rw [forwardTable_of_strip he out hp]
  have hpick : pick hq ((wordList w).drop q) 0 =
      typedEdge (w.edge ⟨q, by omega⟩) := by
    rw [pick_eq hq _ 0 (by rw [List.length_drop, wordList_length]; omega)]
    simp only [wordList, List.getElem_drop, List.getElem_ofFn, Nat.add_zero]
  rw [hpick, original_typed]

/- The additive numbered boundary retains the local squares and their
   finite forgetting, and identifies the generic lift window. -/

open D5.S3.ConceptDynamics.Coding.SameCutWholeRayBridge
open D5.S3.ConceptDynamics.Coding.NumberedSameCutWholeRay

/- Numbering for a sum is coefficientwise: the first summand occupies
   [0,M.coeff), and the second occupies [M.coeff,M.coeff+N.coeff).
   The source, target, group label and every Fin copy are retained. -/
def addLeft {q : ℕ} (M N : GroupMat Sign q q) (e : Edge M) :
    Edge (M + N) :=
  ⟨e.source, e.target, e.label, ⟨e.number.val, by
    have h := e.number.isLt
    change e.number.val < (M e.source e.target + N e.source e.target).coeff e.label
    rw [MonoidAlgebra.coeff_add]
    change e.number.val < (M e.source e.target).coeff e.label +
      (N e.source e.target).coeff e.label
    omega⟩⟩

def addRight {q : ℕ} (M N : GroupMat Sign q q) (e : Edge N) :
    Edge (M + N) :=
  ⟨e.source, e.target, e.label,
    ⟨(M e.source e.target).coeff e.label + e.number.val, by
      have h := e.number.isLt
      change (M e.source e.target).coeff e.label + e.number.val <
        (M e.source e.target + N e.source e.target).coeff e.label
      rw [MonoidAlgebra.coeff_add]
      change (M e.source e.target).coeff e.label + e.number.val <
        (M e.source e.target).coeff e.label + (N e.source e.target).coeff e.label
      omega⟩⟩

private def splitAdd {q : ℕ} (M N : GroupMat Sign q q) (e : Edge (M + N)) :
    Sum (Edge M) (Edge N) :=
  if h : e.number.val < (M e.source e.target).coeff e.label then
    .inl ⟨e.source, e.target, e.label, ⟨e.number.val, h⟩⟩
  else .inr ⟨e.source, e.target, e.label,
    ⟨e.number.val - (M e.source e.target).coeff e.label, by
      have hn := e.number.isLt
      change e.number.val <
        (M e.source e.target + N e.source e.target).coeff e.label at hn
      rw [MonoidAlgebra.coeff_add] at hn
      change e.number.val < (M e.source e.target).coeff e.label +
        (N e.source e.target).coeff e.label at hn
      omega⟩⟩

private def joinAdd {q : ℕ} (M N : GroupMat Sign q q) :
    Sum (Edge M) (Edge N) → Edge (M + N)
  | .inl e => addLeft M N e
  | .inr e => addRight M N e

private theorem splitAdd_left {q : ℕ} (M N : GroupMat Sign q q) (e : Edge M) :
    splitAdd M N (addLeft M N e) = .inl e := by
  dsimp only [splitAdd, addLeft]
  simp only [dif_pos e.number.isLt]

private theorem splitAdd_right {q : ℕ} (M N : GroupMat Sign q q) (e : Edge N) :
    splitAdd M N (addRight M N e) = .inr e := by
  have h : ¬ (M e.source e.target).coeff e.label + e.number.val <
      (M e.source e.target).coeff e.label := by omega
  dsimp only [splitAdd, addRight]
  rw [dif_neg h]
  congr 1
  apply numbered_ext
  · rfl
  · rfl
  · rfl
  · change (M e.source e.target).coeff e.label + e.number.val -
      (M e.source e.target).coeff e.label = e.number.val
    omega

private theorem joinAdd_split {q : ℕ} (M N : GroupMat Sign q q)
    (e : Edge (M + N)) : joinAdd M N (splitAdd M N e) = e := by
  by_cases h : e.number.val < (M e.source e.target).coeff e.label
  · simp only [splitAdd, dif_pos h, joinAdd, addLeft]
  · simp only [splitAdd, dif_neg h, joinAdd, addRight]
    apply numbered_ext
    · rfl
    · rfl
    · rfl
    · change (M e.source e.target).coeff e.label +
        (e.number.val - (M e.source e.target).coeff e.label) = e.number.val
      omega

def expandedAddEquiv {q : ℕ} (M N : GroupMat Sign q q) :
    Sum (Edge M × Sign) (Edge N × Sign) ≃ Edge (M + N) × Sign where
  toFun p := match p with
    | .inl e => (addLeft M N e.1, e.2)
    | .inr e => (addRight M N e.1, e.2)
  invFun p := match splitAdd M N p.1 with
    | .inl e => .inl (e, p.2)
    | .inr e => .inr (e, p.2)
  left_inv p := by
    cases p with
    | inl p => simp only [splitAdd_left]
    | inr p => simp only [splitAdd_right]
  right_inv p := by
    have h := joinAdd_split M N p.1
    cases hs : splitAdd M N p.1 with
    | inl e =>
        simp only [hs, joinAdd] at h
        simpa only [hs] using
          (Prod.ext h rfl : (addLeft M N e, p.2) = p)
    | inr e =>
        simp only [hs, joinAdd] at h
        simpa only [hs] using
          (Prod.ext h rfl : (addRight M N e, p.2) = p)

theorem identity_coefficient {q : ℕ} (i j : Fin q) (g : Sign) :
    ((1 : GroupMat Sign q q) i j).coeff g =
      if i = j ∧ g = 1 then 1 else 0 := by
  classical
  by_cases hij : i = j <;> by_cases hg : g = 1 <;>
    simp [Matrix.one_apply, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, hij, hg, eq_comm]

def identityEdge {q : ℕ} (i : Fin q) : Edge (1 : GroupMat Sign q q) :=
  ⟨i, i, 1, ⟨0, by rw [identity_coefficient]; simp⟩⟩

private theorem identity_support {q : ℕ} (e : Edge (1 : GroupMat Sign q q)) :
    e.source = e.target ∧ e.label = 1 := by
  have hn : 0 < ((1 : GroupMat Sign q q) e.source e.target).coeff e.label :=
    lt_of_le_of_lt (Nat.zero_le e.number.val) e.number.isLt
  rw [identity_coefficient] at hn
  split_ifs at hn with h
  · exact h
  · omega

def identityExpandedEquiv (q : ℕ) :
    Vertex q ≃ Edge (1 : GroupMat Sign q q) × Sign where
  toFun v := (identityEdge v.1, v.2)
  invFun p := (p.1.source, p.2)
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨ht, hl⟩ := identity_support p.1
    have hc : ((1 : GroupMat Sign q q) p.1.source p.1.target).coeff p.1.label = 1 := by
      rw [identity_coefficient]
      simp [ht, hl]
    have hn : p.1.number.val = 0 := by have h := p.1.number.isLt; omega
    apply Prod.ext
    · apply numbered_ext
      · rfl
      · exact ht
      · exact hl.symm
      · exact hn.symm
    · rfl

/- This is now an equivalence to the actual graph of 1+M. The intervening
   Sum is merely the decoder for the disjoint coefficient number intervals. -/
private def numberedBoundaryEquiv {q : ℕ} (hq : 0 < q) :
    R q ≃ Edge ((1 : GroupMat Sign q q) + resetMatrix q) × Sign :=
  (actualBoundaryEquiv hq).trans
    ((Equiv.sumCongr (identityExpandedEquiv q) (Equiv.refl _)).trans
      (expandedAddEquiv (1 : GroupMat Sign q q) (resetMatrix q)))

private theorem numbered_boundary_source {q : ℕ} (hq : 0 < q) (r : R q) :
    (expandedGraph ((1 : GroupMat Sign q q) + resetMatrix q)).source
      (numberedBoundaryEquiv hq r) = sourceR r := by
  cases r <;> rfl

private theorem numbered_boundary_target {q : ℕ} (hq : 0 < q) (r : R q) :
    (expandedGraph ((1 : GroupMat Sign q q) + resetMatrix q)).target
      (numberedBoundaryEquiv hq r) = targetR hq r := by
  cases r <;>
    simp [numberedBoundaryEquiv, actualBoundaryEquiv, originalBoundary,
      identityExpandedEquiv, identityEdge, expandedAddEquiv, addLeft, addRight,
      actualEdgeEquiv, originalEdge, expandedGraph, targetR, flipSign]

private theorem decoded_boundary_source {q : ℕ} (hq : 0 < q)
    (r : Edge ((1 : GroupMat Sign q q) + resetMatrix q) × Sign) :
    sourceR ((numberedBoundaryEquiv hq).symm r) =
      (expandedGraph ((1 : GroupMat Sign q q) + resetMatrix q)).source r := by
  rw [← numbered_boundary_source hq, Equiv.apply_symm_apply]

private theorem decoded_boundary_target {q : ℕ} (hq : 0 < q)
    (r : Edge ((1 : GroupMat Sign q q) + resetMatrix q) × Sign) :
    targetR hq ((numberedBoundaryEquiv hq).symm r) =
      (expandedGraph ((1 : GroupMat Sign q q) + resetMatrix q)).target r := by
  rw [← numbered_boundary_target hq, Equiv.apply_symm_apply]

/-- The actual numbered local square interface, with C literally 1+M.
    Local phi and its inverse are the original endpointSquare operations. -/
def resetNumberedData (q : ℕ) (hq : 0 < q) :
    NumberedData (resetMatrix q) (resetMatrix q)
      ((1 : GroupMat Sign q q) + resetMatrix q) where
  squares := {
    source := (expandedGraph ((1 : GroupMat Sign q q) + resetMatrix q)).source
    target := (expandedGraph ((1 : GroupMat Sign q q) + resetMatrix q)).target
    sq := fun r x y s => Square hq ((numberedBoundaryEquiv hq).symm r)
      (typedEdge x) (typedEdge y) ((numberedBoundaryEquiv hq).symm s)
    endpoints := by
      intro r x y s hs
      have h := square_endpoints hs
      exact ⟨(decoded_boundary_source hq r).symm.trans
          (h.1.trans (source_typed hq x)),
        (decoded_boundary_target hq r).symm.trans
          (h.2.1.trans (source_typed hq y)),
        (decoded_boundary_source hq s).symm.trans
          (h.2.2.1.symm.trans (target_typed hq x)),
        (decoded_boundary_target hq s).symm.trans
          (h.2.2.2.trans (target_typed hq y))⟩
    back := fun x s =>
      let p := leftSquare hq (typedEdge x) ((numberedBoundaryEquiv hq).symm s)
      (numberedBoundaryEquiv hq p.1, actualEdgeEquiv hq p.2)
    back_spec := by
      intro x s hc
      have hc' : targetB hq (typedEdge x) =
          sourceR ((numberedBoundaryEquiv hq).symm s) :=
        (target_typed hq x).trans (hc.trans (decoded_boundary_source hq s).symm)
      simpa only [Equiv.symm_apply_apply, actualEdgeEquiv, Equiv.coe_fn_mk, typed_original] using
        leftSquare_spec hq (typedEdge x) ((numberedBoundaryEquiv hq).symm s) hc'
    forth := fun r y =>
      let p := rightSquare hq ((numberedBoundaryEquiv hq).symm r) (typedEdge y)
      (actualEdgeEquiv hq p.1, numberedBoundaryEquiv hq p.2)
    forth_spec := by
      intro r y hc
      have hc' : targetR hq ((numberedBoundaryEquiv hq).symm r) =
          sourceB (typedEdge y) :=
        (decoded_boundary_target hq r).trans (hc.trans (source_typed hq y).symm)
      simpa only [Equiv.symm_apply_apply, actualEdgeEquiv, Equiv.coe_fn_mk, typed_original] using
        rightSquare_spec hq ((numberedBoundaryEquiv hq).symm r) (typedEdge y) hc'
    back_unique := by
      intro r r' s x y y' hs hs'
      have hu := square_left_unique hs hs' rfl rfl
      constructor
      · exact (numberedBoundaryEquiv hq).symm.injective hu.1
      · exact (actualEdgeEquiv hq).symm.injective hu.2
    forth_unique := by
      intro r s s' x x' y hs hs'
      have hu := square_right_unique hs hs' rfl rfl
      constructor
      · exact (actualEdgeEquiv hq).symm.injective hu.1
      · exact (numberedBoundaryEquiv hq).symm.injective hu.2
    outgoing := fun v => ⟨numberedBoundaryEquiv hq (identityR v),
      numbered_boundary_source hq (identityR v)⟩
    incoming := fun v => ⟨numberedBoundaryEquiv hq (identityR v),
      numbered_boundary_target hq (identityR v)⟩ }
  source_exact _ := rfl
  target_exact _ := rfl

/- Increasing natural indices are chronological order. This conversion
   accepts every square function; it requires neither a path hypothesis nor
   a special boundary choice. Adjacent squares already supply those seams. -/
private theorem indexedStrip {q : ℕ} (hq : 0 < q) (n : ℕ)
    (x y : ℕ → B q) (b : ℕ → R q)
    (hs : ∀ i, i < n → Square hq (b i) (x i) (y i) (b (i + 1))) :
    Strip hq (List.ofFn (fun i : Fin n => x i.val)) (b 0) (b n)
      (List.ofFn (fun i : Fin n => y i.val)) := by
  induction n generalizing x y b with
  | zero => simpa using Strip.nil (hq := hq) (b 0)
  | succ n ih =>
      have ht := ih (fun i => x (i + 1)) (fun i => y (i + 1))
        (fun i => b (i + 1)) (by
          intro i hi
          exact hs (i + 1) (by omega))
      simpa [List.ofFn_succ] using Strip.cons (hs 0 (by omega)) ht

/-- Both actual q-square forgetting obligations are proved for unrestricted
    natural-indexed strips. The left terminal SOURCE is forced by the common
    last input edge; no terminal-target equality is asserted or needed. -/
def resetFiniteForgetting (q : ℕ) (hq : 0 < q) (he : Even q) :
    FiniteForgetting (resetNumberedData q hq).squares q where
  positive := hq
  left := by
    intro x y y' r r' hs hs'
    have ht := indexedStrip hq q (fun i => typedEdge (x i))
      (fun i => typedEdge (y i)) (fun i => (numberedBoundaryEquiv hq).symm (r i)) hs
    have ht' := indexedStrip hq q (fun i => typedEdge (x i))
      (fun i => typedEdge (y' i)) (fun i => (numberedBoundaryEquiv hq).symm (r' i)) hs'
    have hc : sourceR ((numberedBoundaryEquiv hq).symm (r q)) =
        sourceR ((numberedBoundaryEquiv hq).symm (r' q)) := by
      have h := (square_endpoints (hs (q - 1) (by omega))).2.2.1
      have h' := (square_endpoints (hs' (q - 1) (by omega))).2.2.1
      have hn : q - 1 + 1 = q := by omega
      simpa only [hn] using h.symm.trans h'
    apply (numberedBoundaryEquiv hq).symm.injective
    exact (actualBoundaryEquiv hq).injective
      (strip_left_forgets he ht ht' (by simp) hc)
  right := by
    intro x x' y r r' hs hs'
    have ht := indexedStrip hq q (fun i => typedEdge (x i))
      (fun i => typedEdge (y i)) (fun i => (numberedBoundaryEquiv hq).symm (r i)) hs
    have ht' := indexedStrip hq q (fun i => typedEdge (x' i))
      (fun i => typedEdge (y i)) (fun i => (numberedBoundaryEquiv hq).symm (r' i)) hs'
    apply (numberedBoundaryEquiv hq).symm.injective
    exact (actualBoundaryEquiv hq).injective
      (strip_right_forgets he ht ht' (by simp))

/-- Every expanded reset vertex has an actual incoming and outgoing edge.
    Incoming to suffix zero uses a reset; incoming to a positive suffix uses
    its predecessor advance. Absolute signs are part of both witnesses. -/
theorem reset_expanded_essential (q : ℕ) (hq : 0 < q) :
    Essential (expandedGraph (resetMatrix q)) := by
  constructor
  · rintro ⟨i, h⟩
    exact ⟨originalEdge hq (.f i h), actual_source hq (.f i h)⟩
  · rintro ⟨j, h⟩
    by_cases hj : j.val = 0
    · have hz : zero hq = j := Fin.ext hj.symm
      refine ⟨originalEdge hq (.f (zero hq) (flipSign h)), ?_⟩
      rw [actual_target]
      cases h <;> simp only [targetB, flipSign, hz] <;> rfl
    · let i : Fin q := ⟨j.val - 1, by omega⟩
      have hi : i.val + 1 < q := by dsimp [i]; omega
      refine ⟨originalEdge hq (.a i h hi), ?_⟩
      rw [actual_target]
      apply Prod.ext
      · apply Fin.ext
        dsimp [targetB, next, i]
        omega
      · rfl

/- A local window of an arbitrary generic full lift is a private Strip.
   Boundary i is at k+i-1, immediately before edge k+i. -/
private theorem fullSquare_window {q : ℕ} (hq : 0 < q)
    (P : (resetNumberedData q hq).squares.FullSquare) (k : ℤ) (n : ℕ) :
    Strip hq (wordList (historyWindow (expandedGraph (resetMatrix q)) P.left k n))
      ((numberedBoundaryEquiv hq).symm (P.boundary (k - 1)))
      ((numberedBoundaryEquiv hq).symm (P.boundary (k + (n : ℤ) - 1)))
      (wordList (historyWindow (expandedGraph (resetMatrix q)) P.right k n)) := by
  have hs := indexedStrip hq n
    (fun i => typedEdge (P.left.val (k + (i : ℤ))))
    (fun i => typedEdge (P.right.val (k + (i : ℤ))))
    (fun i => (numberedBoundaryEquiv hq).symm (P.boundary (k + (i : ℤ) - 1)))
    (by
      intro i hi
      have ht : k + ((i + 1 : ℕ) : ℤ) - 1 = k + (i : ℤ) := by omega
      have hp := P.square (k + (i : ℤ))
      simpa only [resetNumberedData, ht] using hp)
  simpa only [wordList, historyWindow, Int.natCast_zero, add_zero] using hs

private theorem generic_forward_coordinate (q : ℕ) (hq : 0 < q) (he : Even q)
    (x : History (expandedGraph (resetMatrix q))) (k : ℤ) :
    ((resetNumberedData q hq).squares.H (resetFiniteForgetting q hq he) x).val k =
      forwardTable hq (historyWindow (expandedGraph (resetMatrix q)) x k (q + 1)) := by
  let P := (resetNumberedData q hq).squares.leftLift (resetFiniteForgetting q hq he) x
  change P.right.val k = _
  have hs := fullSquare_window hq P k (q + 1)
  have ht := forwardTable_of_strip he
    (historyWindow (expandedGraph (resetMatrix q)) x k (q + 1)) hs
  rw [wordList_pick hq _ 0 (by omega), original_typed] at ht
  simpa only [historyWindow, Int.natCast_zero, add_zero] using ht.symm

end Alternating

/-- The exact family table input on the original numbered expanded graph.
    The forward and backward windows retain all original edge coordinates. -/
def resetAlternatingTablePair (q : ℕ) (hq : 0 < q) :
    FiniteWindowTableCriterion.TablePair
      (expandedGraph (resetMatrix q)) (expandedGraph (resetMatrix q)) 0 q q 0 where
  f w := Alternating.forwardTable hq {
    edge j := w.edge ⟨j.val, by omega⟩
    legal j hj := w.legal ⟨j.val, by omega⟩
      (by simpa only [Fin.val_mk, Nat.zero_add] using hj) }
  g w := Alternating.backwardTable hq w

/-- Uniform guarded alternating-square tables for every positive even q.
    Both seams and both round trips come from full q-step boundary contraction
    and overlapping strips on the actual numbered graph. -/
theorem reset_alternating_tables_local (q : ℕ) (hq : 0 < q) (he : Even q) :
    FiniteWindowTableCriterion.LocalCriterion (resetAlternatingTablePair q hq) := by
  have hf := Alternating.forward_seam hq he
  have hg := Alternating.backward_seam hq he
  have hlocal : FiniteWindowTableCriterion.LocalCriterion (resetAlternatingTablePair q hq) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro w
      let wc : EssentialWordRealization.LegalWord
          (expandedGraph (resetMatrix q)) (q + 1 + 1) := {
        edge j := w.edge ⟨j.val, by omega⟩
        legal j hj := w.legal ⟨j.val, by omega⟩
          (by simp only [Fin.val_mk]; omega) }
      simpa [resetAlternatingTablePair, wc, Alternating.forwardTable,
        Alternating.wordList, FiniteWindowTableCriterion.sliceWord,
        Nat.zero_add, Nat.add_zero] using hf wc
    · simpa [resetAlternatingTablePair, Nat.zero_add, Nat.add_zero] using hg
    · intro w
      let wc : EssentialWordRealization.LegalWord
          (expandedGraph (resetMatrix q)) (q + q + 1) := {
        edge j := w.edge ⟨j.val, by omega⟩
        legal j hj := w.legal ⟨j.val, by omega⟩
          (by simp only [Fin.val_mk]; omega) }
      simpa [resetAlternatingTablePair, wc, Alternating.forwardTable,
        Alternating.backwardTable, Alternating.wordList,
        FiniteWindowTableCriterion.mapBlock, FiniteWindowTableCriterion.sliceWord,
        Nat.zero_add, Nat.add_zero] using
        Alternating.forward_roundtrip hq he hf wc
    · intro w
      let wc : EssentialWordRealization.LegalWord
          (expandedGraph (resetMatrix q)) (q + q + 1) := {
        edge j := w.edge ⟨j.val, by omega⟩
        legal j hj := w.legal ⟨j.val, by omega⟩
          (by simp only [Fin.val_mk]; omega) }
      simpa [resetAlternatingTablePair, wc, Alternating.forwardTable,
        Alternating.backwardTable, Alternating.wordList,
        FiniteWindowTableCriterion.mapBlock, FiniteWindowTableCriterion.sliceWord,
        Nat.zero_add, Nat.add_zero] using
        Alternating.backward_roundtrip hq he hg wc
  exact hlocal

/- The full square lift agrees with the finite tables on every legal history.
   Its same-cut image retains the complete numbered boundary and every future. -/

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
open D5.S3.ConceptDynamics.Coding.SameCutWholeRayBridge
open D5.S3.ConceptDynamics.Coding.NumberedSameCutWholeRay

/-- The generic square-lift H is exactly the original table map on EVERY
    legal history. The proof compares its q+1-square window with the original
    private sweep via first_output_independent / forwardTable_of_strip. -/
theorem reset_generic_H_eq_applyTable (q : ℕ) (hq : 0 < q) (he : Even q)
    (x : History (expandedGraph (resetMatrix q))) :
    (Alternating.resetNumberedData q hq).squares.H
        (Alternating.resetFiniteForgetting q hq he) x =
      applyTable (expandedGraph (resetMatrix q)) (expandedGraph (resetMatrix q))
        (resetAlternatingTablePair q hq).f
        (reset_alternating_tables_local q hq he).seamG x := by
  apply Subtype.ext
  funext k
  simpa [applyTable, resetAlternatingTablePair, Alternating.forwardTable,
    Alternating.wordList, historyWindow, Nat.zero_add, Nat.add_zero,
    Int.natCast_zero, sub_zero] using Alternating.generic_forward_coordinate q hq he x k

/-- The homeomorphism is the generic construction from actual local squares
    and proved finite forgetting, on the original product/subtype topology. -/
def resetAlternatingWholeRayHomeomorph (q : ℕ) (hq : 0 < q) (he : Even q) :
    History (expandedGraph (resetMatrix q)) ≃ₜ History (expandedGraph (resetMatrix q)) :=
  (Alternating.resetNumberedData q hq).squares.historyHomeomorph
    (Alternating.resetFiniteForgetting q hq he)

/-- A full legal representative of the prescribed right past, indexed by a
    FULL numbered outgoing edge of 1+M with its absolute group coordinate. -/
def resetRayRepresentative (q : ℕ) (hq : 0 < q)
    (alpha : History (expandedGraph (resetMatrix q))) (n : ℤ)
    (r : {r : Edge ((1 : GroupMat Sign q q) + resetMatrix q) × Sign //
      (expandedGraph ((1 : GroupMat Sign q q) + resetMatrix q)).source r =
        (expandedGraph (resetMatrix q)).target (alpha.val n)}) :
    History (expandedGraph (resetMatrix q)) :=
  (Alternating.resetNumberedData q hq).beta
    (Alternating.reset_expanded_essential q hq) alpha n r

/-- For every positive even q, every alpha and every integer cut n, the
    exact generic/table map sends the ENTIRE left ray to the disjoint union
    indexed by all actual numbered outgoing C edges. Each component ends at
    the actual target of its indexing edge. Every legal future has a preimage
    with the original alpha past and precisely that numbered boundary at n.
    The cut and all boundary endpoints are those of the original graph. -/
theorem reset_even_same_cut_whole_rays (q : ℕ) (hq : 0 < q) (he : Even q)
    (alpha : History (expandedGraph (resetMatrix q))) (n : ℤ) :
    let Out := {r : Edge ((1 : GroupMat Sign q q) + resetMatrix q) × Sign //
      (expandedGraph ((1 : GroupMat Sign q q) + resetMatrix q)).source r =
        (expandedGraph (resetMatrix q)).target (alpha.val n)}
    (resetAlternatingWholeRayHomeomorph q hq he ''
        {x : History (expandedGraph (resetMatrix q)) |
          ∀ k, k ≤ n → x.val k = alpha.val k} =
      ⋃ r : Out, {y : History (expandedGraph (resetMatrix q)) |
        ∀ k, k ≤ n → y.val k = (resetRayRepresentative q hq alpha n r).val k}) ∧
    (∀ r : Out,
      (expandedGraph (resetMatrix q)).target
          ((resetRayRepresentative q hq alpha n r).val n) =
        (expandedGraph ((1 : GroupMat Sign q q) + resetMatrix q)).target r.val) ∧
    (∀ r s : Out, r ≠ s →
      Disjoint
        {y : History (expandedGraph (resetMatrix q)) |
          ∀ k, k ≤ n → y.val k = (resetRayRepresentative q hq alpha n r).val k}
        {y : History (expandedGraph (resetMatrix q)) |
          ∀ k, k ≤ n → y.val k = (resetRayRepresentative q hq alpha n s).val k}) ∧
    (∀ r : Out, ∀ y : History (expandedGraph (resetMatrix q)),
      (∀ k, k ≤ n → y.val k = (resetRayRepresentative q hq alpha n r).val k) →
      ∃ x : History (expandedGraph (resetMatrix q)),
        (∀ k, k ≤ n → x.val k = alpha.val k) ∧
        resetAlternatingWholeRayHomeomorph q hq he x = y ∧
        ((Alternating.resetNumberedData q hq).squares.leftLift
          (Alternating.resetFiniteForgetting q hq he) x).boundary n = r.val) := by
  dsimp only
  let T := Alternating.resetNumberedData q hq
  let K := Alternating.resetFiniteForgetting q hq he
  let hM := Alternating.reset_expanded_essential q hq
  exact ⟨T.numbered_same_cut_whole_ray_image K hM alpha n,
    T.numbered_beta_endpoint hM alpha n,
    fun r s hrs => T.numbered_components_disjoint K hM alpha n hrs,
    fun r y hy => T.numbered_arbitrary_future_preimage K hM alpha n r y hy⟩


end D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
