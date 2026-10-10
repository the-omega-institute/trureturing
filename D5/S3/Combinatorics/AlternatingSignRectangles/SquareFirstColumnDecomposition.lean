/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.avoidingASM_card_schroder; premises=D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.AvoidASM_zero_card
   digest: SquareFirstColumnDecomposition for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
tailRow_strictMono: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_first_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_right_col
tailCol_strictMono: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_lower_row, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_top_row
tailRow_range: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_right_col
tailCol_range: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_empty_original, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_lower_row
residualRect_noncorner: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_empty_original, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_first_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_lower_row, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_right_col, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_top_row
line_of_unique_ones: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_first_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_top_row
line_tail_zero_after_complete: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
residualRect_first_col_line: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_first_col_line
residualRect_top_row: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_top_row
residualRect_lower_row: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
residualRect_right_col: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.one_before_minus
residualRect_isASR: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_first_col_line
sum_cut: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_colSum
residualRect_colSum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
residualRect_empty_original: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_top_row
residualRect_extAvoids: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_extAvoids
castRect_isASR: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_isASR
castRect_extAvoids: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_extAvoids
castRect_nonemptyRows: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_nonemptyRows
mergeRectAt_isASR: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.concat_complete_opposite
mergeRectAt_extAvoids: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
mergeRectAt_nonemptyRows: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.extractColumnFibre, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeColumnFibre
mergeRectAt_top: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_before, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_prefixSquare
mergeRectAt_lower: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_residual
mergeRectAt_first_col: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeColumnFibre
mergeRectAt_before: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeColumnFibre
mergeRectAt_prefixSquare: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.firstColumnFactorEquiv
mergeRectAt_residual: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.firstColumnFactorEquiv
mergeRectAt_reconstruct: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_reconstruct
firstColumnFactor_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_first_col_line
squareCount_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
AvoidASM_zero_card: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.avoidingASM_card_schroder
asm_extAvoids: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.asmColumnFibreEquiv
asm_first_column_one: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.asmPivot, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.asmPivot_spec
asmNonzeroFibre_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_first_col_line
Direct frozen dependencies: none; the ASR prerequisites are same-delivery content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private def tailRow {r : ℕ} (i : Fin r) (u : Fin (r-i.val)) : Fin r :=
  Fin.cast (by have := i.isLt; omega : i.val+(r-i.val)=r) (Fin.natAdd i.val u)

private def tailCol {k p : ℕ} (hp : p < k) (c : Fin (k-p)) : Fin k :=
  Fin.cast (by omega : p+(k-p)=k) (Fin.natAdd p c)

private lemma tailRow_strictMono {r : ℕ} (i : Fin r) : StrictMono (tailRow i) := by
  exact (Fin.cast_strictMono (by have := i.isLt; omega)).comp (Fin.strictMono_natAdd i.val)

private lemma tailCol_strictMono {k p : ℕ} (hp : p < k) : StrictMono (tailCol hp) := by
  exact (Fin.cast_strictMono (by omega)).comp (Fin.strictMono_natAdd p)

private lemma tailRow_range {r : ℕ} (i v : Fin r) :
    (∃ u, tailRow i u=v) ↔ i.val ≤ v.val := by
  constructor
  · rintro ⟨u,rfl⟩
    change i.val ≤ i.val+u.val
    omega
  · intro hv
    refine ⟨⟨v.val-i.val,by have := v.isLt; omega⟩,?_⟩
    apply Fin.ext
    change i.val+(v.val-i.val)=v.val
    omega

private lemma tailCol_range {k p : ℕ} (hp : p < k) (c : Fin k) :
    (∃ x, tailCol hp x=c) ↔ p ≤ c.val := by
  constructor
  · rintro ⟨x,rfl⟩
    change p ≤ p+x.val
    omega
  · intro hc
    refine ⟨⟨c.val-p,by have := c.isLt; omega⟩,?_⟩
    apply Fin.ext
    change p+(c.val-p)=c.val
    omega

private def residualRect {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (i : Fin r) (hp : i.val < k) : Matrix (Fin (r-i.val)) (Fin (k-i.val)) SignType :=
  fun u c => if u.val=0 ∧ c.val=0 then incCorner (R (tailRow i u) (tailCol hp c))
    else R (tailRow i u) (tailCol hp c)

private lemma residualRect_noncorner {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (i : Fin r) (hp : i.val < k) (u : Fin (r-i.val)) (c : Fin (k-i.val))
    (hn : u.val ≠ 0 ∨ c.val ≠ 0) :
    residualRect R i hp u c = R (tailRow i u) (tailCol hp c) := by
  simp [residualRect,show ¬ (u.val=0 ∧ c.val=0) by omega]

private lemma line_of_unique_ones {n : ℕ} (a : Fin n → SignType)
    (hn : ∀ x, a x ≠ -1) (hu : ∀ x y, a x=1 → a y=1 → x=y) :
    Alternates a ∧ StartsOne a ∧ EndsOne a := by
  have hone (x : Fin n) (hx : a x ≠ 0) : a x=1 := by
    have hm := hn x
    cases hs : a x <;> simp_all
  refine ⟨?_,?_,?_⟩
  · intro x y hxy hx hy _
    exact (ne_of_lt hxy (hu x y (hone x hx) (hone y hy))).elim
  · intro x hx _
    exact hone x hx
  · intro x hx _
    exact hone x hx

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma line_tail_zero_after_complete {n p : ℕ} (hp : p ≤ n) (a : Fin n → SignType)
    (ha : Alternates a) (hs : StartsOne a)
    (ht : (∑ u : Fin p, (a (Fin.castLE hp u) : ℤ))=1)
    (hn : ∀ v, p ≤ v.val → a v ≠ -1) : ∀ v, p ≤ v.val → a v=0 := by
  have hl := prefix_line hp a ha hs
  rcases alternating_line_state (fun u => a (Fin.castLE hp u)) hl.1 hl.2 with
    ⟨hz,hzsum⟩ | ⟨u,hu,htail,huSum⟩
  · exact ((by decide : (0 : ℤ) ≠ 1) (hzsum.symm.trans ht)).elim
  · have hone : a (Fin.castLE hp u)=1 := by
      by_contra hn1
      simp only [hn1,if_false] at huSum
      omega
    intro v hv
    by_contra hv0
    have hv1 : a v=1 := by have := hn v hv; cases he : a v <;> simp_all
    obtain ⟨z,huz,_,hzm⟩ := minus_between_ones a ha (Fin.castLE hp u) v
      (by change u.val < v.val; have := u.isLt; omega) hone hv1
    by_cases hz : z.val < p
    · have hzt := htail ⟨z.val,hz⟩ huz
      have heq : Fin.castLE hp (⟨z.val,hz⟩ : Fin p)=z := by apply Fin.ext; rfl
      change a (Fin.castLE hp ⟨z.val,hz⟩)=0 at hzt
      rw [heq,hzm] at hzt
      exact (by decide : (-1 : SignType) ≠ 0) hzt
    · exact hn z (by omega) hzm

private lemma residualRect_first_col_line {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩=1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0) (hi : 0 < i.val) :
    let hp : i.val < k := by have := prefix_width R hR hk i hfirst hbefore; omega
    Alternates (fun u => residualRect R i hp u ⟨0,by omega⟩) ∧
      StartsOne (fun u => residualRect R i hp u ⟨0,by omega⟩) := by
  dsimp
  let hp : i.val < k := by have := prefix_width R hR hk i hfirst hbefore; omega
  let p : Fin k := ⟨i.val,hp⟩
  let B := residualRect R i hp
  have hcol (u : Fin (r-i.val)) : tailCol hp (⟨0,by omega⟩ : Fin (k-i.val))=p := by
    apply Fin.ext; simp [tailCol,p]
  have hnm (u : Fin (r-i.val)) : B u ⟨0,by omega⟩ ≠ -1 := by
    by_cases hu : u.val=0
    · simp only [B,residualRect,hu,true_and,Fin.val_mk,if_true,incCorner]
      split_ifs <;> decide
    · rw [show B u ⟨0,by omega⟩=R (tailRow i u) p from by
        change residualRect R i hp u _ = _
        rw [residualRect_noncorner R i hp u _ (Or.inl hu),hcol u]]
      exact below_pivot_end_not_minus R hR he hk i (tailRow i u) hfirst hbefore hi
        (by change i.val < i.val+u.val; omega)
  have hcorner : R i p ≠ 1 := pivot_not_one_at_prefix_end R hR he hk i hfirst hbefore hi
  have htop (u : Fin (r-i.val)) (hu : u.val=0) : B u ⟨0,by omega⟩=incCorner (R i p) := by
    have heq : tailRow i u=i := by apply Fin.ext; simp [tailRow,hu]
    simp [B,residualRect,hu,hcol u,heq]
  have hother (u : Fin (r-i.val)) (hu : u.val ≠ 0) : B u ⟨0,by omega⟩=R (tailRow i u) p := by
    change residualRect R i hp u _ = _
    rw [residualRect_noncorner R i hp u _ (Or.inl hu),hcol u]
  have huniq (u v : Fin (r-i.val)) (hu : B u ⟨0,by omega⟩=1)
      (hv : B v ⟨0,by omega⟩=1) : u=v := by
    by_cases hzero : R i p=0
    · have hprefix : (∑ x : Fin i.val, (R (Fin.castLE (Nat.le_of_lt i.isLt) x) p : ℤ))=1 := by
        have hsum := prefix_shift_column_sum R hR he hk i hfirst hbefore
          (⟨i.val-1,by omega⟩ : Fin i.val)
        have heq : shiftCol (prefix_width R hR hk i hfirst hbefore) (⟨i.val-1,by omega⟩ : Fin i.val)=p := by
          apply Fin.ext; simp [shiftCol,p]; omega
        simpa only [heq,colSum,topRows] using hsum
      have hn (w : Fin r) (hw : i.val ≤ w.val) : R w p ≠ -1 := by
        by_cases hEq : w=i
        · simp [hEq,hzero]
        · apply below_pivot_end_not_minus R hR he hk i w hfirst hbefore hi
          have hne : w.val ≠ i.val := by intro hv; exact hEq (Fin.ext hv)
          omega
      have hz := line_tail_zero_after_complete (Nat.le_of_lt i.isLt) (fun w => R w p)
        (hR.2 p).1 (hR.2 p).2 hprefix hn
      have hu0 : u.val=0 := by
        by_contra hun
        rw [hother u hun,hz (tailRow i u) (by change i.val ≤ i.val+u.val; omega)] at hu
        exact (by decide : (0 : SignType) ≠ 1) hu
      have hv0 : v.val=0 := by
        by_contra hvn
        rw [hother v hvn,hz (tailRow i v) (by change i.val ≤ i.val+v.val; omega)] at hv
        exact (by decide : (0 : SignType) ≠ 1) hv
      apply Fin.ext
      omega
    · have hm : R i p=-1 := by cases h : R i p <;> simp_all
      have hu0 : u.val ≠ 0 := by
        intro h
        rw [htop u h,hm] at hu
        simp [incCorner] at hu
      have hv0 : v.val ≠ 0 := by
        intro h
        rw [htop v h,hm] at hv
        simp [incCorner] at hv
      rw [hother u hu0] at hu
      rw [hother v hv0] at hv
      suffices heq : tailRow i u=tailRow i v from (tailRow_strictMono i).injective heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨z,huz,_,hzm⟩ := minus_between_ones (fun w => R w p) (hR.2 p).1
          (tailRow i u) (tailRow i v) hlt hu hv
        exact below_pivot_end_not_minus R hR he hk i z hfirst hbefore hi
          (by change i.val+u.val < z.val at huz; omega) hzm
      · obtain ⟨z,hvz,_,hzm⟩ := minus_between_ones (fun w => R w p) (hR.2 p).1
          (tailRow i v) (tailRow i u) hgt hv hu
        exact below_pivot_end_not_minus R hR he hk i z hfirst hbefore hi
          (by change i.val+v.val < z.val at hvz; omega) hzm
  exact ⟨(line_of_unique_ones _ hnm huniq).1,(line_of_unique_ones _ hnm huniq).2.1⟩

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma residualRect_top_row {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩=1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0) (hi : 0 < i.val) :
    let hp : i.val < k := by have := prefix_width R hR hk i hfirst hbefore; omega
    let u : Fin (r-i.val) := ⟨0,by have := i.isLt; omega⟩
    (Alternates (residualRect R i hp u) ∧ StartsOne (residualRect R i hp u) ∧
      EndsOne (residualRect R i hp u)) ∧ ∃ c, residualRect R i hp u c ≠ 0 := by
  dsimp
  let hp : i.val < k := by have := prefix_width R hR hk i hfirst hbefore; omega
  let u : Fin (r-i.val) := ⟨0,by have := i.isLt; omega⟩
  let p : Fin k := ⟨i.val,hp⟩
  let B := residualRect R i hp
  change (Alternates (B u) ∧ StartsOne (B u) ∧ EndsOne (B u)) ∧ ∃ c, B u c ≠ 0
  have hrow : tailRow i u=i := by apply Fin.ext; simp [tailRow,u]
  have hcol : tailCol hp (⟨0,by omega⟩ : Fin (k-i.val))=p := by apply Fin.ext; simp [tailCol,p]
  have htop : B u ⟨0,by omega⟩=incCorner (R i p) := by
    simp [B,residualRect,u,hrow,hcol]
  have hother (c : Fin (k-i.val)) (hc : c.val ≠ 0) : B u c=R i (tailCol hp c) := by
    change residualRect R i hp u c= _
    rw [residualRect_noncorner R i hp u c (Or.inr hc),hrow]
  have hnm (c : Fin (k-i.val)) : B u c ≠ -1 := by
    by_cases hc : c.val=0
    · have heq : c=⟨0,by omega⟩ := Fin.ext hc
      rw [heq,htop]
      unfold incCorner
      split_ifs <;> decide
    · rw [hother c hc]
      exact pivot_no_minus_after_prefix R hR he hk i hfirst hbefore (tailCol hp c)
        (by change i.val < i.val+c.val; omega)
  by_cases hm : R i p=-1
  · obtain ⟨q,hq,hqs⟩ := pivot_row_right_singleton R hR he hk i hfirst hbefore hm
    let c : Fin (k-i.val) := ⟨q.val-i.val,by have := q.isLt; omega⟩
    have hc0 : c.val ≠ 0 := by change q.val-i.val ≠ 0; omega
    have hce : tailCol hp c=q := by apply Fin.ext; simp [tailCol,c]; omega
    have hcone : B u c=1 := by rw [hother c hc0,hce,hqs q hq]; simp
    have huniq (a b : Fin (k-i.val)) (ha : B u a=1) (hb : B u b=1) : a=b := by
      have ha0 : a.val ≠ 0 := by
        intro h
        have heq : a=⟨0,by omega⟩ := Fin.ext h
        rw [heq,htop,hm] at ha
        simp [incCorner] at ha
      have hb0 : b.val ≠ 0 := by
        intro h
        have heq : b=⟨0,by omega⟩ := Fin.ext h
        rw [heq,htop,hm] at hb
        simp [incCorner] at hb
      rw [hother a ha0,hqs _ (by change i.val < i.val+a.val; omega)] at ha
      rw [hother b hb0,hqs _ (by change i.val < i.val+b.val; omega)] at hb
      have haq : tailCol hp a=q := by simpa using ha
      have hbq : tailCol hp b=q := by simpa using hb
      exact (tailCol_strictMono hp).injective (haq.trans hbq.symm)
    exact ⟨line_of_unique_ones _ hnm huniq,⟨c,by rw [hcone]; decide⟩⟩
  · have hs := pivot_row_singleton_if_no_minus R hR he hk i hfirst hbefore hm
    have hcorner : R i p=0 := by simpa [p,show i.val ≠ 0 by omega] using hs p
    have htopone : B u ⟨0,by omega⟩=1 := by rw [htop,hcorner]; simp [incCorner]
    have hzero (c : Fin (k-i.val)) (hc : c.val ≠ 0) : B u c=0 := by
      rw [hother c hc,hs]
      simp [tailCol,Nat.ne_of_gt hi,hc]
    have huniq (a b : Fin (k-i.val)) (ha : B u a=1) (hb : B u b=1) : a=b := by
      have ha0 : a.val=0 := by by_contra hn; rw [hzero a hn] at ha; cases ha
      have hb0 : b.val=0 := by by_contra hn; rw [hzero b hn] at hb; cases hb
      apply Fin.ext
      omega
    exact ⟨line_of_unique_ones _ hnm huniq,⟨⟨0,by omega⟩,by rw [htopone]; decide⟩⟩

private lemma residualRect_lower_row {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩=1)
    (hbefore : ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0) (hp : i.val < k)
    (u : Fin (r-i.val)) (hu : u.val ≠ 0) :
    Alternates (residualRect R i hp u) ∧ StartsOne (residualRect R i hp u) ∧
      EndsOne (residualRect R i hp u) := by
  have hval (c : Fin (k-i.val)) : R (tailRow i u) (tailCol hp c)=residualRect R i hp u c :=
    (residualRect_noncorner R i hp u c (Or.inl hu)).symm
  have hout (c : Fin k) (hc : ¬ ∃ x, tailCol hp x=c) : R (tailRow i u) c=0 := by
    have hcp : c.val < i.val := by have := (tailCol_range hp c).not.mp hc; omega
    by_cases hc0 : c.val=0
    · have heq : c=⟨0,hk⟩ := Fin.ext hc0
      rw [heq,first_column_zero_except_pivot R hR hk i hfirst]
      have hne : tailRow i u ≠ i := by
        intro heq
        have hv := congrArg Fin.val heq
        change i.val+u.val=i.val at hv
        omega
      simp [hne]
    · exact below_prefix_interior_zero R hR he hk i (tailRow i u) hfirst hbefore
        (by change i.val ≤ i.val+u.val; omega) c (by omega) hcp
  have hl := line_restrict (residualRect R i hp u) (R (tailRow i u)) (tailCol hp)
    (tailCol_strictMono hp) hval hout (hR.1 _).1 (hR.1 _).2.1
  exact ⟨hl.1,hl.2,ends_restrict _ _ _ (tailCol_strictMono hp) hval hout (hR.1 _).2.2⟩

private lemma residualRect_right_col {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩=1)
    (hbefore : ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0) (hp : i.val < k)
    (c : Fin (k-i.val)) (hc : c.val ≠ 0) :
    Alternates (fun u => residualRect R i hp u c) ∧ StartsOne (fun u => residualRect R i hp u c) := by
  have hval (u : Fin (r-i.val)) : R (tailRow i u) (tailCol hp c)=residualRect R i hp u c :=
    (residualRect_noncorner R i hp u c (Or.inr hc)).symm
  have hout (v : Fin r) (hv : ¬ ∃ x, tailRow i x=v) : R v (tailCol hp c)=0 := by
    have hvi : v.val < i.val := by have := (tailRow_range i v).not.mp hv; omega
    exact prefix_outside_zero R hR he hk i v (tailCol hp c) hvi hfirst
      (by change i.val < i.val+c.val; omega) hbefore
  exact line_restrict _ _ (tailRow i) (tailRow_strictMono i) hval hout
    (hR.2 _).1 (hR.2 _).2

private lemma residualRect_isASR {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩=1)
    (hbefore : ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0) (hi : 0 < i.val) :
    let hp : i.val < k := by have := prefix_width R hR hk i hfirst hbefore; omega
    IsASR (residualRect R i hp) := by
  dsimp
  refine ⟨?_,?_⟩
  · intro u
    by_cases hu : u.val=0
    · have heq : u=⟨0,by have := i.isLt; omega⟩ := Fin.ext hu
      rw [heq]
      exact (residualRect_top_row R hR he hk i hfirst hbefore hi).1
    · exact residualRect_lower_row R hR he hk i hfirst hbefore _ u hu
  · intro c
    by_cases hc : c.val=0
    · have heq : c=⟨0,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ := Fin.ext hc
      rw [heq]
      exact residualRect_first_col_line R hR he hk i hfirst hbefore hi
    · exact residualRect_right_col R hR he hk i hfirst hbefore _ c hc

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma sum_cut {n p : ℕ} (hp : p ≤ n) (a : Fin n → ℤ) :
    (∑ u, a u) =
      (∑ u : Fin p, a ⟨u.val,by have := u.isLt; omega⟩) +
      ∑ v : Fin (n-p), a ⟨p+v.val,by have := v.isLt; omega⟩ := by
  let hn : p+(n-p)=n := by omega
  let b : Fin (p+(n-p)) → ℤ := fun u => a (Fin.cast hn u)
  have he : (∑ u, b u) = ∑ u, a u := by
    apply sum_bij (fun u _ => Fin.cast hn u)
    · intro _ _; exact mem_univ _
    · intro u _ v _ heq; exact Fin.cast_injective hn heq
    · intro u _; exact ⟨Fin.cast hn.symm u,mem_univ _,by simp⟩
    · intro _ _; rfl
  rw [←he,Fin.sum_univ_add]
  rfl

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma residualRect_colSum {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩=1)
    (hbefore : ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0) (hi : 0 < i.val)
    (hp : i.val < k) (c : Fin (k-i.val)) :
    colSum (residualRect R i hp) c = colSum R (tailCol hp c) := by
  classical
  by_cases hc : c.val=0
  · have hce : c=⟨0,by omega⟩ := Fin.ext hc
    rw [hce]
    let p : Fin k := ⟨i.val,hp⟩
    have hcol : tailCol hp (⟨0,by omega⟩ : Fin (k-i.val))=p := by apply Fin.ext; simp [tailCol,p]
    have hcorner : R i p ≠ 1 := pivot_not_one_at_prefix_end R hR he hk i hfirst hbefore hi
    have hval (u : Fin (r-i.val)) : (residualRect R i hp u ⟨0,by omega⟩ : ℤ)=
        (R (tailRow i u) p : ℤ) + if u=(⟨0,by have := i.isLt; omega⟩ : Fin (r-i.val)) then 1 else 0 := by
      by_cases hu : u.val=0
      · have hrw : tailRow i u=i := by apply Fin.ext; simp [tailRow,hu]
        have hue : u=(⟨0,by have := i.isLt; omega⟩ : Fin (r-i.val)) := Fin.ext hu
        simp only [residualRect,hu,Fin.val_mk,true_and,if_true,hcol,hrw,hue]
        exact incCorner_cast _ hcorner
      · have hun : u ≠ (⟨0,by have := i.isLt; omega⟩ : Fin (r-i.val)) := by
          intro heq; exact hu (by simpa using congrArg Fin.val heq)
        rw [residualRect_noncorner R i hp u _ (Or.inl hu),hcol]
        simp [hun]
    have hprefix : (∑ x : Fin i.val, (R (Fin.castLE (Nat.le_of_lt i.isLt) x) p : ℤ))=1 := by
      have hsum := prefix_shift_column_sum R hR he hk i hfirst hbefore
        (⟨i.val-1,by omega⟩ : Fin i.val)
      have heq : shiftCol (prefix_width R hR hk i hfirst hbefore) (⟨i.val-1,by omega⟩ : Fin i.val)=p := by
        apply Fin.ext; simp [shiftCol,p]; omega
      simpa only [heq,colSum,topRows] using hsum
    have hsplit := sum_cut (Nat.le_of_lt i.isLt) (fun u => (R u p : ℤ))
    change colSum R p = (∑ x : Fin i.val, (R (Fin.castLE (Nat.le_of_lt i.isLt) x) p : ℤ)) +
      ∑ u : Fin (r-i.val), (R (tailRow i u) p : ℤ) at hsplit
    rw [hprefix] at hsplit
    unfold colSum at hsplit
    rw [hcol]
    unfold colSum
    simp_rw [hval]
    rw [sum_add_distrib]
    simp only [sum_ite_eq',mem_univ,if_true]
    omega
  · have hval (u : Fin (r-i.val)) : R (tailRow i u) (tailCol hp c)=residualRect R i hp u c :=
      (residualRect_noncorner R i hp u c (Or.inr hc)).symm
    have hout (v : Fin r) (hv : ¬ ∃ x, tailRow i x=v) : R v (tailCol hp c)=0 := by
      have hvi : v.val < i.val := by have := (tailRow_range i v).not.mp hv; omega
      exact prefix_outside_zero R hR he hk i v (tailCol hp c) hvi hfirst
        (by change i.val < i.val+c.val; omega) hbefore
    exact sum_embed _ _ (tailRow i) (tailRow_strictMono i) hval hout

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma residualRect_empty_original {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩=1)
    (hbefore : ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0) (hi : 0 < i.val)
    (hp : i.val < k) (u : Fin (r-i.val))
    (hempty : ∀ c, residualRect R i hp u c=0) : ∀ c, R (tailRow i u) c=0 := by
  have hu : u.val ≠ 0 := by
    intro hu0
    have heq : u=⟨0,by have := i.isLt; omega⟩ := Fin.ext hu0
    obtain ⟨c,hc⟩ := (residualRect_top_row R hR he hk i hfirst hbefore hi).2
    exact hc (by simpa only [heq] using hempty c)
  intro c
  by_cases hcp : i.val ≤ c.val
  · obtain ⟨x,rfl⟩ := (tailCol_range hp c).mpr hcp
    rw [←residualRect_noncorner R i hp u x (Or.inl hu)]
    exact hempty x
  · by_cases hc0 : c.val=0
    · have heq : c=⟨0,hk⟩ := Fin.ext hc0
      rw [heq,first_column_zero_except_pivot R hR hk i hfirst]
      have hne : tailRow i u ≠ i := by
        intro heq
        have hv := congrArg Fin.val heq
        change i.val+u.val=i.val at hv
        omega
      simp [hne]
    · exact below_prefix_interior_zero R hR he hk i (tailRow i u) hfirst hbefore
        (by change i.val ≤ i.val+u.val; omega) c (by omega) (by omega)

private lemma residualRect_extAvoids {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩=1)
    (hbefore : ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0) (hi : 0 < i.val) :
    let hp : i.val < k := by have := prefix_width R hR hk i hfirst hbefore; omega
    ExtAvoids312 (residualRect R i hp) := by
  dsimp
  let hp : i.val < k := by have := prefix_width R hR hk i hfirst hbefore; omega
  let B := residualRect R i hp
  apply (extAvoids312_iff_safe B (residualRect_isASR R hR he hk i hfirst hbefore hi)).mpr
  have hrm := tailRow_strictMono i
  have hcm := tailCol_strictMono hp
  have hor (u : Fin (r-i.val)) (c : Fin (k-i.val)) (hn : u.val ≠ 0 ∨ c.val ≠ 0) :
      B u c=R (tailRow i u) (tailCol hp c) := residualRect_noncorner R i hp u c hn
  have hsum (c : Fin (k-i.val)) : colSum B c=colSum R (tailCol hp c) :=
    residualRect_colSum R hR he hk i hfirst hbefore hi hp c
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨u,v,w,a,b,c,hu,hv,ha,hb,h₁,h₂,h₃⟩
    apply extAvoids312_corner R he
    refine ⟨tailRow i u,tailRow i v,tailRow i w,tailCol hp a,tailCol hp b,tailCol hp c,
      hrm hu,hrm hv,hcm ha,hcm hb,?_,?_,?_⟩
    · rw [←hor u c (Or.inr (by change b.val < c.val at hb; omega))]
      exact h₁
    · rw [←hor v a (Or.inl (by change u.val < v.val at hu; omega))]
      exact h₂
    · rw [←hor w b (Or.inl (by change v.val < w.val at hv; omega))]
      exact h₃
  · intro u v a b c hu ha hb h₁ h₂ hz
    apply no312_with_deficient_last R he (tailRow i u) (tailRow i v)
      (tailCol hp a) (tailCol hp b) (tailCol hp c) (hrm hu) (hcm ha) (hcm hb)
    · rw [←hor u c (Or.inr (by change b.val < c.val at hb; omega))]
      exact h₁
    · rw [←hor v a (Or.inl (by change u.val < v.val at hu; omega))]
      exact h₂
    · rw [←hsum]
      exact hz
  · intro u v w a b hu hv hab hempty
    rintro ⟨h₁,h₂⟩
    apply no12_below_empty R he (tailRow i u) (tailRow i v) (tailRow i w)
      (tailCol hp a) (tailCol hp b) (hrm hu) (hrm hv) (hcm hab)
      (residualRect_empty_original R hR he hk i hfirst hbefore hi hp u hempty)
    constructor
    · rw [←hor v a (Or.inl (by change u.val < v.val at hu; omega))]
      exact h₁
    · rw [←hor w b (Or.inl (by change v.val < w.val at hv; omega))]
      exact h₂
  · intro u v a b hu hab hempty h₁ hz
    apply no12_with_empty_deficient R he (tailRow i u) (tailRow i v) (tailCol hp a) (tailCol hp b)
      (hrm hu) (hcm hab) (residualRect_empty_original R hR he hk i hfirst hbefore hi hp u hempty)
    · rw [←hor v a (Or.inl (by change u.val < v.val at hu; omega))]
      exact h₁
    · rw [←hsum]
      exact hz

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry

private def castRect {r k r' k' : ℕ} (hr : r=r') (hk : k=k')
    (R : Matrix (Fin r) (Fin k) SignType) : Matrix (Fin r') (Fin k') SignType :=
  Matrix.reindex (finCongr hr) (finCongr hk) R

private lemma castRect_isASR {r k r' k' : ℕ} (hr : r=r') (hk : k=k')
    (R : Matrix (Fin r) (Fin k) SignType) (hR : IsASR R) : IsASR (castRect hr hk R) := by
  subst r'; subst k'; exact hR

private lemma castRect_extAvoids {r k r' k' : ℕ} (hr : r=r') (hk : k=k')
    (R : Matrix (Fin r) (Fin k) SignType) (he : ExtAvoids312 R) : ExtAvoids312 (castRect hr hk R) := by
  subst r'; subst k'; exact he

private lemma castRect_nonemptyRows {r k r' k' : ℕ} (hr : r=r') (hk : k=k')
    (R : Matrix (Fin r) (Fin k) SignType) : nonemptyRows (castRect hr hk R)=nonemptyRows R := by
  subst r'; subst k'; rfl

private def mergeRectAt {r k p : ℕ} (hr : p < r) (hk : p < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin (r-p)) (Fin (k-p)) SignType) :
    Matrix (Fin r) (Fin k) SignType :=
  castRect (by omega : p+(r-p)=r) (by omega : p+(k-p)=k) (mergeRect M B)

private lemma mergeRectAt_isASR {r k p : ℕ} (hr : p < r) (hk : p < k) (hp : 0 < p)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin (r-p)) (Fin (k-p)) SignType)
    (hM : IsASM M) (hB : IsASR B) (hne : ∃ c, B ⟨0,by omega⟩ c ≠ 0) :
    IsASR (mergeRectAt hr hk M B) :=
  castRect_isASR _ _ _ (mergeRect_isASR hp (by omega) (by omega) M B hM hB hne)

private lemma mergeRectAt_extAvoids {r k p : ℕ} (hr : p < r) (hk : p < k) (hp : 0 < p)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin (r-p)) (Fin (k-p)) SignType)
    (hM : IsASM M) (hm : ¬ Contains312 M) (hB : IsASR B) (he : ExtAvoids312 B)
    (hne : ∃ c, B ⟨0,by omega⟩ c ≠ 0) : ExtAvoids312 (mergeRectAt hr hk M B) :=
  castRect_extAvoids _ _ _ (mergeRect_extAvoids hp (by omega) (by omega) M B hM hm hB he hne)

private lemma mergeRectAt_nonemptyRows {r k p : ℕ} (hr : p < r) (hk : p < k) (hp : 0 < p)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin (r-p)) (Fin (k-p)) SignType)
    (hM : IsASM M) (hB : IsASR B) (hne : ∃ c, B ⟨0,by omega⟩ c ≠ 0) :
    nonemptyRows (mergeRectAt hr hk M B)=p+nonemptyRows B := by
  rw [mergeRectAt,castRect_nonemptyRows]
  exact mergeRect_nonemptyRows hp (by omega) (by omega) M B hM hB hne

private lemma mergeRectAt_top {r k p : ℕ} (hr : p < r) (hk : p < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin (r-p)) (Fin (k-p)) SignType)
    (u c : Fin p) : mergeRectAt hr hk M B (Fin.castLE (le_of_lt hr) u) ⟨c.val+1,by omega⟩ = M u c := by
  have hu : Fin.cast (show p+(r-p)=r by omega).symm (Fin.castLE (le_of_lt hr) u)=u.castAdd (r-p) := by
    apply Fin.ext; rfl
  have hc : Fin.cast (show p+(k-p)=k by omega).symm (⟨c.val+1,by omega⟩ : Fin k)=
      shiftCol (by omega : p+1 ≤ p+(k-p)) c := by apply Fin.ext; rfl
  change mergeRect M B
    (Fin.cast (show p+(r-p)=r by omega).symm (Fin.castLE (le_of_lt hr) u))
    (Fin.cast (show p+(k-p)=k by omega).symm ⟨c.val+1,by omega⟩) = M u c
  rw [hu,hc]
  exact mergeRect_top (by omega) M B u c

private lemma mergeRectAt_lower {r k p : ℕ} (hr : p < r) (hk : p < k) (hp : 0 < p)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin (r-p)) (Fin (k-p)) SignType)
    (u : Fin (r-p)) (c : Fin (k-p)) :
    mergeRectAt hr hk M B (tailRow (⟨p,hr⟩ : Fin r) u) (tailCol hk c)=
      if u.val=0 ∧ c.val=0 then decCorner (B u c) else B u c := by
  have hu : Fin.cast (show p+(r-p)=r by omega).symm (tailRow (⟨p,hr⟩ : Fin r) u)=Fin.natAdd p u := by
    apply Fin.ext; rfl
  have hc : Fin.cast (show p+(k-p)=k by omega).symm (tailCol hk c)=Fin.natAdd p c := by
    apply Fin.ext; rfl
  change mergeRect M B
    (Fin.cast (show p+(r-p)=r by omega).symm (tailRow (⟨p,hr⟩ : Fin r) u))
    (Fin.cast (show p+(k-p)=k by omega).symm (tailCol hk c)) = _
  rw [hu,hc]
  exact mergeRect_lower hp M B u c

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma mergeRectAt_first_col {r k p : ℕ} (hr : p < r) (hk : p < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin (r-p)) (Fin (k-p)) SignType)
    (u : Fin r) : mergeRectAt hr hk M B u ⟨0,by omega⟩=if u.val=p then 1 else 0 := by
  have hc : Fin.cast (show p+(k-p)=k by omega).symm (⟨0,by omega⟩ : Fin k)=⟨0,by omega⟩ := by
    apply Fin.ext; rfl
  change mergeRect M B (Fin.cast (show p+(r-p)=r by omega).symm u)
    (Fin.cast (show p+(k-p)=k by omega).symm ⟨0,by omega⟩) = _
  rw [hc,mergeRect_first_col (show 0 < k-p by omega)]
  rfl

private lemma mergeRectAt_before {r k p : ℕ} (hr : p < r) (hk : p < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin (r-p)) (Fin (k-p)) SignType)
    (hM : IsASM M) (v : Fin r) (hv : v.val < p) : ∃ c, mergeRectAt hr hk M B v c ≠ 0 := by
  let u : Fin p := ⟨v.val,hv⟩
  obtain ⟨c,hc⟩ := row_has_one hM u
  have hu : Fin.castLE (le_of_lt hr) u=v := by apply Fin.ext; rfl
  let j : Fin k := ⟨c.val+1,by have := c.isLt; omega⟩
  refine ⟨j,?_⟩
  have hone : mergeRectAt hr hk M B v j=1 := by
    simpa only [hu,hc] using mergeRectAt_top hr hk M B u c
  rw [hone]
  decide

private lemma mergeRectAt_prefixSquare {r k p : ℕ} (hr : p < r) (hk : p < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin (r-p)) (Fin (k-p)) SignType)
    (hw : p+1 ≤ k) : prefixSquare (mergeRectAt hr hk M B) ⟨p,hr⟩ hw=M := by
  ext u c
  exact mergeRectAt_top hr hk M B u c

private lemma mergeRectAt_residual {r k p : ℕ} (hr : p < r) (hk : p < k) (hp : 0 < p)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin (r-p)) (Fin (k-p)) SignType)
    (hB : IsASR B) : residualRect (mergeRectAt hr hk M B) ⟨p,hr⟩ hk=B := by
  ext u c
  simp only [residualRect,mergeRectAt_lower hr hk hp M B]
  by_cases hc : u.val=0 ∧ c.val=0
  · simp only [hc,if_true]
    apply incCorner_dec
    have heq : u=(⟨0,by omega⟩ : Fin (r-p)) := Fin.ext hc.1
    rw [heq]
    exact asr_first_row_not_minus B hB (by omega) c
  · simp [hc]

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma mergeRectAt_reconstruct {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩=1)
    (hbefore : ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0) (hi : 0 < i.val) :
    let hw := prefix_width R hR hk i hfirst hbefore
    let hp : i.val < k := by omega
    mergeRectAt i.isLt hp (prefixSquare R i hw) (residualRect R i hp)=R := by
  dsimp
  let hw := prefix_width R hR hk i hfirst hbefore
  let hp : i.val < k := by have := hw; omega
  let M := prefixSquare R i hw
  let B := residualRect R i hp
  ext u c
  change mergeRect M B (Fin.cast (show i.val+(r-i.val)=r by have := i.isLt; omega).symm u)
    (Fin.cast (show i.val+(k-i.val)=k by omega).symm c)=R u c
  by_cases hu : u.val < i.val
  · by_cases hc : 0 < c.val ∧ c.val ≤ i.val
    · simp only [mergeRect,Fin.val_cast,hu,dif_pos,hc]
      have hur : Fin.castLE (Nat.le_of_lt i.isLt) (⟨u.val,hu⟩ : Fin i.val)=u := by apply Fin.ext; rfl
      have hcr : shiftCol hw (⟨c.val-1,by omega⟩ : Fin i.val)=c := by
        apply Fin.ext; simp [shiftCol]; omega
      change R (Fin.castLE (Nat.le_of_lt i.isLt) ⟨u.val,hu⟩) (shiftCol hw ⟨c.val-1,by omega⟩)=R u c
      rw [hur,hcr]
    · have hz : R u c=0 := by
        by_cases hc0 : c.val=0
        · have hce : c=⟨0,hk⟩ := Fin.ext hc0
          rw [hce]
          exact prefix_first_column_zero R hR hk i u hu hfirst
        · exact prefix_outside_zero R hR he hk i u c hu hfirst (by omega) hbefore
      simpa [mergeRect,hu,hc] using hz.symm
  · by_cases hc0 : c.val=0
    · have hce : c=⟨0,hk⟩ := Fin.ext hc0
      have hz := first_column_zero_except_pivot R hR hk i hfirst u
      rw [hce]
      simp [mergeRect,hu,Fin.ext_iff] at hz ⊢
      exact hz.symm
    · by_cases hc : i.val ≤ c.val
      · let v : Fin (r-i.val) := ⟨u.val-i.val,by have := u.isLt; omega⟩
        let b : Fin (k-i.val) := ⟨c.val-i.val,by have := c.isLt; omega⟩
        have hvr : tailRow i v=u := by apply Fin.ext; simp [tailRow,v]; omega
        have hbc : tailCol hp b=c := by apply Fin.ext; simp [tailCol,b]; omega
        have hval : B v b=if u.val=i.val ∧ c.val=i.val then incCorner (R u c) else R u c := by
          simp only [B,residualRect,hvr,hbc]
          have heq : (v.val=0 ∧ b.val=0) ↔ (u.val=i.val ∧ c.val=i.val) := by
            simp only [v,b,Fin.val_mk]
            omega
          simp only [heq]
        have hul : lowerIndex (Fin.cast (show i.val+(r-i.val)=r by have := i.isLt; omega).symm u)
            (show i.val ≤ u.val by omega)=v := by apply Fin.ext; rfl
        have hcl : lowerIndex (Fin.cast (show i.val+(k-i.val)=k by omega).symm c) hc=b := by apply Fin.ext; rfl
        simp only [mergeRect,Fin.val_cast,hu,dif_neg,hc0,if_false,hc,dif_pos,hul,hcl]
        simp only [dite_false,dite_true]
        rw [hval]
        by_cases hcorner : u.val=i.val ∧ c.val=i.val
        · simp only [hcorner,if_true]
          have hur : u=i := Fin.ext hcorner.1
          have hcr : c=⟨i.val,hp⟩ := Fin.ext hcorner.2
          rw [hur,hcr]
          exact decCorner_inc _ (pivot_not_one_at_prefix_end R hR he hk i hfirst hbefore hi)
        · simp [hcorner]
      · have hz := below_prefix_interior_zero R hR he hk i u hfirst hbefore (by omega) c (by omega) (by omega)
        simpa [mergeRect,hu,hc0,hc] using hz.symm

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset
noncomputable section

abbrev AvoidASM (n : ℕ) := {M : Matrix (Fin n) (Fin n) SignType // IsASM M ∧ ¬ Contains312 M}

abbrev FirstNonempty (r k d : ℕ) (hr : 0 < r) := {B : Counted r k d // ∃ c, B.val ⟨0,hr⟩ c ≠ 0}

abbrev ColumnFibre (r k d p : ℕ) (hr : p < r) (hk : p < k) :=
  {R : Matrix (Fin r) (Fin k) SignType // IsASR R ∧ ExtAvoids312 R ∧ nonemptyRows R=d ∧
    R ⟨p,hr⟩ ⟨0,by omega⟩=1 ∧ ∀ v : Fin r, v.val < p → ∃ c, R v c ≠ 0}

private def extractColumnFibre {r k d p : ℕ} (hr : p < r) (hk : p < k) (hp : 0 < p)
    (R : ColumnFibre r k d p hr hk) : AvoidASM p × FirstNonempty (r-p) (k-p) (d-p) (by omega) := by
  let i : Fin r := ⟨p,hr⟩
  have hR := R.property.1
  have he := R.property.2.1
  have hfirst := R.property.2.2.2.1
  have hbefore := R.property.2.2.2.2
  let hw := prefix_width R.val hR (show 0 < k by omega) i hfirst hbefore
  let M := prefixSquare R.val i hw
  let B := residualRect R.val i hk
  have hM : IsASM M := prefixSquare_isASM R.val hR he (by omega) i hfirst hbefore
  have hm : ¬ Contains312 M := prefixSquare_avoids R.val he i hw
  have hB : IsASR B := residualRect_isASR R.val hR he (by omega) i hfirst hbefore hp
  have hbe : ExtAvoids312 B := residualRect_extAvoids R.val hR he (by omega) i hfirst hbefore hp
  have hne : ∃ c, B ⟨0,by omega⟩ c ≠ 0 := (residualRect_top_row R.val hR he (by omega) i hfirst hbefore hp).2
  have hd : nonemptyRows B=d-p := by
    have hc := mergeRectAt_nonemptyRows hr hk hp M B hM hB hne
    have hi := mergeRectAt_reconstruct R.val hR he (by omega) i hfirst hbefore hp
    rw [show mergeRectAt hr hk M B=R.val from hi] at hc
    have ht := R.property.2.2.1
    omega
  exact (⟨M,hM,hm⟩,⟨⟨B,hB,hbe,hd⟩,hne⟩)

def mergeColumnFibre {r k d p : ℕ} (hr : p < r) (hk : p < k) (hp : 0 < p) (hd : p ≤ d)
    (x : AvoidASM p × FirstNonempty (r-p) (k-p) (d-p) (by omega)) : ColumnFibre r k d p hr hk := by
  let M := x.1.val
  let B := x.2.val.val
  have hM := x.1.property.1
  have hm := x.1.property.2
  have hB := x.2.val.property.1
  have he := x.2.val.property.2.1
  have hne := x.2.property
  refine ⟨mergeRectAt hr hk M B,mergeRectAt_isASR hr hk hp M B hM hB hne,
    mergeRectAt_extAvoids hr hk hp M B hM hm hB he hne,?_,?_,?_⟩
  · rw [mergeRectAt_nonemptyRows hr hk hp M B hM hB hne,x.2.val.property.2.2]
    omega
  · rw [mergeRectAt_first_col]
    simp
  · exact mergeRectAt_before hr hk M B hM

private def firstColumnFactorEquiv {r k d p : ℕ} (hr : p < r) (hk : p < k) (hp : 0 < p) (hd : p ≤ d) :
    ColumnFibre r k d p hr hk ≃ AvoidASM p × FirstNonempty (r-p) (k-p) (d-p) (by omega) where
  toFun := extractColumnFibre hr hk hp
  invFun := mergeColumnFibre hr hk hp hd
  left_inv := by
    intro R
    apply Subtype.ext
    exact mergeRectAt_reconstruct R.val R.property.1 R.property.2.1 (by omega) ⟨p,hr⟩
      R.property.2.2.2.1 R.property.2.2.2.2 hp
  right_inv := by
    intro x
    apply Prod.ext
    · apply Subtype.ext
      exact mergeRectAt_prefixSquare hr hk x.1.val x.2.val.val _
    · apply Subtype.ext
      apply Subtype.ext
      exact mergeRectAt_residual hr hk hp x.1.val x.2.val.val x.2.val.property.1

lemma firstColumnFactor_card {r k d p : ℕ} (hr : p < r) (hk : p < k) (hp : 0 < p) (hd : p ≤ d) :
    Nat.card (ColumnFibre r k d p hr hk) =
      Nat.card (AvoidASM p) * Nat.card (FirstNonempty (r-p) (k-p) (d-p) (by omega)) := by
  rw [Nat.card_congr (firstColumnFactorEquiv hr hk hp hd),Nat.card_prod]

end
end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset
noncomputable section

private def squareCountEquiv (n : ℕ) : Counted n n n ≃ AvoidASM n :=
  Equiv.subtypeEquivRight fun M =>
    ⟨fun h => ⟨square_count_isASM M h.1 h.2.2, extAvoids312_corner M h.2.1⟩,
      fun h => ⟨h.1.1, ⟨n, le_refl _, le_refl _, M, h.1, h.2, by intro u c; rfl⟩,
        asm_nonemptyRows M h.1⟩⟩

lemma squareCount_card (n : ℕ) : S n n n=Nat.card (AvoidASM n) := Nat.card_congr (squareCountEquiv n)

lemma AvoidASM_zero_card : Nat.card (AvoidASM 0)=1 := by
  classical
  letI : Unique (Matrix (Fin 0) (Fin 0) SignType) :=
    { default := fun _ _ => 0, uniq := fun M => funext fun i => Fin.elim0 i }
  simp [AvoidASM, Nat.card_eq_fintype_card, IsASM, IsASR, Contains312,
    Fintype.card_unique]

lemma asm_extAvoids {n : ℕ} (M : AvoidASM n) : ExtAvoids312 M.val := by
  refine ⟨n,le_refl _,le_refl _,M.val,M.property.1,M.property.2,?_⟩
  intro u c; rfl

lemma asm_first_column_one {n : ℕ} (hn : 0 < n) (M : AvoidASM n) : ∃ u, M.val u ⟨0,hn⟩=1 := by
  obtain ⟨u,_,hu⟩ := one_after_zero_prefix (show 0 ≤ n by omega) (fun u => M.val u ⟨0,hn⟩)
    (M.property.1.2.2 _) (by simp)
  exact ⟨u,hu⟩

abbrev ASMFibre (n : ℕ) (hn : 0 < n) (p : Fin n) := {M : AvoidASM n // M.val p ⟨0,hn⟩=1}

private def asmColumnFibreEquiv {n : ℕ} (hn : 0 < n) (p : Fin n) :
    ASMFibre n hn p ≃ ColumnFibre n n n p.val p.isLt p.isLt :=
  (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun M : Matrix (Fin n) (Fin n) SignType => IsASM M ∧ ¬Contains312 M)
    (fun M => M p ⟨0,hn⟩=1)).trans
    (Equiv.subtypeEquivRight fun M =>
      ⟨fun h => ⟨h.1.1.1, asm_extAvoids ⟨M,h.1⟩, asm_nonemptyRows M h.1.1, h.2, by
        intro u _
        exact (asr_row_sum_one_iff M h.1.1.1 u).mp (h.1.1.2.1 u)⟩,
        fun h => ⟨⟨square_count_isASM M h.1 h.2.2.1,
          extAvoids312_corner M h.2.1⟩, h.2.2.2.1⟩⟩)

def fullFirstNonemptyEquiv (r k : ℕ) (hr : 0 < r) : FirstNonempty r k r hr ≃ Counted r k r :=
  Equiv.subtypeUnivEquiv (fun B : Counted r k r =>
    (all_rows_nonempty_iff B.val).mp B.property.2.2 ⟨0,hr⟩)

lemma asmNonzeroFibre_card {n : ℕ} (hn : 0 < n) (p : Fin n) (hp : 0 < p.val) :
    Nat.card (ASMFibre n hn p)=Nat.card (AvoidASM p.val)*Nat.card (AvoidASM (n-p.val)) := by
  rw [Nat.card_congr (asmColumnFibreEquiv hn p),firstColumnFactor_card p.isLt p.isLt hp (le_of_lt p.isLt)]
  congr 1
  rw [Nat.card_congr (fullFirstNonemptyEquiv (n-p.val) (n-p.val) (by have := p.isLt; omega)),←squareCount_card]
  rfl

end
end D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
