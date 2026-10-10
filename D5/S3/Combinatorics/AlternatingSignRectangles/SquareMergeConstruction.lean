/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: SquareMergeConstruction for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
decCorner_cast: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.correctedColumn_sum
incCorner_dec: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_residual
decCorner_inc: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_reconstruct
incCorner_cast: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_colSum
mergeRect_top: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_top, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_empty_source, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_end_column_function, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_interior_column, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_small_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_top_row
mergeRect_top_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_right_column, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_top_row
mergeRect_first_col: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_first_col, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_empty_source, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_lower_row, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_one_zero_col, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_pivot_row_function, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_small_colSum
mergeRect_lower_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_interior_column, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_lower_row, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_pivot_row_function, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_small_colSum
mergeRect_lower: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_lower, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_empty_source, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_end_column_function, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_lower_row, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_pivot_row_function, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_right_column
upperCol_strictMono: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_top_row
upperCol_range: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_top_row
mergeRect_top_row: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_isASR
mergeRect_lower_row: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_isASR
mergeRect_pivot_row_function: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_pivot_row
mergeRect_pivot_row: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.minus_between_ones
correctedColumn_zero: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.minus_between_ones
correctedColumn_line: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.minus_between_ones
mergeRect_interior_column: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_isASR
mergeRect_right_column: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_isASR
mergeRect_end_column_function: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_end_column
mergeRect_end_column: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.concat_complete_opposite
mergeRect_isASR: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.concat_complete_opposite
correctedColumn_sum: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_colSum
mergeRect_colSum: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_deficient_source, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_nonemptyRows
mergeRect_small_colSum: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_deficient_source, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_nonemptyRows
decCorner_ne_one: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_one_lower
mergeRect_one_top: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_avoids_corner, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_extAvoids
mergeRect_one_lower: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_avoids_corner, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_one_late
mergeRect_one_zero_col: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_avoids_corner, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_one_late
lowerIndex_lt: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_avoids_corner, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_extAvoids
mergeRect_avoids_corner: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_avoids_corner
mergeRect_one_late: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_extAvoids
mergeRect_deficient_source: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_extAvoids
mergeRect_empty_source: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_extAvoids
mergeRect_extAvoids: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_avoids_corner
mergeRect_nonemptyRows: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_nonemptyRows
all_rows_nonempty_iff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.pivot_before_nonempty, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.fullFirstNonemptyEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.asm_nonemptyRows, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.square_count_isASM
asm_nonemptyRows: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.asmZeroFibreEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.asmColumnFibreEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.squareCountEquiv
square_count_isASM: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
Direct frozen dependencies: none; the ASR prerequisites are same-delivery content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

def lowerIndex {p n : ℕ} (x : Fin (p+n)) (hx : p ≤ x.val) : Fin n :=
  Fin.subNat p (Fin.cast (Nat.add_comm p n) x) hx

def decCorner (s : SignType) : SignType := if s = 1 then 0 else -1

def incCorner (s : SignType) : SignType := if s = -1 then 0 else 1

private lemma decCorner_cast (s : SignType) (hs : s ≠ -1) :
    (decCorner s : ℤ) = (s : ℤ) - 1 := by cases s <;> simp_all [decCorner]

lemma incCorner_dec (s : SignType) (hs : s ≠ -1) : incCorner (decCorner s) = s := by
  cases s <;> simp_all [decCorner,incCorner]

lemma decCorner_inc (s : SignType) (hs : s ≠ 1) : decCorner (incCorner s) = s := by
  cases s <;> simp_all [decCorner,incCorner]

lemma incCorner_cast (s : SignType) (hs : s ≠ 1) :
    (incCorner s : ℤ) = (s : ℤ) + 1 := by cases s <;> simp_all [incCorner]

def mergeRect {p r k : ℕ} (M : Matrix (Fin p) (Fin p) SignType)
    (B : Matrix (Fin r) (Fin k) SignType) : Matrix (Fin (p+r)) (Fin (p+k)) SignType :=
  fun u c =>
    if hu : u.val < p then
      if hc : 0 < c.val ∧ c.val ≤ p then M ⟨u.val,hu⟩ ⟨c.val-1,by omega⟩ else 0
    else if c.val=0 then if u.val=p then 1 else 0
    else if hc : p ≤ c.val then
      if u.val=p ∧ c.val=p then decCorner (B (lowerIndex u (by omega)) (lowerIndex c hc))
      else B (lowerIndex u (by omega)) (lowerIndex c hc)
    else 0

lemma mergeRect_top {p r k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (u c : Fin p) : mergeRect M B (u.castAdd r) (shiftCol (by omega : p+1 ≤ p+k) c) = M u c := by
  simp [mergeRect,shiftCol,u.isLt,show c.val+1 ≤ p by omega]

private lemma mergeRect_top_zero {p r k : ℕ}
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (u : Fin p) (c : Fin (p+k)) (hc : c.val=0 ∨ p < c.val) :
    mergeRect M B (u.castAdd r) c = 0 := by
  simp only [mergeRect,Fin.val_castAdd, u.isLt,dif_pos]
  have hn : ¬ (0 < c.val ∧ c.val ≤ p) := by omega
  simp [hn]

lemma mergeRect_first_col {p r k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (u : Fin (p+r)) : mergeRect M B u ⟨0,by omega⟩ = if u.val=p then 1 else 0 := by
  by_cases hu : u.val<p
  · simp [mergeRect,hu,show u.val ≠ p by omega]
  · simp [mergeRect,hu]

private lemma mergeRect_lower_zero {p r k : ℕ}
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (u : Fin r) (c : Fin (p+k)) (hc : 0 < c.val) (hcp : c.val < p) :
    mergeRect M B (Fin.natAdd p u) c = 0 := by
  simp [mergeRect,show ¬ p+u.val < p by omega,show c.val ≠ 0 by omega,
    show ¬ p ≤ c.val by omega]

lemma mergeRect_lower {p r k : ℕ} (hp : 0 < p)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (u : Fin r) (c : Fin k) :
    mergeRect M B (Fin.natAdd p u) (Fin.natAdd p c) =
      if u.val=0 ∧ c.val=0 then decCorner (B u c) else B u c := by
  have hu : ¬ p+u.val < p := by omega
  have hc : p+c.val ≠ 0 := by omega
  have hic : lowerIndex (Fin.natAdd p c) (by change p ≤ p+c.val; omega) = c := by
    apply Fin.ext; simp [lowerIndex]
  have hiu : lowerIndex (Fin.natAdd p u) (by change p ≤ p+u.val; omega) = u := by
    apply Fin.ext; simp [lowerIndex]
  simp [mergeRect,hu,hc,hiu,hic,Nat.ne_of_gt hp]

private lemma upperCol_strictMono {p k : ℕ} (hk : 0 < k) : StrictMono (shiftCol (by omega : p+1 ≤ p+k)) := by
  exact (Fin.strictMono_castLE (by omega : p+1 ≤ p+k)).comp Fin.strictMono_succ

private lemma upperCol_range {p k : ℕ} (hk : 0 < k) (c : Fin (p+k)) :
    (∃ x : Fin p, shiftCol (by omega : p+1 ≤ p+k) x=c) ↔ 0 < c.val ∧ c.val ≤ p := by
  constructor
  · rintro ⟨x,rfl⟩
    change 0 < x.val+1 ∧ x.val+1 ≤ p
    have := x.isLt
    omega
  · intro hc
    refine ⟨⟨c.val-1,by omega⟩,?_⟩
    apply Fin.ext
    change c.val-1+1=c.val
    omega

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma mergeRect_top_row {p r k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hM : IsASR M) (u : Fin p) :
    Alternates (mergeRect M B (u.castAdd r)) ∧ StartsOne (mergeRect M B (u.castAdd r)) ∧
      EndsOne (mergeRect M B (u.castAdd r)) := by
  have hout (c : Fin (p+k)) (hc : ¬ ∃ x, shiftCol (by omega : p+1 ≤ p+k) x=c) :
      mergeRect M B (u.castAdd r) c = 0 := by
    have hn := (upperCol_range hk c).not.mp hc
    apply mergeRect_top_zero M B u c
    omega
  have hl := line_embed (M u) (mergeRect M B (u.castAdd r)) (shiftCol (by omega : p+1 ≤ p+k))
    (upperCol_strictMono hk) (mergeRect_top hk M B u) hout (hM.1 u).1 (hM.1 u).2.1
  exact ⟨hl.1,hl.2,ends_embed _ _ _ (upperCol_strictMono hk)
    (mergeRect_top hk M B u) hout (hM.1 u).2.2⟩

private lemma mergeRect_lower_row {p r k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hB : IsASR B) (u : Fin r) (hu : u.val ≠ 0) :
    Alternates (mergeRect M B (Fin.natAdd p u)) ∧ StartsOne (mergeRect M B (Fin.natAdd p u)) ∧
      EndsOne (mergeRect M B (Fin.natAdd p u)) := by
  have hf : StrictMono (Fin.natAdd p : Fin k → Fin (p+k)) := by intro a b hab; simpa using hab
  have hval (c : Fin k) : mergeRect M B (Fin.natAdd p u) (Fin.natAdd p c)=B u c := by
    simp [mergeRect_lower hp M B u c,hu]
  have hout (c : Fin (p+k)) (hc : ¬ ∃ x, Fin.natAdd p x=c) :
      mergeRect M B (Fin.natAdd p u) c=0 := by
    have hcp : c.val < p := by
      by_contra hn
      apply hc
      exact ⟨lowerIndex c (by omega),by apply Fin.ext; simp [lowerIndex] <;> omega⟩
    by_cases hc0 : c.val=0
    · have heq : c=⟨0,by omega⟩ := Fin.ext hc0
      rw [heq,mergeRect_first_col hk M B]
      simp [hu]
    · exact mergeRect_lower_zero M B u c (by omega) hcp
  have hl := line_embed (B u) (mergeRect M B (Fin.natAdd p u)) (Fin.natAdd p) hf hval hout
    (hB.1 u).1 (hB.1 u).2.1
  exact ⟨hl.1,hl.2,ends_embed _ _ _ hf hval hout (hB.1 u).2.2⟩

private lemma mergeRect_pivot_row_function {p r k : ℕ} (hp : 0 < p) (hr : 0 < r) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (q : Fin k) (hq : ∀ c, B ⟨0,hr⟩ c=if c=q then 1 else 0) :
    mergeRect M B (Fin.natAdd p ⟨0,hr⟩) =
      if q.val=0 then (fun c => if c.val=0 then 1 else 0)
      else (fun c => if c.val=0 then 1 else if c.val=p then -1 else
        if c.val=p+q.val then 1 else 0) := by
  funext c
  by_cases hc0 : c.val=0
  · have heq : c=⟨0,by omega⟩ := Fin.ext hc0
    rw [heq,mergeRect_first_col hk M B]
    by_cases hq0 : q.val=0 <;> simp [hq0]
  by_cases hcp : p ≤ c.val
  · let x := lowerIndex c hcp
    have heq : Fin.natAdd p x=c := by apply Fin.ext; simp [x,lowerIndex] <;> omega
    rw [←heq,mergeRect_lower hp M B]
    have hx : x.val = c.val-p := rfl
    have hsum : p+x.val=c.val := by omega
    have hqe : x=q ↔ x.val=q.val := Fin.ext_iff
    have hz : B ⟨0,hr⟩ x=if x=q then 1 else 0 := hq x
    rw [hz]
    simp only [Fin.val_natAdd,Fin.val_mk,zero_add,true_and]
    by_cases hq0 : q.val=0
    · have hxe : x=q ↔ x.val=0 := by rw [hqe,hq0]
      by_cases hx0 : x.val=0 <;> simp [hq0,hxe,hx0,decCorner,hp.ne']
    · by_cases hx0 : x.val=0
      · have hxq : x ≠ q := by intro he; have := congrArg Fin.val he; omega
        simp [hq0,hx0,hxq,decCorner,Nat.ne_of_gt hp]
      · have hpx : p+x.val ≠ p := by omega
        have hpxq : p+x.val=p+q.val ↔ x=q := by rw [hqe]; omega
        simp [hq0,hx0,hpx,hpxq,Nat.ne_of_gt hp,Fin.ext_iff]
  · have hz := mergeRect_lower_zero M B (⟨0,hr⟩ : Fin r) c (by omega) (by omega)
    rw [hz]
    have hnp : c.val ≠ p := by omega
    have hnq : c.val ≠ p+q.val := by omega
    by_cases hq0 : q.val=0 <;> simp [hq0,hc0,hnp,hnq]

private lemma mergeRect_pivot_row {p r k : ℕ} (hp : 0 < p) (hr : 0 < r) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hB : IsASR B) (hne : ∃ c, B ⟨0,hr⟩ c ≠ 0) :
    Alternates (mergeRect M B (Fin.natAdd p ⟨0,hr⟩)) ∧
      StartsOne (mergeRect M B (Fin.natAdd p ⟨0,hr⟩)) ∧
      EndsOne (mergeRect M B (Fin.natAdd p ⟨0,hr⟩)) := by
  obtain ⟨q,hq⟩ := asr_first_row_singleton B hB hr hne
  rw [mergeRect_pivot_row_function hp hr hk M B q hq]
  by_cases hq0 : q.val=0
  · simp only [hq0,if_true]
    have hf : (fun c : Fin (p+k) => if c.val=0 then (1 : SignType) else 0) =
      (fun c => if c=(⟨0,by omega⟩ : Fin (p+k)) then 1 else 0) := by
      funext c; simp [Fin.ext_iff]
    rw [hf]
    simpa only [eq_comm] using singleton_line (⟨0,by omega⟩ : Fin (p+k))
  · simp only [hq0,if_false]
    have hf : (fun c : Fin (p+k) => if c.val=0 then (1 : SignType) else if c.val=p then -1 else
        if c.val=p+q.val then 1 else 0) =
      (fun c => if c=(⟨0,by omega⟩ : Fin (p+k)) then 1 else
        if c=⟨p,by omega⟩ then -1 else if c=Fin.natAdd p q then 1 else 0) := by
      funext c; simp [Fin.ext_iff]
    rw [hf]
    exact three_sign_line _ _ _ hp (by change p < p+q.val; omega)

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private def correctedColumn {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (hk : 0 < k) : Fin r → SignType :=
  fun u => if u.val=0 then decCorner (B u ⟨0,hk⟩) else B u ⟨0,hk⟩

private lemma correctedColumn_zero {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (hB : IsASR B) (hr : 0 < r) (hk : 0 < k) (h00 : B ⟨0,hr⟩ ⟨0,hk⟩=1) :
    correctedColumn B hk = fun _ => 0 := by
  have hs := line_no_minus_singleton (fun u => B u ⟨0,hk⟩) (hB.2 _).1
    (asr_first_col_not_minus B hB hk) ⟨0,hr⟩ h00
  funext u
  simp only [correctedColumn,hs,Fin.ext_iff]
  by_cases hu : u.val=0 <;> simp [hu,decCorner]

private lemma correctedColumn_line {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (hB : IsASR B) (hr : 0 < r) (hk : 0 < k) (h00 : B ⟨0,hr⟩ ⟨0,hk⟩ ≠ 1) :
    Alternates (correctedColumn B hk) ∧ StartsMinus (correctedColumn B hk) := by
  classical
  by_cases hone : ∃ q, B q ⟨0,hk⟩=1
  · obtain ⟨q,hq⟩ := hone
    have hq0 : q.val ≠ 0 := by
      intro h
      have heq : q=⟨0,hr⟩ := Fin.ext h
      exact h00 (by simpa only [heq] using hq)
    have hs := line_no_minus_singleton (fun u => B u ⟨0,hk⟩) (hB.2 _).1
      (asr_first_col_not_minus B hB hk) q hq
    have hf : correctedColumn B hk =
        (fun u => if u=(⟨0,hr⟩ : Fin r) then -1 else if u=q then 1 else 0) := by
      funext u
      simp only [correctedColumn,hs,Fin.ext_iff]
      by_cases hu : u.val=0
      · have hunq : u.val ≠ q.val := by omega
        simp [hu,hunq,decCorner,hq0,Ne.symm hq0]
      · simp [hu]
    rw [hf]
    exact minus_plus_line ⟨0,hr⟩ q (by change 0 < q.val; omega)
  · have hz (u : Fin r) : B u ⟨0,hk⟩=0 := by
      have hn := asr_first_col_not_minus B hB hk u
      have hn1 : B u ⟨0,hk⟩ ≠ 1 := by intro h; exact hone ⟨u,h⟩
      cases he : B u ⟨0,hk⟩ <;> simp_all
    have hf : correctedColumn B hk = (fun u => if u=(⟨0,hr⟩ : Fin r) then -1 else 0) := by
      funext u
      simp [correctedColumn,hz,decCorner,Fin.ext_iff]
    rw [hf]
    exact minus_singleton_line _

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma mergeRect_interior_column {p r k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hM : IsASR M) (c : Fin (p+k)) (hc : 0 < c.val) (hcp : c.val < p) :
    Alternates (fun u => mergeRect M B u c) ∧ StartsOne (fun u => mergeRect M B u c) := by
  let x : Fin p := ⟨c.val-1,by omega⟩
  have heq : shiftCol (by omega : p+1 ≤ p+k) x=c := by apply Fin.ext; simp [shiftCol,x] <;> omega
  have hval (u : Fin p) : mergeRect M B (u.castAdd r) c=M u x := by
    rw [←heq,mergeRect_top hk]
  have hf : StrictMono (fun u : Fin p => u.castAdd r) := by intro a b hab; exact hab
  have hout (v : Fin (p+r)) (hn : ¬ ∃ u : Fin p, u.castAdd r=v) : mergeRect M B v c=0 := by
    have hv : p ≤ v.val := by
      by_contra hnlt
      apply hn
      exact ⟨⟨v.val,by omega⟩,by apply Fin.ext; rfl⟩
    let u := lowerIndex v hv
    have hvu : Fin.natAdd p u=v := by apply Fin.ext; simp [u,lowerIndex] <;> omega
    rw [←hvu]
    exact mergeRect_lower_zero M B u c hc hcp
  exact line_embed (fun u => M u x) (fun u => mergeRect M B u c)
    (fun u => u.castAdd r) hf hval hout (hM.2 x).1 (hM.2 x).2

private lemma mergeRect_right_column {p r k : ℕ} (hp : 0 < p)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hB : IsASR B) (c : Fin (p+k)) (hc : p < c.val) :
    Alternates (fun u => mergeRect M B u c) ∧ StartsOne (fun u => mergeRect M B u c) := by
  let x := lowerIndex c (le_of_lt hc)
  have hx0 : x.val ≠ 0 := by change c.val-p ≠ 0; omega
  have heq : Fin.natAdd p x=c := by apply Fin.ext; simp [x,lowerIndex] <;> omega
  have hval (u : Fin r) : mergeRect M B (Fin.natAdd p u) c=B u x := by
    rw [←heq,mergeRect_lower hp]
    simp [hx0]
  have hf : StrictMono (Fin.natAdd p : Fin r → Fin (p+r)) := by intro a b hab; simpa using hab
  have hout (v : Fin (p+r)) (hn : ¬ ∃ u : Fin r, Fin.natAdd p u=v) : mergeRect M B v c=0 := by
    have hv : v.val < p := by
      by_contra hnlt
      apply hn
      exact ⟨lowerIndex v (by omega),by apply Fin.ext; simp [lowerIndex] <;> omega⟩
    have hvu : (⟨v.val,hv⟩ : Fin p).castAdd r=v := by apply Fin.ext; rfl
    rw [←hvu]
    exact mergeRect_top_zero M B _ c (Or.inr hc)
  exact line_embed (fun u => B u x) (fun u => mergeRect M B u c) (Fin.natAdd p) hf hval hout
    (hB.2 x).1 (hB.2 x).2

private lemma mergeRect_end_column_function {p r k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType) :
    (fun u => mergeRect M B u ⟨p,by omega⟩) =
      Fin.append (fun u => M u ⟨p-1,by omega⟩) (correctedColumn B hk) := by
  funext v
  refine Fin.addCases (fun u => ?_) (fun u => ?_) v
  · have heq : shiftCol (by omega : p+1 ≤ p+k) (⟨p-1,by omega⟩ : Fin p) = ⟨p,by omega⟩ := by
      apply Fin.ext; simp [shiftCol] <;> omega
    rw [←heq,mergeRect_top hk,Fin.append_left]
  · have heq : (⟨p,by omega⟩ : Fin (p+k))=Fin.natAdd p ⟨0,hk⟩ := by apply Fin.ext; simp
    rw [heq,mergeRect_lower hp,Fin.append_right]
    simp [correctedColumn]

private lemma mergeRect_end_column {p r k : ℕ} (hp : 0 < p) (hr : 0 < r) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hM : IsASM M) (hB : IsASR B) :
    Alternates (fun u => mergeRect M B u ⟨p,by omega⟩) ∧
      StartsOne (fun u => mergeRect M B u ⟨p,by omega⟩) := by
  rw [mergeRect_end_column_function hp hk]
  by_cases h00 : B ⟨0,hr⟩ ⟨0,hk⟩=1
  · rw [correctedColumn_zero B hB hr hk h00]
    have h := pad_zero_line (t := r) (fun u => M u ⟨p-1,by omega⟩)
      (hM.1.2 _).1 (hM.1.2 _).2 (asm_column_ends_one hM _)
    exact ⟨h.1,h.2.1⟩
  · have h := correctedColumn_line B hB hr hk h00
    exact concat_complete_opposite _ _ (hM.1.2 _).1 (hM.1.2 _).2
      (asm_column_ends_one hM _) (hM.2.2 _) h.1 h.2

lemma mergeRect_isASR {p r k : ℕ} (hp : 0 < p) (hr : 0 < r) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hM : IsASM M) (hB : IsASR B) (hne : ∃ c, B ⟨0,hr⟩ c ≠ 0) :
    IsASR (mergeRect M B) := by
  refine ⟨?_,?_⟩
  · intro v
    refine Fin.addCases (fun u => mergeRect_top_row hk M B hM.1 u) (fun u => ?_) v
    by_cases hu : u.val=0
    · have heq : u=⟨0,hr⟩ := Fin.ext hu
      rw [heq]
      exact mergeRect_pivot_row hp hr hk M B hB hne
    · exact mergeRect_lower_row hp hk M B hB u hu
  · intro c
    by_cases hc0 : c.val=0
    · have heq : c=⟨0,by omega⟩ := Fin.ext hc0
      rw [heq]
      have hf : (fun u => mergeRect M B u ⟨0,by omega⟩) =
          (fun u => if (Fin.natAdd p ⟨0,hr⟩ : Fin (p+r))=u then 1 else 0) := by
        funext u
        rw [mergeRect_first_col hk]
        simp [Fin.ext_iff,eq_comm]
      rw [hf]
      exact ⟨(singleton_line _).1,(singleton_line _).2.1⟩
    rcases lt_trichotomy c.val p with hc | hc | hc
    · exact mergeRect_interior_column hk M B hM.1 c (by omega) hc
    · have heq : c=⟨p,by omega⟩ := Fin.ext hc
      rw [heq]
      exact mergeRect_end_column hp hr hk M B hM hB
    · exact mergeRect_right_column hp M B hB c hc

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma correctedColumn_sum {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (hB : IsASR B) (hr : 0 < r) (hk : 0 < k) :
    (∑ u, (correctedColumn B hk u : ℤ)) = colSum B ⟨0,hk⟩-1 := by
  have hv (u : Fin r) : (correctedColumn B hk u : ℤ) =
      (B u ⟨0,hk⟩ : ℤ) - if u=(⟨0,hr⟩ : Fin r) then 1 else 0 := by
    by_cases hu : u.val=0
    · have heq : u=⟨0,hr⟩ := Fin.ext hu
      simp only [correctedColumn,hu,if_true,heq]
      exact decCorner_cast _ (asr_first_col_not_minus B hB hk _)
    · have hn : u ≠ ⟨0,hr⟩ := by intro heq; exact hu (by simpa using congrArg Fin.val heq)
      simp [correctedColumn,hu,hn]
  simp_rw [hv]
  rw [sum_sub_distrib]
  simp [colSum]

private lemma mergeRect_colSum {p r k : ℕ} (hp : 0 < p) (hr : 0 < r) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hM : IsASM M) (hB : IsASR B) (c : Fin k) :
    colSum (mergeRect M B) (Fin.natAdd p c) = colSum B c := by
  by_cases hc : c.val=0
  · have heq : c=⟨0,hk⟩ := Fin.ext hc
    subst c
    have hep : (Fin.natAdd p ⟨0,hk⟩ : Fin (p+k))=⟨p,by omega⟩ := by apply Fin.ext; simp
    change (∑ u, (mergeRect M B u (Fin.natAdd p ⟨0,hk⟩) : ℤ)) = _
    rw [hep]
    simp_rw [congrFun (mergeRect_end_column_function hp hk M B)]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right]
    rw [hM.2.2,correctedColumn_sum B hB hr hk]
    omega
  · have hval (u : Fin r) : mergeRect M B (Fin.natAdd p u) (Fin.natAdd p c)=B u c := by
      simp [mergeRect_lower hp M B u c,hc]
    change (∑ u, (mergeRect M B u (Fin.natAdd p c) : ℤ)) = _
    rw [Fin.sum_univ_add]
    have hz (u : Fin p) : mergeRect M B (u.castAdd r) (Fin.natAdd p c)=0 :=
      mergeRect_top_zero M B u _ (Or.inr (by change p < p+c.val; omega))
    simp only [hz,hval,SignType.coe_zero,sum_const_zero,zero_add]
    rfl

private lemma mergeRect_small_colSum {p r k : ℕ} (hp : 0 < p) (hr : 0 < r) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hM : IsASM M) (c : Fin (p+k)) (hc : c.val < p) :
    colSum (mergeRect M B) c=1 := by
  by_cases hc0 : c.val=0
  · have heq : c=⟨0,by omega⟩ := Fin.ext hc0
    rw [heq]
    unfold colSum
    simp_rw [mergeRect_first_col hk M B]
    have hv (u : Fin (p+r)) : ((if u.val=p then 1 else 0 : SignType) : ℤ)=
        if u=(Fin.natAdd p ⟨0,hr⟩ : Fin (p+r)) then 1 else 0 := by
      simp only [Fin.ext_iff,Fin.val_natAdd,Fin.val_mk,add_zero]
      split_ifs <;> rfl
    simp_rw [hv]
    simp
  · let x : Fin p := ⟨c.val-1,by omega⟩
    have heq : shiftCol (by omega : p+1 ≤ p+k) x=c := by apply Fin.ext; simp [shiftCol,x] <;> omega
    unfold colSum
    rw [Fin.sum_univ_add]
    have hl (u : Fin p) : mergeRect M B (u.castAdd r) c=M u x := by rw [←heq,mergeRect_top hk]
    have hr' (u : Fin r) : mergeRect M B (Fin.natAdd p u) c=0 :=
      mergeRect_lower_zero M B u c (by omega) hc
    simp_rw [hl,hr']
    simp only [SignType.coe_zero,sum_const_zero,add_zero]
    exact hM.2.2 x

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma decCorner_ne_one (s : SignType) : decCorner s ≠ 1 := by
  unfold decCorner
  split_ifs <;> decide

private lemma mergeRect_one_top {p r k : ℕ}
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (u : Fin (p+r)) (c : Fin (p+k)) (hu : u.val < p) (hone : mergeRect M B u c=1) :
    ∃ hc : 0 < c.val ∧ c.val ≤ p, M ⟨u.val,hu⟩ ⟨c.val-1,by omega⟩=1 := by
  by_cases hc : 0 < c.val ∧ c.val ≤ p
  · exact ⟨hc,by simpa [mergeRect,hu,hc] using hone⟩
  · simp [mergeRect,hu,hc] at hone

private lemma mergeRect_one_lower {p r k : ℕ}
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (u : Fin (p+r)) (c : Fin (p+k)) (hu : p ≤ u.val) (hc0 : c.val ≠ 0)
    (hone : mergeRect M B u c=1) :
    ∃ hc : p ≤ c.val, B (lowerIndex u hu) (lowerIndex c hc)=1 := by
  have hnu : ¬ u.val < p := by omega
  by_cases hc : p ≤ c.val
  · by_cases hx : u.val=p ∧ c.val=p
    · have hp0 : p ≠ 0 := by omega
      have hm : decCorner (B (lowerIndex u hu) (lowerIndex c hc))=1 := by
        simpa [mergeRect,hnu,hc0,hc,hx,hp0] using hone
      exact (decCorner_ne_one _ hm).elim
    · exact ⟨hc,by simpa [mergeRect,hnu,hc0,hc,hx] using hone⟩
  · simp [mergeRect,hnu,hc0,hc] at hone

private lemma mergeRect_one_zero_col {p r k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (u : Fin (p+r)) (c : Fin (p+k)) (hc : c.val=0) (hone : mergeRect M B u c=1) : u.val=p := by
  have heq : c=⟨0,by omega⟩ := Fin.ext hc
  rw [heq,mergeRect_first_col hk] at hone
  by_contra hn
  simp [hn] at hone

private lemma lowerIndex_lt {p n : ℕ} (u v : Fin (p+n)) (hu : p ≤ u.val) (hv : p ≤ v.val)
    (huv : u < v) : lowerIndex u hu < lowerIndex v hv := by
  change u.val-p < v.val-p
  change u.val < v.val at huv
  omega

private lemma mergeRect_avoids_corner {p r k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hm : ¬ Contains312 M) (hb : ¬ RectContains312 B) : ¬ RectContains312 (mergeRect M B) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,hi₁,hi₂,hj₁,hj₂,h₁,h₂,h₃⟩
  by_cases htop : i₁.val < p
  · obtain ⟨hc₃,hm₁⟩ := mergeRect_one_top M B i₁ j₃ htop h₁
    have hi₃ : i₃.val < p := by
      by_contra hn
      have hj₂0 : j₂.val ≠ 0 := by have := j₁.isLt; change j₁.val < j₂.val at hj₁; omega
      obtain ⟨hc₂,_⟩ := mergeRect_one_lower M B i₃ j₂ (by omega) hj₂0 h₃
      change j₂.val < j₃.val at hj₂
      omega
    have hi₂' : i₂.val < p := lt_trans hi₂ hi₃
    obtain ⟨hc₁,hm₂⟩ := mergeRect_one_top M B i₂ j₁ hi₂' h₂
    obtain ⟨hc₂,hm₃⟩ := mergeRect_one_top M B i₃ j₂ hi₃ h₃
    apply hm
    refine ⟨⟨i₁.val,htop⟩,⟨i₂.val,hi₂'⟩,⟨i₃.val,hi₃⟩,
      ⟨j₁.val-1,by omega⟩,⟨j₂.val-1,by omega⟩,⟨j₃.val-1,by omega⟩,
      hi₁,hi₂,?_,?_,hm₁,hm₂,hm₃⟩
    · change j₁.val-1 < j₂.val-1
      change j₁.val < j₂.val at hj₁
      omega
    · change j₂.val-1 < j₃.val-1
      change j₂.val < j₃.val at hj₂
      omega
  · have hi₁' : p ≤ i₁.val := by omega
    have hi₂' : p ≤ i₂.val := by change i₁.val < i₂.val at hi₁; omega
    have hi₃' : p ≤ i₃.val := by change i₂.val < i₃.val at hi₂; omega
    have hj₃0 : j₃.val ≠ 0 := by change j₂.val < j₃.val at hj₂; omega
    have hj₂0 : j₂.val ≠ 0 := by change j₁.val < j₂.val at hj₁; omega
    have hj₁0 : j₁.val ≠ 0 := by
      intro hzero
      have hi₂p := mergeRect_one_zero_col hk M B i₂ j₁ hzero h₂
      change i₁.val < i₂.val at hi₁
      omega
    obtain ⟨hc₃,hb₁⟩ := mergeRect_one_lower M B i₁ j₃ hi₁' hj₃0 h₁
    obtain ⟨hc₁,hb₂⟩ := mergeRect_one_lower M B i₂ j₁ hi₂' hj₁0 h₂
    obtain ⟨hc₂,hb₃⟩ := mergeRect_one_lower M B i₃ j₂ hi₃' hj₂0 h₃
    exact hb ⟨lowerIndex i₁ hi₁',lowerIndex i₂ hi₂',lowerIndex i₃ hi₃',
      lowerIndex j₁ hc₁,lowerIndex j₂ hc₂,lowerIndex j₃ hc₃,
      lowerIndex_lt i₁ i₂ hi₁' hi₂' hi₁,lowerIndex_lt i₂ i₃ hi₂' hi₃' hi₂,
      lowerIndex_lt j₁ j₂ hc₁ hc₂ hj₁,lowerIndex_lt j₂ j₃ hc₂ hc₃ hj₂,hb₁,hb₂,hb₃⟩

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma mergeRect_one_late {p r k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (u : Fin (p+r)) (c : Fin (p+k)) (hu : p < u.val) (hone : mergeRect M B u c=1) :
    ∃ hc : p ≤ c.val, B (lowerIndex u (le_of_lt hu)) (lowerIndex c hc)=1 := by
  have hc0 : c.val ≠ 0 := by
    intro hc
    have hv := mergeRect_one_zero_col hk M B u c hc hone
    omega
  exact mergeRect_one_lower M B u c (le_of_lt hu) hc0 hone

private lemma mergeRect_deficient_source {p r k : ℕ} (hp : 0 < p) (hr : 0 < r) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hM : IsASM M) (hB : IsASR B) (c : Fin (p+k)) (hz : colSum (mergeRect M B) c=0) :
    ∃ hc : p ≤ c.val, colSum B (lowerIndex c hc)=0 := by
  have hc : p ≤ c.val := by
    by_contra hn
    have hs := mergeRect_small_colSum hp hr hk M B hM c (by omega)
    omega
  refine ⟨hc,?_⟩
  have heq : Fin.natAdd p (lowerIndex c hc)=c := by apply Fin.ext; simp [lowerIndex] <;> omega
  rw [←mergeRect_colSum hp hr hk M B hM hB,heq]
  exact hz

private lemma mergeRect_empty_source {p r k : ℕ} (hp : 0 < p) (hr : 0 < r) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hM : IsASM M) (v : Fin (p+r)) (hz : ∀ c, mergeRect M B v c=0) :
    ∃ hv : p < v.val, ∀ c, B (lowerIndex v (le_of_lt hv)) c=0 := by
  have hv : p < v.val := by
    by_cases hvt : v.val < p
    · let u : Fin p := ⟨v.val,hvt⟩
      have heq : u.castAdd r=v := by apply Fin.ext; rfl
      obtain ⟨c,hc⟩ := row_has_one hM u
      have hm := mergeRect_top hk M B u c
      rw [heq,hz] at hm
      exact (by decide : (0 : SignType) ≠ 1) (hm.trans hc) |>.elim
    · have hne : v.val ≠ p := by
        intro hEq
        have hzero := hz ⟨0,by omega⟩
        rw [mergeRect_first_col hk] at hzero
        simp [hEq] at hzero
      omega
  refine ⟨hv,?_⟩
  intro c
  let u := lowerIndex v (le_of_lt hv)
  have heq : Fin.natAdd p u=v := by apply Fin.ext; simp [u,lowerIndex] <;> omega
  have hu0 : u.val ≠ 0 := by change v.val-p ≠ 0; omega
  have hval := mergeRect_lower hp M B u c
  simp only [hu0,false_and,if_false] at hval
  rw [heq,hz] at hval
  exact hval.symm

lemma mergeRect_extAvoids {p r k : ℕ} (hp : 0 < p) (hr : 0 < r) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hM : IsASM M) (hm : ¬ Contains312 M) (hB : IsASR B) (he : ExtAvoids312 B)
    (hne : ∃ c, B ⟨0,hr⟩ c ≠ 0) : ExtAvoids312 (mergeRect M B) := by
  apply (extAvoids312_iff_safe _ (mergeRect_isASR hp hr hk M B hM hB hne)).mpr
  refine ⟨mergeRect_avoids_corner hk M B hm (extAvoids312_corner B he),?_,?_,?_⟩
  · intro u v a b c huv hab hbc h₁ h₂ hz
    obtain ⟨hbp,hbz⟩ := mergeRect_deficient_source hp hr hk M B hM hB b hz
    have hu : p ≤ u.val := by
      by_contra hut
      obtain ⟨hc,_⟩ := mergeRect_one_top M B u c (by omega) h₁
      change b.val < c.val at hbc
      omega
    have hv : p < v.val := by change u.val < v.val at huv; omega
    obtain ⟨hap,hb₂⟩ := mergeRect_one_late hk M B v a hv h₂
    have hc0 : c.val ≠ 0 := by change b.val < c.val at hbc; omega
    obtain ⟨hcp,hb₁⟩ := mergeRect_one_lower M B u c hu hc0 h₁
    exact no312_with_deficient_last B he (lowerIndex u hu) (lowerIndex v (le_of_lt hv))
      (lowerIndex a hap) (lowerIndex b hbp) (lowerIndex c hcp)
      (lowerIndex_lt u v hu (le_of_lt hv) huv) (lowerIndex_lt a b hap hbp hab)
      (lowerIndex_lt b c hbp hcp hbc) hb₁ hb₂ hbz
  · intro u v w a b huv hvw hab hempty
    rintro ⟨h₁,h₂⟩
    obtain ⟨hu,hbu⟩ := mergeRect_empty_source hp hr hk M B hM u hempty
    have hv : p < v.val := by change u.val < v.val at huv; omega
    have hw : p < w.val := by change v.val < w.val at hvw; omega
    obtain ⟨hap,hb₁⟩ := mergeRect_one_late hk M B v a hv h₁
    obtain ⟨hbp,hb₂⟩ := mergeRect_one_late hk M B w b hw h₂
    apply no12_below_empty B he (lowerIndex u (le_of_lt hu)) (lowerIndex v (le_of_lt hv))
      (lowerIndex w (le_of_lt hw)) (lowerIndex a hap) (lowerIndex b hbp)
      (lowerIndex_lt u v (le_of_lt hu) (le_of_lt hv) huv)
      (lowerIndex_lt v w (le_of_lt hv) (le_of_lt hw) hvw)
      (lowerIndex_lt a b hap hbp hab) hbu
    exact ⟨hb₁,hb₂⟩
  · intro u v a b huv hab hempty h₁ hz
    obtain ⟨hu,hbu⟩ := mergeRect_empty_source hp hr hk M B hM u hempty
    have hv : p < v.val := by change u.val < v.val at huv; omega
    obtain ⟨hap,hb₁⟩ := mergeRect_one_late hk M B v a hv h₁
    obtain ⟨hbp,hbz⟩ := mergeRect_deficient_source hp hr hk M B hM hB b hz
    exact no12_with_empty_deficient B he (lowerIndex u (le_of_lt hu)) (lowerIndex v (le_of_lt hv))
      (lowerIndex a hap) (lowerIndex b hbp) (lowerIndex_lt u v (le_of_lt hu) (le_of_lt hv) huv)
      (lowerIndex_lt a b hap hbp hab) hbu hb₁ hbz

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

lemma mergeRect_nonemptyRows {p r k : ℕ} (hp : 0 < p) (hr : 0 < r) (hk : 0 < k)
    (M : Matrix (Fin p) (Fin p) SignType) (B : Matrix (Fin r) (Fin k) SignType)
    (hM : IsASM M) (hB : IsASR B) (hne : ∃ c, B ⟨0,hr⟩ c ≠ 0) :
    nonemptyRows (mergeRect M B) = p+nonemptyRows B := by
  have hR := mergeRect_isASR hp hr hk M B hM hB hne
  have ht := asr_total_sum (mergeRect M B) hR
  rw [sum_comm] at ht
  change (∑ c, colSum (mergeRect M B) c)=(nonemptyRows (mergeRect M B) : ℤ) at ht
  rw [Fin.sum_univ_add] at ht
  have hsmall (c : Fin p) : colSum (mergeRect M B) (c.castAdd k)=1 :=
    mergeRect_small_colSum hp hr hk M B hM _ c.isLt
  simp_rw [hsmall,mergeRect_colSum hp hr hk M B hM hB] at ht
  have hb := asr_total_sum B hB
  rw [sum_comm] at hb
  change (∑ c, colSum B c)=(nonemptyRows B : ℤ) at hb
  rw [hb] at ht
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at ht
  omega

lemma all_rows_nonempty_iff {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) :
    nonemptyRows R=r ↔ ∀ u, ∃ c, R u c ≠ 0 := by
  classical
  have hb := emptyRows_balance R
  constructor
  · intro h u
    have hc : (emptyRows R).card=0 := by omega
    have hu : u ∉ emptyRows R := by rw [card_eq_zero.mp hc]; simp
    simpa only [mem_emptyRows,not_forall] using hu
  · intro h
    have hc : emptyRows R=∅ := by
      apply eq_empty_of_forall_notMem
      intro u hu
      obtain ⟨c,hc⟩ := h u
      exact hc ((mem_emptyRows R u).mp hu c)
    simpa [hc] using hb

lemma asm_nonemptyRows {n : ℕ} (M : Matrix (Fin n) (Fin n) SignType) (hM : IsASM M) :
    nonemptyRows M=n := by
  apply (all_rows_nonempty_iff M).mpr
  intro u
  apply (asr_row_sum_one_iff M hM.1 u).mp
  exact hM.2.1 u

lemma square_count_isASM {n : ℕ} (M : Matrix (Fin n) (Fin n) SignType)
    (hM : IsASR M) (hd : nonemptyRows M=n) : IsASM M := by
  refine ⟨hM,?_,?_⟩
  · intro u
    exact (asr_row_sum_one_iff M hM u).mpr ((all_rows_nonempty_iff M).mp hd u)
  · exact balanced_column_sum M hM hd

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction
