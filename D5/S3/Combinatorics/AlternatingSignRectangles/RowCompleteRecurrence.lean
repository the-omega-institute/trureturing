/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/RowCompleteRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: RowCompleteRecurrence for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
zeroColumn_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.firstEmptyZeroColumnEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumnFibreEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_isASR_inv, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_nonemptyRows, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_one_origin, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_reconstruct
zeroColumn_succ: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.firstEmptyZeroColumnEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumnFibreEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_isASR_inv, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_nonemptyRows, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_one_origin
zeroColumn_isASR: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumnFibreEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids
zeroColumn_colSum: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids_inv
zeroColumn_nonemptyRows: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.extractZeroColumn, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumnFibreEquiv
zeroColumn_isASR_inv: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.extractZeroColumn
zeroColumn_reconstruct: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.firstEmptyZeroColumnEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.extractZeroColumn, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumnFibreEquiv
zeroColumn_one_origin: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids
zeroColumn_extAvoids: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids
zeroColumn_extAvoids_inv: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids_inv
zeroColumnFibre_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids_inv
pivot_before_nonempty_of_deficit: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
pivot_before_nonempty: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
pivot_nonempty_bound: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.pivot_nonempty_bound
positivePivot_iff: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.pivot_nonempty_bound
pivotNonzeroFibre_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
positiveFirst_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.pivot_nonempty_bound
nonzeroFirst_iff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.rectangleFirstColEquiv
rectangle_merge_nat: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.pivot_nonempty_bound
S_row_shift_nat: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.pivot_nonempty_bound
sum_Icc_two: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.S_interior, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.S_row
S_row: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.pivot_nonempty_bound
Direct frozen dependencies: none; the ASR prerequisites are same-delivery content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

def zeroColumn {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) : Matrix (Fin r) (Fin (k+1)) SignType :=
  fun u => Fin.cons 0 (B u)

@[simp] lemma zeroColumn_zero {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) (u : Fin r) : zeroColumn B u 0=0 := by simp [zeroColumn]

@[simp] lemma zeroColumn_succ {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) (u : Fin r) (c : Fin k) : zeroColumn B u c.succ=B u c := by simp [zeroColumn]

private lemma zeroColumn_isASR {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) (hB : IsASR B) : IsASR (zeroColumn B) := by
  refine ⟨?_,?_⟩
  · intro u
    exact ⟨(cons_zero_line _ (hB.1 u).1 (hB.1 u).2.1).1,
      (cons_zero_line _ (hB.1 u).1 (hB.1 u).2.1).2,cons_zero_ends _ (hB.1 u).2.2⟩
  · intro c
    refine Fin.cases ?_ (fun c => ?_) c
    · constructor
      · intro u v _ hu _ _
        simp at hu
      · intro u hu _
        simp at hu
    · exact hB.2 c

private lemma zeroColumn_colSum {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) (c : Fin k) :
    colSum (zeroColumn B) c.succ=colSum B c := by unfold colSum; simp

private lemma zeroColumn_nonemptyRows {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) :
    nonemptyRows (zeroColumn B)=nonemptyRows B := by
  unfold nonemptyRows
  congr 1
  ext u
  simp only [mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨c,hc⟩
    rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨c,rfl⟩
    · simp at hc
    · exact ⟨c,by simpa using hc⟩
  · rintro ⟨c,hc⟩
    exact ⟨c.succ,by simpa using hc⟩

private lemma zeroColumn_isASR_inv {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR (zeroColumn B)) : IsASR B := by
  have hf : StrictMono (Fin.succ : Fin k → Fin (k+1)) := by intro u v huv; simpa using huv
  have hout (u : Fin r) (c : Fin (k+1)) (hc : ¬ ∃ b : Fin k, b.succ=c) : zeroColumn B u c=0 := by
    revert hc
    refine Fin.cases (fun _ => by simp) (fun b hc => (hc ⟨b,rfl⟩).elim) c
  refine ⟨?_,?_⟩
  · intro u
    have hr := hR.1 u
    have hl := line_restrict (B u) (zeroColumn B u) Fin.succ hf (zeroColumn_succ B u) (hout u) hr.1 hr.2.1
    exact ⟨hl.1,hl.2,ends_restrict _ _ Fin.succ hf (zeroColumn_succ B u) (hout u) hr.2.2⟩
  · intro c
    exact hR.2 c.succ

private def cutZeroColumn {r k : ℕ} (R : Matrix (Fin r) (Fin (k+1)) SignType) : Matrix (Fin r) (Fin k) SignType :=
  fun u c => R u c.succ

lemma zeroColumn_reconstruct {r k : ℕ} (R : Matrix (Fin r) (Fin (k+1)) SignType)
    (hz : ∀ u, R u 0=0) : zeroColumn (cutZeroColumn R)=R := by
  ext u c
  refine Fin.cases (by simpa using (hz u).symm) (fun c => by rfl) c

end D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma zeroColumn_one_origin {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (u : Fin r) (c : Fin (k+1)) (hone : zeroColumn B u c=1) : ∃ b, c=b.succ ∧ B u b=1 := by
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨b,rfl⟩
  · simp at hone
  · exact ⟨b,rfl,by simpa using hone⟩

private lemma zeroColumn_extAvoids {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (hB : IsASR B) (he : ExtAvoids312 B) : ExtAvoids312 (zeroColumn B) := by
  apply (extAvoids312_iff_safe _ (zeroColumn_isASR B hB)).mpr
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨u,v,w,a,b,c,hu,hv,ha,hb,h₁,h₂,h₃⟩
    obtain ⟨c',rfl,hb₁⟩ := zeroColumn_one_origin B u c h₁
    obtain ⟨a',rfl,hb₂⟩ := zeroColumn_one_origin B v a h₂
    obtain ⟨b',rfl,hb₃⟩ := zeroColumn_one_origin B w b h₃
    exact extAvoids312_corner B he ⟨u,v,w,a',b',c',hu,hv,by simpa using ha,by simpa using hb,hb₁,hb₂,hb₃⟩
  · intro u v a b c hu ha hb h₁ h₂ hz
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b',rfl⟩
    · exact (Fin.not_lt_zero a ha).elim
    · obtain ⟨c',rfl,hb₁⟩ := zeroColumn_one_origin B u c h₁
      obtain ⟨a',rfl,hb₂⟩ := zeroColumn_one_origin B v a h₂
      exact no312_with_deficient_last B he u v a' b' c' hu (by simpa using ha) (by simpa using hb)
        hb₁ hb₂ (by simpa only [zeroColumn_colSum] using hz)
  · intro u v w a b hu hv hab hempty
    rintro ⟨h₁,h₂⟩
    obtain ⟨a',rfl,hb₁⟩ := zeroColumn_one_origin B v a h₁
    obtain ⟨b',rfl,hb₂⟩ := zeroColumn_one_origin B w b h₂
    apply no12_below_empty B he u v w a' b' hu hv (by simpa using hab)
    · intro c; simpa using hempty c.succ
    · exact ⟨hb₁,hb₂⟩
  · intro u v a b hu hab hempty h₁ hz
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b',rfl⟩
    · exact (Fin.not_lt_zero a hab).elim
    · obtain ⟨a',rfl,hb₁⟩ := zeroColumn_one_origin B v a h₁
      apply no12_with_empty_deficient B he u v a' b' hu (by simpa using hab)
      · intro c; simpa using hempty c.succ
      · exact hb₁
      · simpa only [zeroColumn_colSum] using hz

private lemma zeroColumn_extAvoids_inv {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (hB : IsASR B) (he : ExtAvoids312 (zeroColumn B)) : ExtAvoids312 B := by
  apply (extAvoids312_iff_safe B hB).mpr
  have hf : StrictMono (Fin.succ : Fin k → Fin (k+1)) := by intro a b hab; simpa using hab
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨u,v,w,a,b,c,hu,hv,ha,hb,h₁,h₂,h₃⟩
    exact extAvoids312_corner (zeroColumn B) he ⟨u,v,w,a.succ,b.succ,c.succ,hu,hv,hf ha,hf hb,
      by simpa using h₁,by simpa using h₂,by simpa using h₃⟩
  · intro u v a b c hu ha hb h₁ h₂ hz
    exact no312_with_deficient_last (zeroColumn B) he u v a.succ b.succ c.succ hu (hf ha) (hf hb)
      (by simpa using h₁) (by simpa using h₂) (by simpa only [zeroColumn_colSum] using hz)
  · intro u v w a b hu hv hab hempty
    apply no12_below_empty (zeroColumn B) he u v w a.succ b.succ hu hv (hf hab)
    intro c
    refine Fin.cases (by simp) (fun c => by simpa using hempty c) c
  · intro u v a b hu hab hempty h₁ hz
    apply no12_with_empty_deficient (zeroColumn B) he u v a.succ b.succ hu (hf hab)
    · intro c
      refine Fin.cases (by simp) (fun c => by simpa using hempty c) c
    · simpa using h₁
    · simpa only [zeroColumn_colSum] using hz

end D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
noncomputable section

abbrev ZeroColumnFibre (r k d : ℕ) := {R : Counted r (k+1) d // ∀ u, R.val u 0=0}

def extractZeroColumn {r k d : ℕ} (R : ZeroColumnFibre r k d) : Counted r k d := by
  let B := cutZeroColumn R.val.val
  have hi : zeroColumn B=R.val.val := zeroColumn_reconstruct R.val.val R.property
  have hR : IsASR (zeroColumn B) := by rw [hi]; exact R.val.property.1
  have hB := zeroColumn_isASR_inv B hR
  have he : ExtAvoids312 (zeroColumn B) := by rw [hi]; exact R.val.property.2.1
  have hd : nonemptyRows B=d := by
    rw [←zeroColumn_nonemptyRows B,hi]
    exact R.val.property.2.2
  exact ⟨B,hB,zeroColumn_extAvoids_inv B hB he,hd⟩

def zeroColumnFibreEquiv (r k d : ℕ) : ZeroColumnFibre r k d ≃ Counted r k d where
  toFun := extractZeroColumn
  invFun := fun B => ⟨⟨zeroColumn B.val,zeroColumn_isASR B.val B.property.1,
    zeroColumn_extAvoids B.val B.property.1 B.property.2.1,by
      rw [zeroColumn_nonemptyRows B.val,B.property.2.2]⟩,by intro u; simp⟩
  left_inv := by
    intro R
    apply Subtype.ext
    apply Subtype.ext
    exact zeroColumn_reconstruct R.val.val R.property
  right_inv := by
    intro B
    apply Subtype.ext
    ext u c
    exact zeroColumn_succ B.val u c

private lemma zeroColumnFibre_card (r k d : ℕ) : Nat.card (ZeroColumnFibre r k d)=S r k d :=
  Nat.card_congr (zeroColumnFibreEquiv r k d)

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

lemma pivot_before_nonempty_of_deficit {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩=1) (hd : nonemptyRows R < k) :
    ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0 := by
  have hbal := deficientColumns_balance R hR
  have hcard : 0 < (deficientColumns R).card := by omega
  obtain ⟨c,hc⟩ := card_pos.mp hcard
  have hz := (mem_deficientColumns R c).mp hc
  have hc0 : 0 < c.val := by
    by_contra hn
    have hce : c=⟨0,hk⟩ := Fin.ext (by change c.val=0; omega)
    have hs : colSum R ⟨0,hk⟩=1 := by
      unfold colSum
      simp_rw [first_column_zero_except_pivot R hR hk i hfirst]
      have hv (v : Fin r) : ((if v=i then 1 else 0 : SignType) : ℤ)=if v=i then 1 else 0 := by
        split_ifs <;> rfl
      simp_rw [hv]
      simp
    rw [hce] at hz
    omega
  intro v hvi
  by_contra hn
  push_neg at hn
  have hv : ∀ c, R v c=0 := hn
  exact no12_with_empty_deficient R he v i ⟨0,hk⟩ c hvi hc0 hv hfirst hz

private lemma pivot_before_nonempty {r k d : ℕ} (R : Counted r k d) (hk : 0 < k)
    (i : Fin r) (hfirst : R.val i ⟨0,hk⟩=1) (hgood : d < k ∨ d=r) :
    ∀ v : Fin r, v.val < i.val → ∃ c, R.val v c ≠ 0 := by
  rcases hgood with hd | hd
  · exact pivot_before_nonempty_of_deficit R.val R.property.1 R.property.2.1 hk i hfirst
      (by rw [R.property.2.2]; exact hd)
  · intro v _
    exact (all_rows_nonempty_iff R.val).mp (R.property.2.2.trans hd) v

private lemma pivot_nonempty_bound {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hk : 0 < k) (i : Fin r) (hfirst : R i ⟨0,hk⟩=1)
    (hbefore : ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0) : i.val < nonemptyRows R := by
  classical
  let f : Fin (i.val+1) → {v : Fin r // ∃ c, R v c ≠ 0} := fun u =>
    ⟨⟨u.val,by have := u.isLt; have := i.isLt; omega⟩,by
      by_cases hu : u.val < i.val
      · exact hbefore _ hu
      · have heq : (⟨u.val,by have := u.isLt; have := i.isLt; omega⟩ : Fin r)=i := by
          apply Fin.ext; change u.val=i.val; have := u.isLt; omega
        refine ⟨⟨0,hk⟩,?_⟩
        rw [heq,hfirst]
        decide⟩
  have hf : Function.Injective f := by
    intro u v heq
    apply Fin.ext
    exact congrArg (fun x => x.val.val) heq
  have hc := Nat.card_le_card_of_injective f hf
  rw [←nonemptyRows_eq_card_subtype R,Nat.card_fin] at hc
  omega

end D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset
noncomputable section

private abbrev PositiveFirst (r k d : ℕ) (hk : 0 < k) := {R : Counted r k d // ∃ i, R.val i ⟨0,hk⟩=1}

private abbrev PivotFibre (r k d : ℕ) (hrd : d ≤ r) (hkd : d ≤ k) (p : Fin d) :=
  {R : Counted r k d // R.val ⟨p.val,by have := p.isLt; omega⟩ ⟨0,by have := p.isLt; omega⟩=1}

private def positivePivot {r k d : ℕ} (hk : 0 < k) (hgood : d < k ∨ d=r) (R : PositiveFirst r k d hk) : Fin d := by
  let i := Classical.choose R.property
  have hi : R.val.val i ⟨0,hk⟩=1 := Classical.choose_spec R.property
  have hb := pivot_before_nonempty R.val hk i hi hgood
  have hbound := pivot_nonempty_bound R.val.val hk i hi hb
  rw [R.val.property.2.2] at hbound
  exact ⟨i.val,hbound⟩

private lemma positivePivot_iff {r k d : ℕ} (hk : 0 < k) (hrd : d ≤ r) (hkd : d ≤ k)
    (hgood : d < k ∨ d=r) (R : PositiveFirst r k d hk) (p : Fin d) :
    positivePivot hk hgood R=p ↔ R.val.val ⟨p.val,by have := p.isLt; omega⟩ ⟨0,hk⟩=1 := by
  let i := Classical.choose R.property
  have hi : R.val.val i ⟨0,hk⟩=1 := Classical.choose_spec R.property
  have hval : (positivePivot hk hgood R).val=i.val := rfl
  constructor
  · intro hp
    have hir : i=(⟨p.val,by have := p.isLt; omega⟩ : Fin r) := by
      apply Fin.ext
      simpa only [hp] using hval.symm
    simpa only [hir] using hi
  · intro hp
    have hir := asr_first_col_one_unique R.val.val R.val.property.1 hk i
      ⟨p.val,by have := p.isLt; omega⟩ hi hp
    apply Fin.ext
    rw [hval]
    exact congrArg Fin.val hir

private def positivePivotFibreEquiv {r k d : ℕ} (hk : 0 < k) (hrd : d ≤ r) (hkd : d ≤ k)
    (hgood : d < k ∨ d=r) (p : Fin d) :
    {R : PositiveFirst r k d hk // positivePivot hk hgood R=p} ≃ PivotFibre r k d hrd hkd p :=
  (Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
    (Equiv.subtypeEquivRight fun R =>
      ⟨fun h => (positivePivot_iff hk hrd hkd hgood ⟨R,h.1⟩ p).mp h.2,
        fun h => ⟨⟨⟨p.val,by have := p.isLt; omega⟩,h⟩,
          (positivePivot_iff hk hrd hkd hgood _ p).mpr h⟩⟩)

private def positivePivotEquiv {r k d : ℕ} (hk : 0 < k) (hrd : d ≤ r) (hkd : d ≤ k)
    (hgood : d < k ∨ d=r) : PositiveFirst r k d hk ≃ Σ p : Fin d, PivotFibre r k d hrd hkd p :=
  (Equiv.sigmaFiberEquiv (positivePivot hk hgood)).symm.trans
    (Equiv.sigmaCongrRight fun p => positivePivotFibreEquiv hk hrd hkd hgood p)

private def pivotColumnFibreEquiv {r k d : ℕ} (hrd : d ≤ r) (hkd : d ≤ k)
    (hgood : d < k ∨ d=r) (p : Fin d) :
    PivotFibre r k d hrd hkd p ≃ ColumnFibre r k d p.val (by have := p.isLt; omega) (by have := p.isLt; omega) :=
  (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun R : Matrix (Fin r) (Fin k) SignType => IsASR R ∧ ExtAvoids312 R ∧ nonemptyRows R=d)
    (fun R => R ⟨p.val,by have := p.isLt; omega⟩ ⟨0,by have := p.isLt; omega⟩=1)).trans
    (Equiv.subtypeEquivRight fun R =>
      ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2,
        pivot_before_nonempty ⟨R,h.1⟩ (by have := p.isLt; omega) _ h.2 hgood⟩,
        fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2.1⟩⟩)

private lemma pivotNonzeroFibre_card {r k d : ℕ} (hrd : d ≤ r) (hkd : d ≤ k)
    (hgood : d < k ∨ d=r) (p : Fin d) (hp : 0 < p.val) :
    Nat.card (PivotFibre r k d hrd hkd p)=Nat.card (AvoidASM p.val)*
      Nat.card (FirstNonempty (r-p.val) (k-p.val) (d-p.val) (by have := p.isLt; omega)) := by
  rw [Nat.card_congr (pivotColumnFibreEquiv hrd hkd hgood p),firstColumnFactor_card]
  exacts [hp,by have := p.isLt; omega]

lemma positiveFirst_card (r k d : ℕ) (hrd : d ≤ r) (hkd : d ≤ k) (hgood : d < k ∨ d=r) :
    Nat.card (PositiveFirst (r+1) (k+1) (d+1) (by omega)) = S r k d+
      ∑ p : Fin d, Nat.card (AvoidASM (p.val+1))*
        Nat.card (FirstNonempty (r-p.val) (k-p.val) (d-p.val) (by have := p.isLt; omega)) := by
  classical
  letI : Fintype (PositiveFirst (r+1) (k+1) (d+1) (by omega)) := Fintype.ofFinite _
  let hr' : d+1 ≤ r+1 := by omega
  let hk' : d+1 ≤ k+1 := by omega
  let hg : d+1 < k+1 ∨ d+1=r+1 := by omega
  letI : ∀ p : Fin (d+1), Fintype (PivotFibre (r+1) (k+1) (d+1) hr' hk' p) := fun p => Fintype.ofFinite _
  rw [Nat.card_congr (positivePivotEquiv (show 0 < k+1 by omega) hr' hk' hg),
    Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp_rw [←Nat.card_eq_fintype_card]
  rw [Fin.sum_univ_succ]
  change Nat.card (TopLeftFibre r k d) + _ = _
  rw [topLeftFibre_card]
  congr 1
  apply sum_congr rfl
  intro p _
  simpa only [Fin.val_succ,Nat.add_sub_add_right] using pivotNonzeroFibre_card hr' hk' hg p.succ (by simp)

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset
noncomputable section

private lemma nonzeroFirst_iff {r k d : ℕ} (hk : 0 < k) (R : Counted r k d) :
    (¬ ∀ u, R.val u ⟨0,hk⟩=0) ↔ ∃ u, R.val u ⟨0,hk⟩=1 := by
  classical
  constructor
  · intro hn
    push_neg at hn
    obtain ⟨u,hu⟩ := hn
    have hm := asr_first_col_not_minus R.val R.property.1 hk u
    refine ⟨u,?_⟩
    cases hs : R.val u ⟨0,hk⟩ <;> simp_all
  · rintro ⟨u,hu⟩ hz
    have hf := hz u
    rw [hu] at hf
    exact (by decide : (1 : SignType) ≠ 0) hf

private def rectangleFirstColEquiv (r k d : ℕ) :
    Counted r (k+1) d ≃ ZeroColumnFibre r k d ⊕ PositiveFirst r (k+1) d (by omega) :=
  (Equiv.sumCompl (fun R : Counted r (k+1) d => ∀ u, R.val u 0=0)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivProp
      (funext fun R => propext (nonzeroFirst_iff (by omega) R))))

lemma rectangle_merge_nat (r k d : ℕ) (hrd : d ≤ r) (hkd : d ≤ k) (hgood : d < k ∨ d=r) :
    S (r+1) (k+1) (d+1)=S (r+1) k (d+1)+S r k d+
      ∑ p : Fin d, Nat.card (AvoidASM (p.val+1))*
        Nat.card (FirstNonempty (r-p.val) (k-p.val) (d-p.val) (by have := p.isLt; omega)) := by
  rw [show S (r+1) (k+1) (d+1)=Nat.card (Counted (r+1) (k+1) (d+1)) from rfl,
    Nat.card_congr (rectangleFirstColEquiv (r+1) k (d+1)),Nat.card_sum,zeroColumnFibre_card,
    positiveFirst_card r k d hrd hkd hgood]
  omega

private lemma S_row_shift_nat (r k : ℕ) (hrk : r ≤ k) :
    S (r+1) (k+1) (r+1)=S (r+1) k (r+1)+S r k r+
      ∑ p : Fin r, Nat.largeSchroder p.val*S (r-p.val) (k-p.val) (r-p.val) := by
  rw [rectangle_merge_nat r k r (le_refl _) hrk (Or.inr rfl)]
  congr 1
  apply sum_congr rfl
  intro p _
  rw [avoidingASM_card_schroder]
  congr 1
  exact Nat.card_congr (fullFirstNonemptyEquiv (r-p.val) (k-p.val) (by have := p.isLt; omega))

lemma sum_Icc_two {α : Type} [AddCommMonoid α] (r : ℕ) (hr : 0 < r) (f : ℕ → α) :
    (∑ i : ↥(Icc 2 r), f i.val)=∑ p : Fin (r-1), f (p.val+2) := by
  classical
  apply sum_bij (fun i _ => (⟨i.val-2,by have := mem_Icc.mp i.property; omega⟩ : Fin (r-1)))
  · intro _ _; exact mem_univ _
  · intro i _ j _ heq
    apply Subtype.ext
    have hi := mem_Icc.mp i.property
    have hj := mem_Icc.mp j.property
    have hv := congrArg Fin.val heq
    change i.val-2=j.val-2 at hv
    omega
  · intro p _
    refine ⟨⟨p.val+2,mem_Icc.mpr ⟨by omega,by have := p.isLt; omega⟩⟩,mem_univ _,?_⟩
    apply Fin.ext
    simp
  · intro i _
    congr 1
    change i.val=(i.val-2)+2
    have hi := mem_Icc.mp i.property
    omega

lemma S_row (r k : ℕ) (hr : 0 < r) (hrk : r < k) :
    (S r k r : ℤ)=(S r (k-1) r : ℤ)+(S (r-1) (k-1) (r-1) : ℤ)+
      ∑ i : ↥(Icc 2 r), (Nat.largeSchroder (i.val-2) : ℤ)*
        (S (r+1-i.val) (k+1-i.val) (r+1-i.val) : ℤ) := by
  have hnat := S_row_shift_nat (r-1) (k-1) (by omega)
  have hr' : (r-1)+1=r := by omega
  have hk' : (k-1)+1=k := by omega
  rw [hr',hk'] at hnat
  have hint : (S r k r : ℤ)=(S r (k-1) r : ℤ)+(S (r-1) (k-1) (r-1) : ℤ)+
      ∑ p : Fin (r-1), (Nat.largeSchroder p.val : ℤ)*(S (r-1-p.val) (k-1-p.val) (r-1-p.val) : ℤ) := by
    exact_mod_cast hnat
  rw [hint,sum_Icc_two r hr (fun i => (Nat.largeSchroder (i-2) : ℤ)*
    (S (r+1-i) (k+1-i) (r+1-i) : ℤ))]
  congr 1
  apply sum_congr rfl
  intro p _
  have hi : (p.val+2)-2=p.val := by omega
  have hrp : r+1-(p.val+2)=r-1-p.val := by have := p.isLt; omega
  have hkp : k+1-(p.val+2)=k-1-p.val := by have := p.isLt; omega
  rw [hi,hrp,hkp]

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence
