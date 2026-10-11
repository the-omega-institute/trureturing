/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: SquareASMDecomposition for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
cons_zero_line: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR
cons_zero_ends: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR
topLeft_zero_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeftFibreEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_first_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_reconstruct
topLeft_zero_succ: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_one_noncorner, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_reconstruct
topLeft_succ_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_first_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_one_noncorner, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_reconstruct
topLeft_succ_succ: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeftFibreEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_one_noncorner
topLeft_isASR: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeftFibreEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_nonemptyRows
topLeft_colSum: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_nonemptyRows
topLeft_first_colSum: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_nonemptyRows
topLeft_nonemptyRows: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
topLeft_one_noncorner: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids
topLeft_extAvoids: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids
topLeft_reconstruct: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.extractTopLeft, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeftFibreEquiv
topLeft_isASR_inv: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.extractTopLeft
topLeft_extAvoids_inv: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv
topLeftFibre_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv
asmZeroFibre_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv
asmPivot_spec: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.asmPivot_fibre_iff
asmPivot_fibre_iff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.asmPivotEquiv
asm_succ_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv
avoidingASM_card_schroder: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.avoidingASM_card_schroder
S_diagonal_nat: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.avoidingASM_card_schroder
S_diagonal: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.avoidingASM_card_schroder
Direct frozen dependencies: none; the ASR prerequisites are same-delivery content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition
import Mathlib.Combinatorics.Enumerative.Schroder

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

lemma cons_zero_line {n : ℕ} (a : Fin n → SignType)
    (ha : Alternates a) (hs : StartsOne a) :
    Alternates (Fin.cons 0 a) ∧ StartsOne (Fin.cons 0 a) := by
  have hf : StrictMono (Fin.succ : Fin n → Fin (n+1)) := by intro u v huv; simpa using huv
  have hout (x : Fin (n+1)) (hx : ¬ ∃ u : Fin n, u.succ=x) : (Fin.cons (0 : SignType) a : Fin (n+1) → SignType) x=0 := by
    revert hx
    refine Fin.cases (fun _ => by simp) (fun u hx => ?_) x
    exact (hx ⟨u,rfl⟩).elim
  exact line_embed a (Fin.cons 0 a) Fin.succ hf (by intro u; simp) hout ha hs

lemma cons_zero_ends {n : ℕ} (a : Fin n → SignType) (he : EndsOne a) :
    EndsOne (Fin.cons 0 a) := by
  have hf : StrictMono (Fin.succ : Fin n → Fin (n+1)) := by intro u v huv; simpa using huv
  have hout (x : Fin (n+1)) (hx : ¬ ∃ u : Fin n, u.succ=x) : (Fin.cons (0 : SignType) a : Fin (n+1) → SignType) x=0 := by
    revert hx
    refine Fin.cases (fun _ => by simp) (fun u hx => ?_) x
    exact (hx ⟨u,rfl⟩).elim
  exact ends_embed a (Fin.cons 0 a) Fin.succ hf (by intro u; simp) hout he

private def topLeft {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) :
    Matrix (Fin (r+1)) (Fin (k+1)) SignType :=
  Fin.cons (Fin.cons 1 (fun _ => 0)) (fun u => Fin.cons 0 (B u))

@[simp] private lemma topLeft_zero_zero {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) : topLeft B 0 0=1 := by simp [topLeft]

@[simp] private lemma topLeft_zero_succ {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) (c : Fin k) : topLeft B 0 c.succ=0 := by simp [topLeft]

@[simp] private lemma topLeft_succ_zero {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) (u : Fin r) : topLeft B u.succ 0=0 := by simp [topLeft]

@[simp] private lemma topLeft_succ_succ {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) (u : Fin r) (c : Fin k) : topLeft B u.succ c.succ=B u c := by simp [topLeft]

private lemma topLeft_isASR {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) (hB : IsASR B) : IsASR (topLeft B) := by
  have hfirst : (Fin.cons (1 : SignType) (fun _ : Fin k => 0)) =
      (fun c : Fin (k+1) => if (0 : Fin (k+1))=c then (1 : SignType) else 0) := by
    funext c
    refine Fin.cases (by simp) (fun c => by simp [eq_comm]) c
  refine ⟨?_,?_⟩
  · intro u
    refine Fin.cases ?_ (fun u => ?_) u
    · change Alternates (Fin.cons 1 (fun _ : Fin k => 0)) ∧ StartsOne (Fin.cons 1 (fun _ : Fin k => 0)) ∧ EndsOne (Fin.cons 1 (fun _ : Fin k => 0))
      rw [hfirst]
      exact singleton_line _
    · change Alternates (Fin.cons 0 (B u)) ∧ StartsOne _ ∧ EndsOne _
      exact ⟨(cons_zero_line _ (hB.1 u).1 (hB.1 u).2.1).1,
        (cons_zero_line _ (hB.1 u).1 (hB.1 u).2.1).2,cons_zero_ends _ (hB.1 u).2.2⟩
  · intro c
    refine Fin.cases ?_ (fun c => ?_) c
    · have heq : (fun u => topLeft B u 0)=
          (fun u : Fin (r+1) => if (0 : Fin (r+1))=u then 1 else 0) := by
        funext u; refine Fin.cases (by simp) (fun u => by simp [eq_comm]) u
      rw [heq]
      exact ⟨(singleton_line _).1,(singleton_line _).2.1⟩
    · have heq : (fun u => topLeft B u c.succ)=Fin.cons 0 (fun u => B u c) := by
        funext u; refine Fin.cases (by simp) (fun u => by simp [eq_comm]) u
      rw [heq]
      exact cons_zero_line _ (hB.2 c).1 (hB.2 c).2

private lemma topLeft_colSum {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) (c : Fin k) :
    colSum (topLeft B) c.succ=colSum B c := by
  unfold colSum
  rw [Fin.sum_univ_succ]
  simp

private lemma topLeft_first_colSum {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) :
    colSum (topLeft B) 0=1 := by unfold colSum; rw [Fin.sum_univ_succ]; simp

private lemma topLeft_nonemptyRows {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType) (hB : IsASR B) :
    nonemptyRows (topLeft B)=nonemptyRows B+1 := by
  have ht := asr_total_sum (topLeft B) (topLeft_isASR B hB)
  rw [sum_comm] at ht
  change (∑ c, colSum (topLeft B) c)=(nonemptyRows (topLeft B) : ℤ) at ht
  rw [Fin.sum_univ_succ,topLeft_first_colSum] at ht
  simp_rw [topLeft_colSum] at ht
  have hb := asr_total_sum B hB
  rw [sum_comm] at hb
  change (∑ c, colSum B c)=(nonemptyRows B : ℤ) at hb
  rw [hb] at ht
  omega

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma topLeft_one_noncorner {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (u : Fin (r+1)) (c : Fin (k+1)) (hn : u.val ≠ 0 ∨ c.val ≠ 0) (hone : topLeft B u c=1) :
    ∃ v b, u=v.succ ∧ c=b.succ ∧ B v b=1 := by
  rcases Fin.eq_zero_or_eq_succ u with rfl | ⟨v,rfl⟩
  · rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨b,rfl⟩
    · simp at hn
    · simp at hone
  · rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨b,rfl⟩
    · simp at hone
    · exact ⟨v,b,rfl,rfl,by simpa only [topLeft_succ_succ] using hone⟩

private lemma topLeft_extAvoids {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (hB : IsASR B) (he : ExtAvoids312 B) : ExtAvoids312 (topLeft B) := by
  apply (extAvoids312_iff_safe _ (topLeft_isASR B hB)).mpr
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨u,v,w,a,b,c,hu,hv,ha,hb,h₁,h₂,h₃⟩
    obtain ⟨u',c',rfl,rfl,hb₁⟩ := topLeft_one_noncorner B u c
      (Or.inr (by change b.val < c.val at hb; omega)) h₁
    obtain ⟨v',a',rfl,rfl,hb₂⟩ := topLeft_one_noncorner B v a
      (Or.inl (by change u'.val+1 < v.val at hu; omega)) h₂
    obtain ⟨w',b',rfl,rfl,hb₃⟩ := topLeft_one_noncorner B w b
      (Or.inl (by change v'.val+1 < w.val at hv; omega)) h₃
    exact extAvoids312_corner B he ⟨u',v',w',a',b',c',by simpa using hu,
      by simpa using hv,by simpa using ha,by simpa using hb,hb₁,hb₂,hb₃⟩
  · intro u v a b c hu ha hb h₁ h₂ hz
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b',rfl⟩
    · rw [topLeft_first_colSum] at hz
      omega
    · obtain ⟨u',c',rfl,rfl,hb₁⟩ := topLeft_one_noncorner B u c
        (Or.inr (by change b'.val+1 < c.val at hb; omega)) h₁
      obtain ⟨v',a',rfl,rfl,hb₂⟩ := topLeft_one_noncorner B v a
        (Or.inl (by change u'.val+1 < v.val at hu; omega)) h₂
      exact no312_with_deficient_last B he u' v' a' b' c' (by simpa using hu)
        (by simpa using ha) (by simpa using hb) hb₁ hb₂ (by simpa only [topLeft_colSum] using hz)
  · intro u v w a b hu hv hab hempty
    rcases Fin.eq_zero_or_eq_succ u with rfl | ⟨u',rfl⟩
    · have hf := hempty 0
      simp at hf
    · rintro ⟨h₁,h₂⟩
      obtain ⟨v',a',rfl,rfl,hb₁⟩ := topLeft_one_noncorner B v a
        (Or.inl (by change u'.val+1 < v.val at hu; omega)) h₁
      obtain ⟨w',b',rfl,rfl,hb₂⟩ := topLeft_one_noncorner B w b
        (Or.inl (by change v'.val+1 < w.val at hv; omega)) h₂
      apply no12_below_empty B he u' v' w' a' b' (by simpa using hu) (by simpa using hv) (by simpa using hab)
      · intro c
        simpa only [topLeft_succ_succ] using hempty c.succ
      · exact ⟨hb₁,hb₂⟩
  · intro u v a b hu hab hempty h₁ hz
    rcases Fin.eq_zero_or_eq_succ u with rfl | ⟨u',rfl⟩
    · have hf := hempty 0
      simp at hf
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b',rfl⟩
      · rw [topLeft_first_colSum] at hz
        omega
      · obtain ⟨v',a',rfl,rfl,hb₁⟩ := topLeft_one_noncorner B v a
          (Or.inl (by change u'.val+1 < v.val at hu; omega)) h₁
        apply no12_with_empty_deficient B he u' v' a' b' (by simpa using hu) (by simpa using hab)
        · intro c
          simpa only [topLeft_succ_succ] using hempty c.succ
        · exact hb₁
        · simpa only [topLeft_colSum] using hz

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private def cutTopLeft {r k : ℕ} (R : Matrix (Fin (r+1)) (Fin (k+1)) SignType) :
    Matrix (Fin r) (Fin k) SignType := fun u c => R u.succ c.succ

private lemma topLeft_reconstruct {r k : ℕ} (R : Matrix (Fin (r+1)) (Fin (k+1)) SignType)
    (hR : IsASR R) (h00 : R 0 0=1) : topLeft (cutTopLeft R)=R := by
  have hrow := line_no_minus_singleton (R 0) (hR.1 0).1
    (asr_first_row_not_minus R hR (by omega)) 0 h00
  have hcol := first_column_zero_except_pivot R hR (by omega) 0 h00
  ext u c
  refine Fin.cases ?_ (fun u => ?_) u
  · refine Fin.cases (by simp [h00]) (fun c => ?_) c
    simp only [topLeft_zero_succ]
    have hs := hrow c.succ
    simpa [eq_comm] using hs.symm
  · refine Fin.cases ?_ (fun c => by rfl) c
    simp only [topLeft_succ_zero]
    have hs := hcol u.succ
    simpa [eq_comm] using hs.symm

private lemma topLeft_isASR_inv {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR (topLeft B)) : IsASR B := by
  have hf {n : ℕ} : StrictMono (Fin.succ : Fin n → Fin (n+1)) := by intro u v huv; simpa using huv
  have hout {n : ℕ} (a : Fin n → SignType) (x : Fin (n+1)) (hx : ¬ ∃ u : Fin n, u.succ=x) :
      (Fin.cons (0 : SignType) a : Fin (n+1) → SignType) x=0 := by
    revert hx
    refine Fin.cases (fun _ => by simp) (fun u hx => (hx ⟨u,rfl⟩).elim) x
  refine ⟨?_,?_⟩
  · intro u
    have hr := hR.1 u.succ
    change Alternates (Fin.cons 0 (B u)) ∧ StartsOne (Fin.cons 0 (B u)) ∧ EndsOne (Fin.cons 0 (B u)) at hr
    have hl := line_restrict (B u) (Fin.cons 0 (B u)) Fin.succ hf (by intro c; simp)
      (hout (B u)) hr.1 hr.2.1
    exact ⟨hl.1,hl.2,ends_restrict _ _ Fin.succ hf (by intro c; simp) (hout (B u)) hr.2.2⟩
  · intro c
    have hc := hR.2 c.succ
    have heq : (fun u => topLeft B u c.succ)=Fin.cons 0 (fun u => B u c) := by
      funext u
      refine Fin.cases (by simp) (fun u => by simp) u
    rw [heq] at hc
    exact line_restrict _ _ Fin.succ hf (by intro u; simp) (hout (fun u => B u c)) hc.1 hc.2

private lemma topLeft_extAvoids_inv {r k : ℕ} (B : Matrix (Fin r) (Fin k) SignType)
    (hB : IsASR B) (he : ExtAvoids312 (topLeft B)) : ExtAvoids312 B := by
  apply (extAvoids312_iff_safe B hB).mpr
  have hmono {n : ℕ} : StrictMono (Fin.succ : Fin n → Fin (n+1)) := by intro u v huv; simpa using huv
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨u,v,w,a,b,c,hu,hv,ha,hb,h₁,h₂,h₃⟩
    exact extAvoids312_corner (topLeft B) he ⟨u.succ,v.succ,w.succ,a.succ,b.succ,c.succ,
      hmono hu,hmono hv,hmono ha,hmono hb,by simpa using h₁,by simpa using h₂,by simpa using h₃⟩
  · intro u v a b c hu ha hb h₁ h₂ hz
    exact no312_with_deficient_last (topLeft B) he u.succ v.succ a.succ b.succ c.succ
      (hmono hu) (hmono ha) (hmono hb) (by simpa using h₁) (by simpa using h₂) (by simpa only [topLeft_colSum] using hz)
  · intro u v w a b hu hv hab hempty
    apply no12_below_empty (topLeft B) he u.succ v.succ w.succ a.succ b.succ
      (hmono hu) (hmono hv) (hmono hab)
    intro c
    refine Fin.cases (by simp) (fun c => by simpa using hempty c) c
  · intro u v a b hu hab hempty h₁ hz
    apply no12_with_empty_deficient (topLeft B) he u.succ v.succ a.succ b.succ (hmono hu) (hmono hab)
    · intro c
      refine Fin.cases (by simp) (fun c => by simpa using hempty c) c
    · simpa using h₁
    · simpa only [topLeft_colSum] using hz

end D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
noncomputable section

abbrev TopLeftFibre (r k d : ℕ) := {R : Counted (r+1) (k+1) (d+1) // R.val 0 0=1}

private def extractTopLeft {r k d : ℕ} (R : TopLeftFibre r k d) : Counted r k d := by
  let B := cutTopLeft R.val.val
  have hi : topLeft B=R.val.val := topLeft_reconstruct R.val.val R.val.property.1 R.property
  have hR : IsASR (topLeft B) := by rw [hi]; exact R.val.property.1
  have hB := topLeft_isASR_inv B hR
  have he : ExtAvoids312 (topLeft B) := by rw [hi]; exact R.val.property.2.1
  have hd : nonemptyRows B=d := by
    have hc := topLeft_nonemptyRows B hB
    rw [hi,R.val.property.2.2] at hc
    omega
  exact ⟨B,hB,topLeft_extAvoids_inv B hB he,hd⟩

private def topLeftFibreEquiv (r k d : ℕ) : TopLeftFibre r k d ≃ Counted r k d where
  toFun := extractTopLeft
  invFun := fun B => ⟨⟨topLeft B.val,topLeft_isASR B.val B.property.1,
    topLeft_extAvoids B.val B.property.1 B.property.2.1,by
      rw [topLeft_nonemptyRows B.val B.property.1,B.property.2.2]⟩,by simp⟩
  left_inv := by
    intro R
    apply Subtype.ext
    apply Subtype.ext
    exact topLeft_reconstruct R.val.val R.val.property.1 R.property
  right_inv := by
    intro B
    apply Subtype.ext
    ext u c
    exact topLeft_succ_succ B.val u c

lemma topLeftFibre_card (r k d : ℕ) : Nat.card (TopLeftFibre r k d)=S r k d :=
  Nat.card_congr (topLeftFibreEquiv r k d)

end
end D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset
noncomputable section

private def asmZeroFibreEquiv (n : ℕ) : ASMFibre (n+1) (by omega) 0 ≃ TopLeftFibre n n n :=
  ((show Counted (n+1) (n+1) (n+1) ≃ AvoidASM (n+1) from
    Equiv.subtypeEquivRight fun M =>
      ⟨fun h => ⟨square_count_isASM M h.1 h.2.2, extAvoids312_corner M h.2.1⟩,
        fun h => ⟨h.1.1, ⟨n+1, le_refl _, le_refl _, M, h.1, h.2, by intro u c; rfl⟩,
          asm_nonemptyRows M h.1⟩⟩).symm).subtypeEquiv (fun M => Iff.rfl)

private lemma asmZeroFibre_card (n : ℕ) : Nat.card (ASMFibre (n+1) (by omega) 0)=Nat.card (AvoidASM n) := by
  rw [Nat.card_congr (asmZeroFibreEquiv n),topLeftFibre_card,squareCount_card]

private def asmPivot {n : ℕ} (hn : 0 < n) (M : AvoidASM n) : Fin n := Classical.choose (asm_first_column_one hn M)

private lemma asmPivot_spec {n : ℕ} (hn : 0 < n) (M : AvoidASM n) : M.val (asmPivot hn M) ⟨0,hn⟩=1 :=
  Classical.choose_spec (asm_first_column_one hn M)

private lemma asmPivot_fibre_iff {n : ℕ} (hn : 0 < n) (M : AvoidASM n) (p : Fin n) :
    asmPivot hn M=p ↔ M.val p ⟨0,hn⟩=1 := by
  constructor
  · intro hp
    simpa only [hp] using asmPivot_spec hn M
  · intro hp
    exact asr_first_col_one_unique M.val M.property.1.1 hn (asmPivot hn M) p (asmPivot_spec hn M) hp

private def asmPivotEquiv {n : ℕ} (hn : 0 < n) : AvoidASM n ≃ Σ p : Fin n, ASMFibre n hn p :=
  (Equiv.sigmaFiberEquiv (asmPivot hn)).symm.trans
    (Equiv.sigmaCongrRight fun p => Equiv.subtypeEquivProp
      (funext fun M => propext (asmPivot_fibre_iff hn M p)))

private lemma asm_succ_card (n : ℕ) : Nat.card (AvoidASM (n+1)) = Nat.card (AvoidASM n) +
    ∑ p : Fin n, Nat.card (AvoidASM (p.val+1))*Nat.card (AvoidASM (n-p.val)) := by
  classical
  letI : Fintype (AvoidASM (n+1)) := Fintype.ofFinite _
  letI : ∀ p : Fin (n+1), Fintype (ASMFibre (n+1) (by omega) p) := fun p => Fintype.ofFinite _
  rw [Nat.card_congr (asmPivotEquiv (show 0 < n+1 by omega)),Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp_rw [←Nat.card_eq_fintype_card]
  rw [Fin.sum_univ_succ,asmZeroFibre_card]
  congr 1
  apply sum_congr rfl
  intro p _
  simpa only [Fin.val_succ,Nat.add_sub_add_right] using
    asmNonzeroFibre_card (show 0 < n+1 by omega) p.succ (by simp)

lemma avoidingASM_card_schroder : ∀ n, Nat.card (AvoidASM (n+1))=Nat.largeSchroder n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [asm_succ_card]
      simpa only [Fin.sum_univ_zero,add_zero,Nat.largeSchroder_zero] using AvoidASM_zero_card
    | succ n =>
      rw [asm_succ_card,Nat.largeSchroder]
      rw [ih n (by omega)]
      congr 1
      apply sum_congr rfl
      intro p _
      rw [ih p.val (by have := p.isLt; omega)]
      have hp : n+1-p.val=(n-p.val)+1 := by have := p.isLt; omega
      rw [hp,ih (n-p.val) (by omega)]

private lemma S_diagonal_nat (d : ℕ) (hd : 0 < d) : S d d d=Nat.largeSchroder (d-1) := by
  rw [squareCount_card]
  have heq : (d-1)+1=d := by omega
  simpa only [heq] using avoidingASM_card_schroder (d-1)

lemma S_diagonal (d : ℕ) (hd : 0 < d) : (S d d d : ℤ)=(Nat.largeSchroder (d-1) : ℤ) := by
  exact_mod_cast S_diagonal_nat d hd

end
end D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition
