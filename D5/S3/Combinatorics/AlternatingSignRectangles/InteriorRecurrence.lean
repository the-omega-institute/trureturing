/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/InteriorRecurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/InteriorRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: InteriorRecurrence for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
firstEmpty_first_col_zero: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
firstEmptyCounted_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.firstEmptyCounted_card
firstRowPartition_card: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.firstNonempty_card_int
firstNonempty_card_int: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.firstEmptyCounted_card
S_interior_shift: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.firstEmptyCounted_card
S_interior: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.firstEmptyCounted_card
Direct frozen dependencies: none; the ASR prerequisites are same-delivery content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling
import D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence

namespace D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset
noncomputable section

private abbrev FirstEmptyCounted (r k d : ℕ) (hr : 0 < r) :=
  {R : Counted r k d // ∀ c, R.val ⟨0,hr⟩ c=0}

private lemma firstEmpty_first_col_zero {r k d : ℕ} (hr : 0 < r) (hk : 0 < k) (hd : d < k)
    (R : FirstEmptyCounted r k d hr) : ∀ u, R.val.val u ⟨0,hk⟩=0 := by
  intro u
  have hm := asr_first_col_not_minus R.val.val R.val.property.1 hk u
  have hn : R.val.val u ⟨0,hk⟩ ≠ 1 := by
    intro hone
    by_cases hu : u.val=0
    · have heq : u=⟨0,hr⟩ := Fin.ext hu
      rw [heq,R.property] at hone
      exact (by decide : (0 : SignType) ≠ 1) hone
    · have hb := pivot_before_nonempty_of_deficit R.val.val R.val.property.1 R.val.property.2.1 hk u hone
        (by rw [R.val.property.2.2]; exact hd)
      obtain ⟨c,hc⟩ := hb ⟨0,hr⟩ (by change 0 < u.val; omega)
      exact hc (R.property c)
  cases hs : R.val.val u ⟨0,hk⟩ <;> simp_all

private def firstEmptyZeroColumnEquiv (r k d : ℕ) (hr : 0 < r) (hd : d < k+1) :
    FirstEmptyCounted r (k+1) d hr ≃ FirstEmptyCounted r k d hr where
  toFun := fun R => ⟨extractZeroColumn ⟨R.val,firstEmpty_first_col_zero hr (by omega) hd R⟩,by
    intro c
    exact R.property c.succ⟩
  invFun := fun B => ⟨(zeroColumnFibreEquiv r k d).symm B.val,by
    intro c
    change zeroColumn B.val.val ⟨0,hr⟩ c=0
    refine Fin.cases (by simp) (fun c => by simpa using B.property c) c⟩
  left_inv := by
    intro R
    apply Subtype.ext
    apply Subtype.ext
    exact zeroColumn_reconstruct R.val.val (firstEmpty_first_col_zero hr (by omega) hd R)
  right_inv := by
    intro B
    apply Subtype.ext
    apply Subtype.ext
    ext u c
    exact zeroColumn_succ B.val.val u c

private lemma firstEmptyCounted_card (r k d : ℕ) (hr : 0 < r) (hdr : d < r) (hdk : d ≤ k) :
    Nat.card (FirstEmptyCounted r k d hr)=Nat.choose (r-1) d := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hkd : k=d
    · subst k
      let e : FirstEmptyCounted r d d hr ≃ FirstEmptyFibre r d 0 hdr :=
        Equiv.subtypeEquivRight (fun B =>
          ⟨fun h => ⟨h, by intro u hu; exact (Nat.not_lt_zero u.val hu).elim⟩, fun h => h.1⟩)
      rw [Nat.card_congr e,firstEmptyFibre_card]
      simp only [Fin.val_zero,Nat.sub_zero,Nat.zero_sub]
      rw [S_zero,one_mul]
    · have hlt : d < k := by omega
      have hk : 0 < k := by omega
      have hsucc : k-1+1=k := by omega
      have heq := Nat.card_congr (firstEmptyZeroColumnEquiv r (k-1) d hr (by omega))
      have hcard : Nat.card (FirstEmptyCounted r k d hr)=Nat.card (FirstEmptyCounted r (k-1) d hr) := by
        simpa only [hsucc] using heq
      rw [hcard]
      exact ih (k-1) (by omega) (by omega)

end
end D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence

namespace D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset
noncomputable section

private def firstRowPartitionEquiv (r k d : ℕ) (hr : 0 < r) :
    Counted r k d ≃ FirstNonempty r k d hr ⊕ FirstEmptyCounted r k d hr :=
  (Equiv.sumCompl (fun R : Counted r k d => ∃ c, R.val ⟨0,hr⟩ c ≠ 0)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivProp (funext fun R => propext (by simp))))

private lemma firstRowPartition_card (r k d : ℕ) (hr : 0 < r) :
    Nat.card (FirstNonempty r k d hr)+Nat.card (FirstEmptyCounted r k d hr)=S r k d := by
  rw [show S r k d=Nat.card (Counted r k d) from rfl,
    Nat.card_congr (firstRowPartitionEquiv r k d hr),Nat.card_sum]

private lemma firstNonempty_card_int (r k d : ℕ) (hr : 0 < r) (hdr : d < r) (hdk : d ≤ k) :
    (Nat.card (FirstNonempty r k d hr) : ℤ)=(S r k d : ℤ)-(Nat.choose (r-1) d : ℤ) := by
  have hnat := firstRowPartition_card r k d hr
  rw [firstEmptyCounted_card r k d hr hdr hdk] at hnat
  have hint : (Nat.card (FirstNonempty r k d hr) : ℤ)+(Nat.choose (r-1) d : ℤ)=(S r k d : ℤ) := by
    exact_mod_cast hnat
  omega

private lemma S_interior_shift (r k d : ℕ) (hdr : d < r) (hdk : d < k) :
    (S (r+1) (k+1) (d+1) : ℤ)=(S (r+1) k (d+1) : ℤ)+(S r k d : ℤ)+
      ∑ p : Fin d, (Nat.largeSchroder p.val : ℤ)*
        ((S (r-p.val) (k-p.val) (d-p.val) : ℤ)-
          (Nat.choose (r-p.val-1) (d-p.val) : ℤ)) := by
  have hnat := rectangle_merge_nat r k d (le_of_lt hdr) (le_of_lt hdk) (Or.inl hdk)
  have hint : (S (r+1) (k+1) (d+1) : ℤ)=(S (r+1) k (d+1) : ℤ)+(S r k d : ℤ)+
      ∑ p : Fin d, (Nat.card (AvoidASM (p.val+1)) : ℤ)*
        (Nat.card (FirstNonempty (r-p.val) (k-p.val) (d-p.val) (by have := p.isLt; omega)) : ℤ) := by
    exact_mod_cast hnat
  rw [hint]
  congr 1
  apply sum_congr rfl
  intro p _
  rw [avoidingASM_card_schroder,firstNonempty_card_int _ _ _ _ (by have := p.isLt; omega) (by omega)]

lemma S_interior (r k d : ℕ) (hd : 0 < d) (hdr : d < r) (hdk : d < k) :
    (S r k d : ℤ)=(S r (k-1) d : ℤ)+(S (r-1) (k-1) (d-1) : ℤ)+
      ∑ i : ↥(Icc 2 d), (Nat.largeSchroder (i.val-2) : ℤ)*
        ((S (r+1-i.val) (k+1-i.val) (d+1-i.val) : ℤ)-
          (Nat.choose (r-i.val) (d+1-i.val) : ℤ)) := by
  have hint := S_interior_shift (r-1) (k-1) (d-1) (by omega) (by omega)
  have hr' : (r-1)+1=r := by omega
  have hk' : (k-1)+1=k := by omega
  have hd' : (d-1)+1=d := by omega
  rw [hr',hk',hd'] at hint
  rw [hint,sum_Icc_two d hd (fun i => (Nat.largeSchroder (i-2) : ℤ)*
    ((S (r+1-i) (k+1-i) (d+1-i) : ℤ)-(Nat.choose (r-i) (d+1-i) : ℤ)))]
  congr 1
  apply sum_congr rfl
  intro p _
  have hi : (p.val+2)-2=p.val := by omega
  have hrp : r+1-(p.val+2)=r-1-p.val := by have := p.isLt; omega
  have hkp : k+1-(p.val+2)=k-1-p.val := by have := p.isLt; omega
  have hdp : d+1-(p.val+2)=d-1-p.val := by have := p.isLt; omega
  have hbin : r-(p.val+2)=r-1-p.val-1 := by have := p.isLt; omega
  rw [hi,hrp,hkp,hdp,hbin]

end
end D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence
