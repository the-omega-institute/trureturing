/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: EmptyRowFilling for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
castRows_isASR: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_isASR
castRows_extAvoids312: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_extAvoids312
castRows_nonemptyRows: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_nonemptyRows
filledRectAt_top: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_before, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_reconstruct, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_topRows
filledRectAt_topRows: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.firstEmptyFibreEquiv
filledRectAt_empty: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.fillFibre, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_reconstruct
filledRectAt_tail: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_reconstruct, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_tailChoice
filledRectAt_isASR: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
filledRectAt_extAvoids312: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
filledRectAt_nonemptyRows: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
filledRectAt_tailChoice: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.firstEmptyFibreEquiv
filledRectAt_before: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.fillFibre
choiceDeficient_entries: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
choiceDeficient_strictAnti: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
fillTail_reconstruct: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.fillTail_reconstruct
filledRectAt_reconstruct: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_reconstruct
counted_deficient_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
Choices_card: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.firstEmptyFibre_card
firstEmptyFibre_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_reconstruct
first_empty_unique: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.firstEmptyIndex_fibre_iff
firstEmptyIndex_fibre_iff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.firstEmptyEquiv
S_col_nat: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_reconstruct
S_col: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_reconstruct
Direct frozen dependencies: none; the ASR prerequisites are same-delivery content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

private def castRows {r r' k : ℕ} (h : r = r') (R : Matrix (Fin r) (Fin k) SignType) :
    Matrix (Fin r') (Fin k) SignType := Matrix.reindex (finCongr h) (Equiv.refl (Fin k)) R

private lemma castRows_isASR {r r' k : ℕ} (h : r = r') (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) : IsASR (castRows h R) := by
  subst r'
  have hc : castRows (rfl : r = r) R = R := by rfl
  rw [hc]
  exact hR

private lemma castRows_extAvoids312 {r r' k : ℕ} (h : r = r') (R : Matrix (Fin r) (Fin k) SignType)
    (he : ExtAvoids312 R) : ExtAvoids312 (castRows h R) := by
  subst r'
  have hc : castRows (rfl : r = r) R = R := by rfl
  rw [hc]
  exact he

private lemma castRows_nonemptyRows {r r' k : ℕ} (h : r = r') (R : Matrix (Fin r) (Fin k) SignType) :
    nonemptyRows (castRows h R) = nonemptyRows R := by
  subst r'
  have hc : castRows (rfl : r = r) R = R := by rfl
  rw [hc]

private def filledRectAt {r p k : ℕ} (T : Matrix (Fin p) (Fin k) SignType)
    (A : Finset (Fin (r-p-1))) (hA : A.card = (deficientColumns T).card) (hp : p < r) :
    Matrix (Fin r) (Fin k) SignType :=
  castRows (by omega : p+(1+(r-p-1))=r) (filledRect T A hA)

private lemma filledRectAt_top {r p k : ℕ} (T : Matrix (Fin p) (Fin k) SignType)
    (A : Finset (Fin (r-p-1))) (hA : A.card = (deficientColumns T).card) (hp : p < r)
    (i : Fin p) (c : Fin k) : filledRectAt T A hA hp (Fin.castLE (Nat.le_of_lt hp) i) c = T i c := by
  have hir : Fin.cast (show p+(1+(r-p-1))=r by omega).symm (Fin.castLE (Nat.le_of_lt hp) i) =
      i.castAdd (1+(r-p-1)) := by apply Fin.ext; rfl
  change filledRect T A hA (Fin.cast (show p+(1+(r-p-1))=r by omega).symm (Fin.castLE (Nat.le_of_lt hp) i)) c = T i c
  rw [hir]
  exact filledRect_top T A hA i c

private lemma filledRectAt_topRows {r p k : ℕ} (T : Matrix (Fin p) (Fin k) SignType)
    (A : Finset (Fin (r-p-1))) (hA : A.card = (deficientColumns T).card) (hp : p < r) :
    topRows (filledRectAt T A hA hp) (Nat.le_of_lt hp) = T := by
  ext i c
  exact filledRectAt_top T A hA hp i c

private lemma filledRectAt_empty {r p k : ℕ} (T : Matrix (Fin p) (Fin k) SignType)
    (A : Finset (Fin (r-p-1))) (hA : A.card = (deficientColumns T).card) (hp : p < r)
    (c : Fin k) : filledRectAt T A hA hp ⟨p,hp⟩ c = 0 := by
  have hir : Fin.cast (show p+(1+(r-p-1))=r by omega).symm (⟨p,hp⟩ : Fin r) =
      Fin.natAdd p (0 : Fin (1+(r-p-1))) := by apply Fin.ext; simp
  change filledRect T A hA (Fin.cast (show p+(1+(r-p-1))=r by omega).symm (⟨p,hp⟩ : Fin r)) c = 0
  rw [hir]
  exact filledRect_empty T A hA c

private lemma filledRectAt_tail {r p k : ℕ} (T : Matrix (Fin p) (Fin k) SignType)
    (A : Finset (Fin (r-p-1))) (hA : A.card = (deficientColumns T).card) (hp : p < r)
    (a : Fin (r-p-1)) (c : Fin k) :
    filledRectAt T A hA hp (tailIndex hp a) c = fillTail T A hA a c := by
  have hir : Fin.cast (show p+(1+(r-p-1))=r by omega).symm (tailIndex hp a) =
      Fin.natAdd p (Fin.natAdd 1 a) := by apply Fin.ext; simp [tailIndex]; omega
  change filledRect T A hA (Fin.cast (show p+(1+(r-p-1))=r by omega).symm (tailIndex hp a)) c = fillTail T A hA a c
  rw [hir]
  exact filledRect_tail T A hA a c

private lemma filledRectAt_isASR {r p k : ℕ} (T : Matrix (Fin p) (Fin k) SignType) (hT : IsASR T)
    (A : Finset (Fin (r-p-1))) (hA : A.card = (deficientColumns T).card) (hp : p < r) :
    IsASR (filledRectAt T A hA hp) :=
  castRows_isASR _ _ (filledRect_isASR T hT A hA)

private lemma filledRectAt_extAvoids312 {r p k : ℕ} (T : Matrix (Fin p) (Fin k) SignType)
    (hT : IsASR T) (he : ExtAvoids312 T) (hTrows : nonemptyRows T = p)
    (A : Finset (Fin (r-p-1))) (hA : A.card = (deficientColumns T).card) (hp : p < r) :
    ExtAvoids312 (filledRectAt T A hA hp) :=
  castRows_extAvoids312 _ _ (filledRect_extAvoids312 T hT he hTrows A hA)

private lemma filledRectAt_nonemptyRows {r p k : ℕ} (T : Matrix (Fin p) (Fin k) SignType) (hT : IsASR T)
    (A : Finset (Fin (r-p-1))) (hA : A.card = (deficientColumns T).card) (hp : p < r) :
    nonemptyRows (filledRectAt T A hA hp) = k := by
  rw [filledRectAt,castRows_nonemptyRows,filledRect_nonemptyRows T hT A hA]

private lemma filledRectAt_tailChoice {r p k : ℕ} (T : Matrix (Fin p) (Fin k) SignType)
    (A : Finset (Fin (r-p-1))) (hA : A.card = (deficientColumns T).card) (hp : p < r) :
    tailChoice (filledRectAt T A hA hp) hp = A := by
  classical
  ext a
  rw [mem_tailChoice]
  simp only [filledRectAt_tail]
  constructor
  · rintro ⟨c,hc⟩
    by_contra ha
    rw [fillTail_unselected_row T A hA a ha] at hc
    exact hc rfl
  · intro ha
    obtain ⟨x,hxa⟩ := selectedRowAt_surjective T A hA a ha
    refine ⟨deficientColumnAt T x,?_⟩
    rw [← hxa,fillTail_selected_row]
    simp

private lemma filledRectAt_before {r p k : ℕ} (T : Matrix (Fin p) (Fin k) SignType)
    (hTrows : nonemptyRows T = p)
    (A : Finset (Fin (r-p-1))) (hA : A.card = (deficientColumns T).card) (hp : p < r)
    (i : Fin r) (hi : i.val < p) : ∃ c, filledRectAt T A hA hp i c ≠ 0 := by
  obtain ⟨c,hc⟩ := rowComplete_nonempty T hTrows ⟨i.val,hi⟩
  have hir : Fin.castLE (Nat.le_of_lt hp) (⟨i.val,hi⟩ : Fin p) = i := by apply Fin.ext; rfl
  refine ⟨c,?_⟩
  rw [← hir,filledRectAt_top]
  exact hc

end
end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

private def choiceDeficientEquiv {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ c, R i₀ c = 0) :
    tailChoice R i₀.isLt ≃ deficientColumns (topRows R (Nat.le_of_lt i₀.isLt)) :=
  (tailChoiceEquiv R i₀).symm.trans (balancedTailEquiv R hR he hd i₀ hempty)

private lemma choiceDeficient_entries {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ c, R i₀ c = 0) (a : tailChoice R i₀.isLt) (c : Fin k) :
    R (tailIndex i₀.isLt a.val) c =
      if (choiceDeficientEquiv R hR he hd i₀ hempty a).val = c then 1 else 0 :=
  tailColumn_entries R hR he hd i₀ hempty ((tailChoiceEquiv R i₀).symm a) c

private lemma choiceDeficient_strictAnti {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ c, R i₀ c = 0) :
    StrictAnti (fun a => (choiceDeficientEquiv R hR he hd i₀ hempty a).val) := by
  intro a b hab
  apply balancedTailEquiv_strictAnti R hR he hd i₀ hempty
  change i₀.val+1+a.val.val < i₀.val+1+b.val.val
  change a.val.val < b.val.val at hab
  omega

private lemma fillTail_reconstruct {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ c, R i₀ c = 0)
    (hA : (tailChoice R i₀.isLt).card = (deficientColumns (topRows R (Nat.le_of_lt i₀.isLt))).card)
    (a : Fin (r-i₀.val-1)) (c : Fin k) :
    fillTail (topRows R (Nat.le_of_lt i₀.isLt)) (tailChoice R i₀.isLt) hA a c =
      R (tailIndex i₀.isLt a) c := by
  classical
  let T := topRows R (Nat.le_of_lt i₀.isLt)
  let A := tailChoice R i₀.isLt
  by_cases ha : a ∈ A
  · obtain ⟨x,hxa⟩ := selectedRowAt_surjective T A hA a ha
    rw [← hxa,fillTail_selected_row]
    have hs := strictAnti_equiv_sorted A (deficientColumns T)
      (choiceDeficientEquiv R hR he hd i₀ hempty)
      (choiceDeficient_strictAnti R hR he hd i₀ hempty) hA rfl x
    have hv := congrArg Subtype.val hs
    change (choiceDeficientEquiv R hR he hd i₀ hempty (A.orderIsoOfFin hA x)).val =
      deficientColumnAt T x at hv
    rw [← hv]
    exact (choiceDeficient_entries R hR he hd i₀ hempty (A.orderIsoOfFin hA x) c).symm
  · rw [fillTail_unselected_row T A hA a ha]
    have hz : R (tailIndex i₀.isLt a) c = 0 := by
      by_contra h
      exact ha ((mem_tailChoice R i₀.isLt a).mpr ⟨c,h⟩)
    exact hz.symm

private lemma filledRectAt_reconstruct {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ c, R i₀ c = 0)
    (hA : (tailChoice R i₀.isLt).card = (deficientColumns (topRows R (Nat.le_of_lt i₀.isLt))).card) :
    filledRectAt (topRows R (Nat.le_of_lt i₀.isLt)) (tailChoice R i₀.isLt) hA i₀.isLt = R := by
  ext i c
  by_cases hi : i.val < i₀.val
  · have hir : Fin.castLE (Nat.le_of_lt i₀.isLt) (⟨i.val,hi⟩ : Fin i₀.val) = i := by apply Fin.ext; rfl
    have h := filledRectAt_top (topRows R (Nat.le_of_lt i₀.isLt)) (tailChoice R i₀.isLt) hA i₀.isLt ⟨i.val,hi⟩ c
    simpa only [topRows,hir] using h
  · by_cases hei : i = i₀
    · subst i
      rw [filledRectAt_empty,hempty]
    · have hib : i₀.val < i.val := by
        have hn : i.val ≠ i₀.val := fun h => hei (Fin.ext h)
        omega
      have hb : i.val-i₀.val-1 < r-i₀.val-1 := by have := i.isLt; omega
      let a : Fin (r-i₀.val-1) := ⟨i.val-i₀.val-1,hb⟩
      have hir : tailIndex i₀.isLt a = i := by apply Fin.ext; dsimp [a,tailIndex]; omega
      rw [← hir,filledRectAt_tail]
      exact fillTail_reconstruct R hR he hd i₀ hempty hA a c

end
end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

private abbrev Choices (n q : ℕ) := {A : Finset (Fin n) // A.card = q}

abbrev FirstEmptyFibre (r k : ℕ) (j : Fin (k+1)) (hkr : k < r) :=
  {R : Counted r k k //
    (∀ c, R.val ⟨j.val,by have := j.isLt; omega⟩ c = 0) ∧
      ∀ i : Fin r, i.val < j.val → ∃ c, R.val i c ≠ 0}

private lemma counted_deficient_card (p k : ℕ) (T : Counted p k p) :
    (deficientColumns T.val).card = k-p := by
  have hb := deficientColumns_balance T.val T.property.1
  have hd := T.property.2.2
  omega

private def extractFibre {r k : ℕ} (j : Fin (k+1)) (hkr : k < r) (R : FirstEmptyFibre r k j hkr) :
    Counted j.val k j.val × Choices (r-j.val-1) (k-j.val) := by
  have hp : j.val < r := by have := j.isLt; omega
  let T : Counted j.val k j.val :=
    ⟨topRows R.val.val (Nat.le_of_lt hp),
      topRows_isASR R.val.val (Nat.le_of_lt hp) R.val.property.1,
      topRows_extAvoids312 R.val.val (Nat.le_of_lt hp) R.val.property.2.1,
      topRows_nonemptyRows_of_before R.val.val (Nat.le_of_lt hp) R.property.2⟩
  refine ⟨T,⟨tailChoice R.val.val hp,?_⟩⟩
  exact first_empty_choice_card R.val.val R.val.property.1 R.val.property.2.1 R.val.property.2.2
    ⟨j.val,hp⟩ R.property.1 R.property.2

private def fillFibre {r k : ℕ} (j : Fin (k+1)) (hkr : k < r)
    (x : Counted j.val k j.val × Choices (r-j.val-1) (k-j.val)) : FirstEmptyFibre r k j hkr := by
  have hp : j.val < r := by have := j.isLt; omega
  have hA : x.2.val.card = (deficientColumns x.1.val).card :=
    x.2.property.trans (counted_deficient_card j.val k x.1).symm
  let R := filledRectAt x.1.val x.2.val hA hp
  refine ⟨⟨R,filledRectAt_isASR x.1.val x.1.property.1 x.2.val hA hp,
      filledRectAt_extAvoids312 x.1.val x.1.property.1 x.1.property.2.1 x.1.property.2.2 x.2.val hA hp,
      filledRectAt_nonemptyRows x.1.val x.1.property.1 x.2.val hA hp⟩,?_,?_⟩
  · exact filledRectAt_empty x.1.val x.2.val hA hp
  · exact filledRectAt_before x.1.val x.1.property.2.2 x.2.val hA hp

private def firstEmptyFibreEquiv {r k : ℕ} (j : Fin (k+1)) (hkr : k < r) :
    FirstEmptyFibre r k j hkr ≃ Counted j.val k j.val × Choices (r-j.val-1) (k-j.val) where
  toFun := extractFibre j hkr
  invFun := fillFibre j hkr
  left_inv R := by
    apply Subtype.ext
    apply Subtype.ext
    exact filledRectAt_reconstruct R.val.val R.val.property.1 R.val.property.2.1 R.val.property.2.2
      ⟨j.val,by have := j.isLt; omega⟩ R.property.1 _
  right_inv x := by
    have hp : j.val < r := by have := j.isLt; omega
    have hA : x.2.val.card = (deficientColumns x.1.val).card :=
      x.2.property.trans (counted_deficient_card j.val k x.1).symm
    apply Prod.ext
    · apply Subtype.ext
      change topRows (filledRectAt x.1.val x.2.val hA hp) (Nat.le_of_lt hp) = x.1.val
      exact filledRectAt_topRows x.1.val x.2.val hA hp
    · apply Subtype.ext
      change tailChoice (filledRectAt x.1.val x.2.val hA hp) hp = x.2.val
      exact filledRectAt_tailChoice x.1.val x.2.val hA hp

private lemma Choices_card (n q : ℕ) : Nat.card (Choices n q) = Nat.choose n q := by
  classical
  let e : Choices n q ≃ (univ : Finset (Fin n)).powersetCard q :=
    { toFun := fun A => ⟨A.val,mem_powersetCard.mpr ⟨subset_univ _,A.property⟩⟩
      invFun := fun A => ⟨A.val,(mem_powersetCard.mp A.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,card_powersetCard,card_univ,Fintype.card_fin]

lemma firstEmptyFibre_card {r k : ℕ} (j : Fin (k+1)) (hkr : k < r) :
    Nat.card (FirstEmptyFibre r k j hkr) = S j.val k j.val * Nat.choose (r-j.val-1) (k-j.val) := by
  rw [Nat.card_congr (firstEmptyFibreEquiv j hkr),Nat.card_prod,Choices_card]
  rfl

end
end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

private lemma first_empty_unique {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (a b : Fin r) (ha : ∀ c, R a c = 0) (hb : ∀ c, R b c = 0)
    (hbeforea : ∀ i : Fin r, i < a → ∃ c, R i c ≠ 0)
    (hbeforeb : ∀ i : Fin r, i < b → ∃ c, R i c ≠ 0) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · obtain ⟨c,hc⟩ := hbeforeb a h
    exact (hc (ha c)).elim
  · exact h
  · obtain ⟨c,hc⟩ := hbeforea b h
    exact (hc (hb c)).elim

private def firstEmptyPart {r k : ℕ} (hkr : k < r) (R : Counted r k k) :
    Σ j : Fin (k+1), FirstEmptyFibre r k j hkr := by
  let hex := first_empty_row_exists R.val R.property.2.2 hkr
  let j := Classical.choose hex
  have hp : j.val < r := by have := j.isLt; omega
  have hfirst := Classical.choose_spec hex
  refine ⟨j,⟨R,?_⟩⟩
  obtain ⟨hj,hempty,hbefore⟩ := hfirst
  exact ⟨hempty,hbefore⟩

private lemma firstEmptyIndex_fibre_iff {r k : ℕ} (hkr : k < r) (R : Counted r k k) (j : Fin (k+1)) :
    (firstEmptyPart hkr R).1 = j ↔
      ((∀ c, R.val ⟨j.val,by have := j.isLt; omega⟩ c = 0) ∧
        ∀ i : Fin r, i.val < j.val → ∃ c, R.val i c ≠ 0) := by
  constructor
  · intro h
    rw [← h]
    exact (firstEmptyPart hkr R).2.property
  · intro hp
    apply Fin.ext
    have h := first_empty_unique R.val
      ⟨(firstEmptyPart hkr R).1.val,by have := (firstEmptyPart hkr R).1.isLt; omega⟩
      ⟨j.val,by have := j.isLt; omega⟩
      (firstEmptyPart hkr R).2.property.1 hp.1
      (firstEmptyPart hkr R).2.property.2 hp.2
    exact congrArg (fun i : Fin r => i.val) h

private def firstEmptyEquiv {r k : ℕ} (hkr : k < r) :
    Counted r k k ≃ Σ j : Fin (k+1), FirstEmptyFibre r k j hkr :=
  (Equiv.sigmaFiberEquiv (fun R : Counted r k k => (firstEmptyPart hkr R).1)).symm.trans
    (Equiv.sigmaCongrRight fun j => Equiv.subtypeEquivProp
      (funext fun R => propext (firstEmptyIndex_fibre_iff hkr R j)))

private lemma S_col_nat (r k : ℕ) (hkr : k < r) :
    S r k k = ∑ j : Fin (k+1), S j.val k j.val * Nat.choose (r-j.val-1) (k-j.val) := by
  classical
  letI : Fintype (Counted r k k) := Fintype.ofFinite _
  letI : ∀ j : Fin (k+1), Fintype (FirstEmptyFibre r k j hkr) := fun j => Fintype.ofFinite _
  rw [show S r k k = Nat.card (Counted r k k) from rfl,
    Nat.card_congr (firstEmptyEquiv hkr),Nat.card_eq_fintype_card,Fintype.card_sigma]
  apply sum_congr rfl
  intro j _
  rw [← Nat.card_eq_fintype_card,firstEmptyFibre_card]

lemma S_col (r k : ℕ) (_hk : 0 < k) (hkr : k < r) :
    (S r k k : ℤ) = ∑ j : Fin (k+1),
      (S j.val k j.val : ℤ) * (Nat.choose (r-j.val-1) (k-j.val) : ℤ) := by
  exact_mod_cast S_col_nat r k hkr

end
end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling
