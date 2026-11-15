/- GID: D5/S3/SpinModels/KingDefects/KingHorizontal
   generality: G
   mirror-B: D5/B/S3/SpinModels/KingDefects/KingHorizontal
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Horizontal one-defect fields and their compressed slot assignments. -/
/-
admission_basis: escape-witness
escape_witness: boundary_slot_equiv (exact horizontal boundary-slot classification).
BoundaryData: proof_shape=bind-only; consumers=BoundaryValid,boundary_build,boundary_extract
BoundaryValid: proof_shape=bind-only; consumers=boundary_build_raw,boundary_extract_valid
boundary_build: proof_shape=bind-only; consumers=boundary_build_raw,boundary_reconstruct
boundary_extract: proof_shape=bind-only; consumers=boundary_extract_valid,boundary_reconstruct
boundary_h: proof_shape=content; consumers=boundary_extract_valid,boundary_reconstruct
boundary_v: proof_shape=content; consumers=boundary_extract_valid,boundary_reconstruct
boundary_build_raw: proof_shape=content; consumers=boundary_slot_equiv
boundary_extract_valid: proof_shape=content; consumers=boundary_slot_equiv
boundary_reconstruct: proof_shape=content; consumers=boundary_slot_equiv
boundary_slot_equiv: proof_shape=content; consumers=KingClosedForm.horizontal_count
-/
import D5.S3.SpinModels.KingDefects.KingDifference

/-! Horizontal defects, with dimensions expressed as numbers of steps. -/
namespace D5.S3.SpinModels.KingDefects.KingHorizontal

open KingGrid KingDifference
open scoped IsAddKleinFour

/-- The special ordered pair, horizontal slots and ordinary vertical slots. -/
@[ext] structure BoundaryData (m M : ℕ) where
  p : K
  q : K
  h : Fin M → K
  v : Fin m → K
  deriving DecidableEq

/-- The two half-slots exclude their vertical values; every ordinary crossing is proper. -/
def BoundaryValid {m M : ℕ} (s : Fin M) (b : BoundaryData m M) : Prop :=
  b.p ≠ 0 ∧ b.q ≠ 0 ∧ b.p ≠ b.q ∧ b.h s = b.p + b.q ∧
    (∀ j, b.h j ≠ 0) ∧ (∀ i, b.v i ≠ 0) ∧
    (∀ j, j < s → b.h j ≠ b.p) ∧ (∀ j, s < j → b.h j ≠ b.q) ∧
    ∀ i j, b.h j ≠ b.v i

def boundary_build {m M : ℕ} (s : Fin M) (b : BoundaryData m M) :
    DiffField (m + 1) M where
  h i j := if i = 0 ∧ j = s then 0 else b.h j
  v i j := if hi : i = 0 then (if j.val ≤ s.val then b.p else b.q)
    else b.v (i.pred hi)

def boundary_extract {m M : ℕ} (s : Fin M) (t : DiffField (m + 1) M) :
    BoundaryData m M where
  p := t.v 0 s.castSucc
  q := t.v 0 s.succ
  h := t.h 1
  v i := t.v i.succ 0

/-- All horizontal slots other than the defect extend through the full rectangle. -/
theorem boundary_h {m M : ℕ} (s : Fin M) (t : DiffField (m + 1) M)
    (ht : RawAdmissible (.H 0 s) t) (i : Fin (m + 1 + 1)) (j : Fin M) :
    t.h i j = if i = 0 ∧ j = s then 0 else t.h 1 j := by
  have clear (a : Fin (m + 1)) (ha : a.val ≠ 0 ∨ j ≠ s) :
      BlockAvoids (.H 0 s) a j := by
    refine ⟨?_, by simp, by simp, by simp, by simp, ?_⟩
    · intro he
      have he := Edge.H.inj he
      rcases ha with ha | ha
      · exact ha (by simpa using congrArg Fin.val he.1)
      · exact ha he.2
    · intro he
      have he := Edge.H.inj he
      have := congrArg Fin.val he.1
      simp at this
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = s
    · subst j
      simpa [edgeValue] using (ht.2 (.H 0 s)).mpr rfl
    · simp only [hj, and_false, ↓reduceIte]
      exact horizontal_slot_eq (.H 0 s) t ht j 0 1 (Fin.zero_le _)
        (fun a _ _ => clear a (Or.inr hj))
  · simp only [hi, false_and, ↓reduceIte]
    exact (horizontal_slot_eq (.H 0 s) t ht j 1 i
      (by simpa only [Fin.le_iff_val_le_val, Fin.val_one] using
        Nat.one_le_iff_ne_zero.mpr (fun h => hi (Fin.ext h)))
      (fun a ha _ => clear a (Or.inl (by
        simp only [Fin.val_one] at ha
        omega)))).symm

/-- The first vertical slot splits at the defect; every later slot is constant. -/
theorem boundary_v {m M : ℕ} (s : Fin M) (t : DiffField (m + 1) M)
    (ht : RawAdmissible (.H 0 s) t) (i : Fin (m + 1)) (j : Fin (M + 1)) :
    t.v i j = if i = 0 then
      (if j.val ≤ s.val then t.v 0 s.castSucc else t.v 0 s.succ)
      else t.v i 0 := by
  have clear (a : Fin M) (ha : i ≠ 0 ∨ a ≠ s) : BlockAvoids (.H 0 s) i a := by
    refine ⟨?_, by simp, by simp, by simp, by simp, ?_⟩
    · intro he
      obtain ⟨h1,h2⟩ := Edge.H.inj he
      rcases ha with ha | ha
      · exact ha (by apply Fin.ext; simpa using congrArg Fin.val h1)
      · exact ha h2
    · intro he
      obtain ⟨h1,_⟩ := Edge.H.inj he
      have := congrArg Fin.val h1
      simp at this
  by_cases hi : i = 0
  · subst i
    by_cases hj : j.val ≤ s.val
    · simp only [hj, ↓reduceIte]
      exact vertical_slot_eq (.H 0 s) t ht 0 j s.castSucc hj
        (fun a _ ha => clear a (Or.inr (by
          intro he
          subst a
          simp at ha)))
    · simp only [hj, ↓reduceIte]
      exact (vertical_slot_eq (.H 0 s) t ht 0 s.succ j (by
        simp only [Fin.le_iff_val_le_val, Fin.val_succ]
        omega) (fun a ha _ => clear a (Or.inr (by
          intro he
          subst a
          simp at ha)))).symm
  · simp only [hi]
    exact (vertical_slot_eq (.H 0 s) t ht i 0 j (Fin.zero_le _)
      (fun a _ _ => clear a (Or.inl hi))).symm

/-- Every valid compressed boundary assignment gives exactly one horizontal defect. -/
theorem boundary_build_raw {m M : ℕ} (s : Fin M) (b : BoundaryData m M)
    (hb : BoundaryValid s b) : RawAdmissible (.H 0 s) (boundary_build s b) := by
  rcases hb with ⟨hp,hq,hpq,hs,hh,hv,hl,hr,hcross⟩
  have local_top (j : Fin M) :
      (boundary_build s b).h 0 j + (boundary_build s b).v 0 j.succ =
        (boundary_build s b).v 0 j.castSucc + (boundary_build s b).h 1 j := by
    by_cases hj : j = s
    · subst j
      simp [boundary_build, hs, IsAddKleinFour.add_self, ← add_assoc]
    · rcases lt_or_gt_of_ne hj with hj | hj
      · have h1 : j.val ≤ s.val := Nat.le_of_lt hj
        have h2 : j.val + 1 ≤ s.val := hj
        simp [boundary_build, ne_of_lt hj, h1, h2, add_comm]
      · have h1 : ¬j.val ≤ s.val := Nat.not_le_of_gt hj
        have h2 : ¬j.val + 1 ≤ s.val := by omega
        simp [boundary_build, ne_of_gt hj, h1, h2, add_comm]
  have hc : Cocycle (boundary_build s b) := by
    intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · exact local_top j
    · simp [boundary_build, Fin.succ_ne_zero, add_comm]
  refine ⟨hc, ?_⟩
  intro e
  cases e with
  | H i j =>
    simp [edgeValue, boundary_build, hh, Edge.H.injEq]
  | V i j =>
    suffices edgeValue (boundary_build s b) (.V i j) ≠ 0 by simpa using this
    dsimp only [edgeValue]
    refine Fin.cases ?_ (fun a => ?_) i
    · dsimp only [boundary_build]
      simp only [dite_true]
      split <;> assumption
    · simpa [boundary_build] using hv a
  | D i j =>
    suffices edgeValue (boundary_build s b) (.D i j) ≠ 0 by simpa using this
    dsimp only [edgeValue]
    refine Fin.cases ?_ (fun a => ?_) i
    · by_cases hj : j = s
      · subst j
        simpa [boundary_build] using hq
      · rcases lt_or_gt_of_ne hj with hj | hj
        · have h1 : j.val + 1 ≤ s.val := hj
          simpa [boundary_build, ne_of_lt hj, h1, add_eq_zero_iff_eq_neg] using hl j hj
        · have h1 : ¬j.val + 1 ≤ s.val := by omega
          simpa [boundary_build, ne_of_gt hj, h1, add_eq_zero_iff_eq_neg] using hr j hj
    · simpa [boundary_build, add_eq_zero_iff_eq_neg] using hcross a j
  | A i j =>
    suffices edgeValue (boundary_build s b) (.A i j) ≠ 0 by simpa using this
    dsimp only [edgeValue]
    refine Fin.cases ?_ (fun a => ?_) i
    · by_cases hj : j = s
      · subst j
        simpa [boundary_build] using hp
      · rcases lt_or_gt_of_ne hj with hj | hj
        · have h1 : j.val ≤ s.val := Nat.le_of_lt hj
          simpa [boundary_build, ne_of_lt hj, h1, add_eq_zero_iff_eq_neg] using hl j hj
        · have h1 : ¬j.val ≤ s.val := Nat.not_le_of_gt hj
          simpa [boundary_build, ne_of_gt hj, h1, add_eq_zero_iff_eq_neg] using hr j hj
    · simpa [boundary_build, add_eq_zero_iff_eq_neg] using hcross a j

/-- Admissibility supplies precisely the boundary-slot exclusions. -/
theorem boundary_extract_valid {m M : ℕ} (s : Fin M) (t : DiffField (m + 1) M)
    (ht : RawAdmissible (.H 0 s) t) : BoundaryValid s (boundary_extract s t) := by
  have nz (e : Edge (m + 1 + 1) (M + 1)) (he : e ≠ .H 0 s) :
      edgeValue t e ≠ 0 := mt (ht.2 e).mp he
  have hp : t.v 0 s.castSucc ≠ 0 := nz (.V (0 : Fin (m + 1)) s.castSucc) (by simp)
  have hq : t.v 0 s.succ ≠ 0 := nz (.V (0 : Fin (m + 1)) s.succ) (by simp)
  have hh (j : Fin M) : t.h 1 j ≠ 0 := nz (.H 1 j) (by simp)
  have hs : t.h 1 s = t.v 0 s.castSucc + t.v 0 s.succ := by
    have hc := ht.1 0 s
    have hz : t.h 0 s = 0 := (ht.2 (.H 0 s)).mpr rfl
    change t.h 0 s + t.v 0 s.succ = t.v 0 s.castSucc + t.h 1 s at hc
    rw [hz, zero_add] at hc
    simpa [← add_assoc, IsAddKleinFour.add_self] using
      congrArg (fun x => t.v 0 s.castSucc + x) hc.symm
  have hpq : t.v 0 s.castSucc ≠ t.v 0 s.succ := by
    intro he
    apply hh s
    rw [hs, he, IsAddKleinFour.add_self]
  refine ⟨hp,hq,hpq,hs,hh,?_,?_,?_,?_⟩
  · intro a
    exact nz (.V a.succ 0) (by simp)
  · intro j hj
    have hj' : j ≠ s := ne_of_lt hj
    have htop : t.h 0 j = t.h 1 j := by
      simpa [hj'] using boundary_h s t ht 0 j
    have hv : t.v 0 j.castSucc = t.v 0 s.castSucc := by
      simpa [Nat.le_of_lt hj] using boundary_v s t ht 0 j.castSucc
    have hn := nz (.A (0 : Fin (m + 1)) j) (by simp)
    simpa [boundary_extract, edgeValue, htop, hv, add_eq_zero_iff_eq_neg] using hn
  · intro j hj
    have hj' : j ≠ s := ne_of_gt hj
    have htop : t.h 0 j = t.h 1 j := by
      simpa [hj'] using boundary_h s t ht 0 j
    have hv : t.v 0 j.castSucc = t.v 0 s.succ := by
      simpa [Nat.not_le_of_gt hj] using boundary_v s t ht 0 j.castSucc
    have hn := nz (.A (0 : Fin (m + 1)) j) (by simp)
    simpa [boundary_extract, edgeValue, htop, hv, add_eq_zero_iff_eq_neg] using hn
  · intro a j
    have htop : t.h a.succ.castSucc j = t.h 1 j := by
      simpa using boundary_h s t ht a.succ.castSucc j
    have hv : t.v a.succ j.castSucc = t.v a.succ 0 := by
      simpa using boundary_v s t ht a.succ j.castSucc
    have hn := nz (.A a.succ j) (by simp)
    change t.h a.succ.castSucc j + t.v a.succ j.castSucc ≠ 0 at hn
    rw [htop, hv] at hn
    simpa [boundary_extract, add_eq_zero_iff_eq_neg] using hn

/-- Extracting the compressed slots loses no field values. -/
theorem boundary_reconstruct {m M : ℕ} (s : Fin M) (t : DiffField (m + 1) M)
    (ht : RawAdmissible (.H 0 s) t) : boundary_build s (boundary_extract s t) = t := by
  apply DiffField.ext
  · funext i j
    exact (boundary_h s t ht i j).symm
  · funext i j
    dsimp only [boundary_build, boundary_extract]
    rw [boundary_v s t ht i j]
    split
    · rfl
    · congr 1
      exact Fin.succ_pred _ _

/-- Top-boundary fields are in bijection with compressed slot assignments. -/
def boundary_slot_equiv (m M : ℕ) (s : Fin M) :
    {t : DiffField (m + 1) M // RawAdmissible (.H 0 s) t} ≃
      {b : BoundaryData m M // BoundaryValid s b} where
  toFun t := ⟨boundary_extract s t.val, boundary_extract_valid s t.val t.property⟩
  invFun b := ⟨boundary_build s b.val, boundary_build_raw s b.val b.property⟩
  left_inv t := Subtype.ext (boundary_reconstruct s t.val t.property)
  right_inv b := by
    apply Subtype.ext
    apply BoundaryData.ext
    · simp [boundary_extract, boundary_build]
    · simp [boundary_extract, boundary_build]
    · funext j
      simp [boundary_extract, boundary_build]
    · funext i
      simp [boundary_extract, boundary_build]

#print axioms boundary_slot_equiv

/-- Binary encoding of ordinary vertical slots and the two horizontal words. -/
def BoundaryWords (m c d : ℕ) :=
  {w : (Fin m → Bool) × (Fin c → Bool) × (Fin d → Bool) //
    (w.1 ≠ (fun _ => false) → w.2.1 = (fun _ => true)) ∧
    (w.1 ≠ (fun _ => true) → w.2.2 = (fun _ => true))}

private def boundary_words_zero_equiv (c d : ℕ) :
    BoundaryWords 0 c d ≃ (Fin c → Bool) × (Fin d → Bool) where
  toFun w := w.val.2
  invFun w := ⟨(fun i => Fin.elim0 i, w), by
    constructor <;> intro h <;> exact (h (funext fun i => Fin.elim0 i)).elim⟩
  left_inv w := by
    apply Subtype.ext
    exact Prod.ext (funext fun i => Fin.elim0 i) rfl
  right_inv _ := rfl

private noncomputable def boundary_words_sum_equiv (m c d : ℕ) (hm : 0 < m) :
    BoundaryWords m c d ≃
      (Fin c → Bool) ⊕ (Fin d → Bool) ⊕
        {u : Fin m → Bool // u ≠ (fun _ => false) ∧ u ≠ (fun _ => true)} := by
  classical
  have hft : (fun _ : Fin m => false) ≠ (fun _ => true) := by
    intro h
    have := congrFun h ⟨0, hm⟩
    contradiction
  refine {
    toFun := fun w => if hf : w.val.1 = (fun _ => false) then Sum.inl w.val.2.1
      else if ht : w.val.1 = (fun _ => true) then Sum.inr (Sum.inl w.val.2.2)
      else Sum.inr (Sum.inr ⟨w.val.1, hf, ht⟩)
    invFun := fun w => match w with
      | .inl l => ⟨((fun _ => false), l, (fun _ => true)), by simp⟩
      | .inr (.inl r) => ⟨((fun _ => true), (fun _ => true), r), by simp⟩
      | .inr (.inr u) => ⟨(u.val, (fun _ => true), (fun _ => true)), by simp⟩
    left_inv := ?_
    right_inv := ?_ }
  · rintro ⟨⟨u,l,r⟩,hl,hr⟩
    dsimp
    by_cases hf : u = (fun _ => false)
    · simp only [hf, ↓reduceDIte]
      apply Subtype.ext
      exact Prod.ext rfl (Prod.ext rfl (hr (by simpa [hf] using hft)).symm)
    · simp only [hf, ↓reduceDIte]
      by_cases ht : u = (fun _ => true)
      · simp only [ht, ↓reduceDIte]
        apply Subtype.ext
        exact Prod.ext rfl (Prod.ext (hl hf).symm rfl)
      · simp only [ht, ↓reduceDIte]
        exact Subtype.ext (Prod.ext rfl (Prod.ext (hl hf).symm (hr ht).symm))
  · intro w
    rcases w with l | (r | u)
    · simp
    · simp [Ne.symm hft]
    · simp [u.property.1, u.property.2]

/-- The empty vertical word leaves two independent binary horizontal words. -/
theorem boundary_words_zero_card (c d : ℕ) : Nat.card (BoundaryWords 0 c d) = 2 ^ (c + d) := by
  rw [Nat.card_congr (boundary_words_zero_equiv c d), Nat.card_prod]
  simp [pow_add]

/-- The three disjoint vertical-support cases give the subtraction-free E identity. -/
theorem boundary_words_pos_card (m c d : ℕ) (hm : 0 < m) :
    Nat.card (BoundaryWords m c d) + 2 = 2 ^ m + 2 ^ c + 2 ^ d := by
  classical
  have hft : (fun _ : Fin m => false) ≠ (fun _ => true) := by
    intro h
    have := congrFun h ⟨0, hm⟩
    contradiction
  have hmix : Nat.card {u : Fin m → Bool //
      u ≠ (fun _ => false) ∧ u ≠ (fun _ => true)} = 2 ^ m - 2 := by
    simp only [Nat.card_eq_fintype_card]
    have h := Fintype.card_subtype_compl
      (fun u : Fin m → Bool => u = (fun _ => false) ∨ u = (fun _ => true))
    rw [Fintype.card_subtype_eq_or_eq_of_ne hft] at h
    simpa only [not_or, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using h
  rw [Nat.card_congr (boundary_words_sum_equiv m c d hm), Nat.card_sum,
    Nat.card_sum, hmix]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have htwo : 2 ≤ 2 ^ m := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  omega

#print axioms boundary_words_zero_card
#print axioms boundary_words_pos_card

/-- The six ordered pairs of distinct nonzero Klein values. -/
abbrev NZPair := {pq : K × K // pq.1 ≠ 0 ∧ pq.2 ≠ 0 ∧ pq.1 ≠ pq.2}

private theorem nz_pair_card : Nat.card NZPair = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The column pair separating the words of lengths `c` and `d`. -/
def pivot (c d : ℕ) : Fin (c + (d + 1)) := Fin.natAdd c 0

private def boundary_word_build {m c d : ℕ} (x : NZPair) (w : BoundaryWords m c d) :
    BoundaryData m (c + (d + 1)) where
  p := x.val.1
  q := x.val.2
  h := Fin.addCases (fun j => if w.val.2.1 j then x.val.1 + x.val.2 else x.val.2)
    (Fin.cases (x.val.1 + x.val.2)
      (fun j => if w.val.2.2 j then x.val.1 + x.val.2 else x.val.1))
  v i := if w.val.1 i then x.val.2 else x.val.1

private theorem boundary_word_build_valid {m c d : ℕ} (x : NZPair)
    (w : BoundaryWords m c d) : BoundaryValid (pivot c d) (boundary_word_build x w) := by
  obtain ⟨hp,hq,hpq⟩ := x.property
  have hz : x.val.1 + x.val.2 ≠ 0 := by
    rw [ne_eq, add_eq_zero_iff_eq_neg, IsAddKleinFour.neg_eq_self]
    exact hpq
  have hzp : x.val.1 + x.val.2 ≠ x.val.1 := by simpa using hq
  have hzq : x.val.1 + x.val.2 ≠ x.val.2 := by simpa using hp
  refine ⟨hp,hq,hpq,?_,?_,?_,?_,?_,?_⟩
  · simp [boundary_word_build, pivot]
  · intro j
    refine Fin.addCases (fun l => ?_) (fun r => ?_) j
    · simp only [boundary_word_build, Fin.addCases_left]
      split <;> assumption
    · refine Fin.cases ?_ (fun r => ?_) r
      · simpa [boundary_word_build] using hz
      · simp only [boundary_word_build, Fin.addCases_right, Fin.cases_succ]
        split <;> assumption
  · intro i
    simp only [boundary_word_build]
    split <;> assumption
  · intro j
    refine Fin.addCases (fun l hl => ?_) (fun r hr => ?_) j
    · simp only [boundary_word_build, Fin.addCases_left]
      split
      · exact hzp
      · exact Ne.symm hpq
    · have hr' := r.isLt
      simp only [Fin.lt_def, Fin.val_natAdd, pivot, Fin.val_zero] at hr
      omega
  · intro j
    refine Fin.addCases (fun l hl => ?_) (fun r hr => ?_) j
    · have hl' := l.isLt
      simp only [Fin.lt_def, Fin.val_castAdd, pivot, Fin.val_natAdd,
        Fin.val_zero] at hl
      omega
    · refine Fin.cases (fun h => ?_) (fun r _ => ?_) r hr
      · exact (lt_irrefl _ h).elim
      · simp only [boundary_word_build, Fin.addCases_right, Fin.cases_succ]
        split
        · exact hzq
        · exact hpq
  · intro i j
    refine Fin.addCases (fun l => ?_) (fun r => ?_) j
    · by_cases hu : w.val.1 = (fun _ => false)
      · simp only [boundary_word_build, Fin.addCases_left, hu, Bool.false_eq_true,
          ↓reduceIte]
        split
        · exact hzp
        · exact Ne.symm hpq
      · have hl := w.property.1 hu
        simp only [boundary_word_build, Fin.addCases_left, hl, ↓reduceIte]
        split
        · exact hzq
        · exact hzp
    · refine Fin.cases ?_ (fun r => ?_) r
      · simp only [boundary_word_build, Fin.addCases_right, Fin.cases_zero]
        split
        · exact hzq
        · exact hzp
      · by_cases hu : w.val.1 = (fun _ => true)
        · simp only [boundary_word_build, Fin.addCases_right, Fin.cases_succ, hu,
            ↓reduceIte]
          split
          · exact hzq
          · exact hpq
        · have hr := w.property.2 hu
          simp only [boundary_word_build, Fin.addCases_right, Fin.cases_succ, hr, ↓reduceIte]
          split
          · exact hzq
          · exact hzp

private def boundary_word_map (m c d : ℕ) (w : NZPair × BoundaryWords m c d) :
    {b : BoundaryData m (c + (d + 1)) // BoundaryValid (pivot c d) b} :=
  ⟨boundary_word_build w.1 w.2, boundary_word_build_valid w.1 w.2⟩

private theorem boundary_word_map_injective (m c d : ℕ) :
    Function.Injective (boundary_word_map m c d) := by
  rintro ⟨x,w⟩ ⟨y,z⟩ he
  have hp := congrArg (fun b => b.val.p) he
  have hq := congrArg (fun b => b.val.q) he
  have hxy : x = y := Subtype.ext (Prod.ext hp hq)
  subst y
  have hi {p q : K} (hpq : p ≠ q) :
      Function.Injective (fun b : Bool => if b then p else q) := by
    intro a b h
    cases a <;> cases b <;> simp_all
  have hzp : x.val.1 + x.val.2 ≠ x.val.1 := by simpa using x.property.2.1
  have hzq : x.val.1 + x.val.2 ≠ x.val.2 := by simpa using x.property.1
  suffices w = z by rw [this]
  apply Subtype.ext
  apply Prod.ext
  · funext i
    apply hi (Ne.symm x.property.2.2)
    exact congrArg (fun b => b.val.v i) he
  · apply Prod.ext
    · funext j
      apply hi hzq
      have h := congrArg (fun b => b.val.h (j.castAdd (d + 1))) he
      simpa [boundary_word_map, boundary_word_build] using h
    · funext j
      apply hi hzp
      have h := congrArg (fun b => b.val.h (j.succ.natAdd c)) he
      simpa [boundary_word_map, boundary_word_build] using h

private theorem boundary_word_map_surjective (m c d : ℕ) :
    Function.Surjective (boundary_word_map m c d) := by
  classical
  rintro ⟨b,hp,hq,hpq,hs,hh,hv,hl,hr,hcross⟩
  have all (t : K) : t = b.p + b.q ∨ t = b.p ∨ t = b.q ∨ t = 0 := by
    have ht : t ∈ ({b.p + b.q, b.p, b.q, 0} : Finset K) := by
      rw [IsAddKleinFour.eq_finset_univ hp hq hpq]
      exact Finset.mem_univ t
    simpa only [Finset.mem_insert, Finset.mem_singleton] using ht
  have vu (i : Fin m) : ∃ a : Bool, (if a then b.q else b.p) = b.v i := by
    rcases all (b.v i) with h | h | h | h
    · exact (hcross i (pivot c d) (hs.trans h.symm)).elim
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
    · exact (hv i h).elim
  have vl (j : Fin c) : ∃ a : Bool,
      (if a then b.p + b.q else b.q) = b.h (j.castAdd (d + 1)) := by
    rcases all (b.h (j.castAdd (d + 1))) with h | h | h | h
    · exact ⟨true,h.symm⟩
    · exact (hl _ (by simp [pivot, Fin.lt_def]) h).elim
    · exact ⟨false,h.symm⟩
    · exact (hh _ h).elim
  have vr (j : Fin d) : ∃ a : Bool,
      (if a then b.p + b.q else b.p) = b.h (j.succ.natAdd c) := by
    rcases all (b.h (j.succ.natAdd c)) with h | h | h | h
    · exact ⟨true,h.symm⟩
    · exact ⟨false,h.symm⟩
    · exact (hr _ (by simp [pivot, Fin.lt_def]) h).elim
    · exact (hh _ h).elim
  choose u hu using vu
  choose l hleft using vl
  choose r hright using vr
  have hw : (u ≠ (fun _ => false) → l = (fun _ => true)) ∧
      (u ≠ (fun _ => true) → r = (fun _ => true)) := by
    constructor
    · intro hnu
      funext j
      cases hj : l j with
      | true => rfl
      | false =>
        exfalso
        apply hnu
        funext i
        cases hi : u i with
        | false => rfl
        | true =>
          exfalso
          apply hcross i (j.castAdd (d + 1))
          have h1 : b.q = b.h (j.castAdd (d + 1)) := by simpa [hj] using hleft j
          have h2 : b.q = b.v i := by simpa [hi] using hu i
          exact h1.symm.trans h2
    · intro hnu
      funext j
      cases hj : r j with
      | true => rfl
      | false =>
        exfalso
        apply hnu
        funext i
        cases hi : u i with
        | true => rfl
        | false =>
          exfalso
          apply hcross i (j.succ.natAdd c)
          have h1 : b.p = b.h (j.succ.natAdd c) := by simpa [hj] using hright j
          have h2 : b.p = b.v i := by simpa [hi] using hu i
          exact h1.symm.trans h2
  refine ⟨(⟨(b.p,b.q),hp,hq,hpq⟩,⟨(u,l,r),hw⟩), ?_⟩
  apply Subtype.ext
  apply BoundaryData.ext
  · rfl
  · rfl
  · funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa [boundary_word_map, boundary_word_build] using hleft j
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa [boundary_word_map, boundary_word_build, pivot] using hs.symm
      · simpa [boundary_word_map, boundary_word_build] using hright j
  · funext i
    exact hu i

/-- A boundary field consists of a six-way ordered-pair choice and three binary words. -/
noncomputable def boundary_word_equiv (m c d : ℕ) :
    {t : DiffField (m + 1) (c + (d + 1)) // RawAdmissible (.H 0 (pivot c d)) t} ≃
      NZPair × BoundaryWords m c d :=
  (boundary_slot_equiv m _ (pivot c d)).trans
    (Equiv.ofBijective (boundary_word_map m c d)
      ⟨boundary_word_map_injective m c d, boundary_word_map_surjective m c d⟩).symm

/-- Lemma 6 for a top boundary with no ordinary vertical slots. -/
theorem boundary_count_zero (c d : ℕ) :
    N_e (.H 0 (pivot c d) : Edge 2 (c + (d + 1) + 1)) = 6 * 2 ^ (c + d) := by
  unfold N_e
  rw [Nat.card_congr (boundary_word_equiv 0 c d), Nat.card_prod,
    nz_pair_card, boundary_words_zero_card]

/-- Lemma 6 for a top boundary with a nonempty ordinary vertical word. -/
theorem boundary_count_pos (m c d : ℕ) (hm : 0 < m) :
    N_e (.H 0 (pivot c d) : Edge (m + 1 + 1) (c + (d + 1) + 1)) + 12 =
      6 * (2 ^ m + 2 ^ c + 2 ^ d) := by
  have hw := boundary_words_pos_card m c d hm
  unfold N_e
  rw [Nat.card_congr (boundary_word_equiv m c d), Nat.card_prod, nz_pair_card]
  omega

#print axioms boundary_word_equiv
#print axioms boundary_count_zero
#print axioms boundary_count_pos

/-- Row reflection preserves the root-zero count at each horizontal edge. -/
theorem horizontal_count_row_reflect {N M : ℕ} (i : Fin (N + 1)) (j : Fin M) :
    N_e (.H i.rev j : Edge (N + 1) (M + 1)) = N_e (.H i j) := by
  let e : Edge (N + 1) (M + 1) := .H i j
  have hc := Nat.card_congr
    ((transposeDefectEquiv (C := Fin 4) e).trans
      ((reflectDefectEquiv (C := Fin 4) (transposeEdge e)).trans
        (transposeDefectEquiv (C := Fin 4) (reflectEdge (transposeEdge e)))))
  change Nat.card {f : Cell (N + 1) (M + 1) → Fin 4 //
    DefectAt (.H i j : Edge (N + 1) (M + 1)) f} =
    Nat.card {f : Cell (N + 1) (M + 1) → Fin 4 //
      DefectAt (.H i.rev j : Edge (N + 1) (M + 1)) f} at hc
  rw [count_fixed_edge, count_fixed_edge] at hc
  omega

/-- Lemma 6 at the bottom boundary of a two-row rectangle. -/
theorem boundary_count_bottom_zero (c d : ℕ) :
    N_e (.H (Fin.last 1) (pivot c d) : Edge 2 (c + (d + 1) + 1)) =
      6 * 2 ^ (c + d) := by
  have h := horizontal_count_row_reflect (N := 1) (0 : Fin 2) (pivot c d)
  simpa using h.trans (boundary_count_zero c d)

/-- Lemma 6 at the bottom boundary with a nonempty ordinary vertical word. -/
theorem boundary_count_bottom_pos (m c d : ℕ) (hm : 0 < m) :
    N_e (.H (Fin.last (m + 1)) (pivot c d) :
      Edge (m + 1 + 1) (c + (d + 1) + 1)) + 12 =
        6 * (2 ^ m + 2 ^ c + 2 ^ d) := by
  have h := horizontal_count_row_reflect (N := m + 1) (0 : Fin (m + 1 + 1)) (pivot c d)
  simpa using (congrArg (fun a => a + 12) h).trans (boundary_count_pos m c d hm)

#print axioms horizontal_count_row_reflect
#print axioms boundary_count_bottom_zero
#print axioms boundary_count_bottom_pos

/-- The boundary-word count, including the empty ordinary-vertical word. -/
def E (m c d : ℕ) : ℕ :=
  if m = 0 then 2 ^ (c + d) else 2 ^ m + 2 ^ c + 2 ^ d - 2

/-- Lemma 6 in a single formula, with the two side lengths explicit. -/
theorem boundary_count (m c d : ℕ) :
    N_e (.H 0 (pivot c d) : Edge (m + 1 + 1) (c + (d + 1) + 1)) =
      6 * E m c d := by
  by_cases hm : m = 0
  · subst m
    simpa [E] using boundary_count_zero c d
  · have h := boundary_count_pos m c d (Nat.pos_of_ne_zero hm)
    simp only [E, hm, ↓reduceIte]
    omega

/-- The per-position top-boundary count in the step-count API. -/
theorem boundary_count_at {m M : ℕ} (s : Fin M) :
    N_e (.H 0 s : Edge (m + 1 + 1) (M + 1)) =
      6 * E m s.val (M - 1 - s.val) := by
  have aux (c d : ℕ) {L : ℕ} (hL : L = c + (d + 1)) (j : Fin L) (hj : j.val = c) :
      N_e (.H 0 j : Edge (m + 1 + 1) (L + 1)) = 6 * E m c d := by
    subst L
    have he : j = pivot c d := Fin.ext (by simpa [pivot] using hj)
    subst j
    exact boundary_count m c d
  exact aux s.val (M - 1 - s.val) (by have := s.isLt; omega) s rfl

/-- Both boundary rows have the same exact E count. -/
theorem boundary_rows_count {m M : ℕ} (r : Fin (m + 1 + 1)) (s : Fin M)
    (hr : r = 0 ∨ r = Fin.last (m + 1)) :
    N_e (.H r s : Edge (m + 1 + 1) (M + 1)) =
      6 * E m s.val (M - 1 - s.val) := by
  rcases hr with rfl | rfl
  · exact boundary_count_at s
  · have h := horizontal_count_row_reflect (0 : Fin (m + 1 + 1)) s
    simpa using h.trans (boundary_count_at s)

#print axioms boundary_rows_count

end D5.S3.SpinModels.KingDefects.KingHorizontal
