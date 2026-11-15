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
  deriving DecidableEq, Fintype

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
    simp only [BlockAvoids, ne_eq, Edge.H.injEq, Edge.V_ne_H, Edge.D_ne_H,
      Edge.A_ne_H, not_false_eq_true, true_and, and_true]
    constructor
    · intro he
      rcases ha with ha | ha
      · exact ha (by simpa using congrArg Fin.val he.1)
      · exact ha he.2
    · intro he
      have := congrArg Fin.val he.1
      simp at this
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = s
    · subst j
      simpa [edgeValue] using (ht.2 (.H 0 s)).mpr rfl
    · simp only [hj, and_false, ↓reduceIte]
      exact horizontal_slot_eq (.H 0 s) t ht j 0 1 (by decide)
        (fun a _ _ => clear a (Or.inr hj))
  · simp only [hi, false_and, ↓reduceIte]
    exact (horizontal_slot_eq (.H 0 s) t ht j 1 i
      (by simp only [Fin.le_iff_val_le_val]; have := i.isLt; omega)
      (fun a ha _ => clear a (Or.inl (by
        simp only [Fin.val_one] at ha
        omega)))).symm

/-- The first vertical slot splits at the defect; every later slot is constant. -/
theorem boundary_v {m M : ℕ} (s : Fin M) (t : DiffField (m + 1) M)
    (ht : RawAdmissible (.H 0 s) t) (i : Fin (m + 1)) (j : Fin (M + 1)) :
    t.v i j = if hi : i = 0 then
      (if j.val ≤ s.val then t.v 0 s.castSucc else t.v 0 s.succ)
      else t.v i 0 := by
  have clear (a : Fin M) (ha : i ≠ 0 ∨ a ≠ s) : BlockAvoids (.H 0 s) i a := by
    simp only [BlockAvoids, ne_eq, Edge.H.injEq, Edge.V_ne_H, Edge.D_ne_H,
      Edge.A_ne_H, not_false_eq_true, true_and, and_true]
    constructor
    · rintro ⟨h1,h2⟩
      rcases ha with ha | ha
      · exact ha (Fin.ext (congrArg Fin.val h1))
      · exact ha h2
    · rintro ⟨h1,_⟩
      have := congrArg Fin.val h1
      simp at this
  by_cases hi : i = 0
  · subst i
    simp only [dite_true]
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
  · simp only [hi, dite_false]
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
    simp only [edgeValue, Edge.V_ne_H, iff_false]
    refine Fin.cases ?_ (fun a => ?_) i
    · simp [boundary_build, hp, hq]
    · simpa [boundary_build] using hv a
  | D i j =>
    simp only [edgeValue, Edge.D_ne_H, iff_false]
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
    simp only [edgeValue, Edge.A_ne_H, iff_false]
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
  have hp : t.v 0 s.castSucc ≠ 0 := nz (.V 0 s.castSucc) (by simp)
  have hq : t.v 0 s.succ ≠ 0 := nz (.V 0 s.succ) (by simp)
  have hh (j : Fin M) : t.h 1 j ≠ 0 := nz (.H 1 j) (by simp)
  have hs : t.h 1 s = t.v 0 s.castSucc + t.v 0 s.succ := by
    have hc := ht.1 0 s
    have hz : t.h 0 s = 0 := (ht.2 (.H 0 s)).mpr rfl
    dsimp only [Cocycle] at hc
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
    have hn := nz (.A 0 j) (by simp)
    simpa [boundary_extract, edgeValue, htop, hv, add_eq_zero_iff_eq_neg] using hn
  · intro j hj
    have hj' : j ≠ s := ne_of_gt hj
    have htop : t.h 0 j = t.h 1 j := by
      simpa [hj'] using boundary_h s t ht 0 j
    have hv : t.v 0 j.castSucc = t.v 0 s.succ := by
      simpa [Nat.not_le_of_gt hj] using boundary_v s t ht 0 j.castSucc
    have hn := nz (.A 0 j) (by simp)
    simpa [boundary_extract, edgeValue, htop, hv, add_eq_zero_iff_eq_neg] using hn
  · intro a j
    have htop : t.h a.succ.castSucc j = t.h 1 j := by
      simpa using boundary_h s t ht a.succ.castSucc j
    have hv : t.v a.succ j.castSucc = t.v a.succ 0 := by
      simpa using boundary_v s t ht a.succ j.castSucc
    have hn := nz (.A a.succ j) (by simp)
    simpa [boundary_extract, edgeValue, htop, hv, add_eq_zero_iff_eq_neg] using hn

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
      exact congrArg (fun a => t.v a 0) (Fin.succ_pred _ _)

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

end D5.S3.SpinModels.KingDefects.KingHorizontal
