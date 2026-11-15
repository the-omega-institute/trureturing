/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Boundary rows, word encodings, and the horizontal cut equivalence. -/
/-
admission_basis: open-problem-resolution (#30641; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229571.result, HardinA229573.result, HardinA229574.result, HardinA229575.result, HardinA229576.result, HardinA229577.result, HardinA229578.result)
BoundaryData: proof_shape=bind-only; consumers=KingHorizontal.BoundaryValid,KingHorizontal.InteriorSlots,KingHorizontal.boundary_bottom_shared,KingHorizontal.boundary_bottom_slot_equiv,KingHorizontal.boundary_build,KingHorizontal.boundary_build_raw,KingHorizontal.boundary_extract,KingHorizontal.boundary_extract_valid,KingHorizontal.boundary_slot_equiv,KingHorizontal.boundary_slots_one_column,KingHorizontal.boundary_top_shared,KingHorizontal.boundary_word_build,KingHorizontal.boundary_word_build_valid,KingHorizontal.boundary_word_equiv,KingHorizontal.boundary_word_map,KingHorizontal.boundary_word_map_injective,KingHorizontal.boundary_word_map_surjective,KingHorizontal.coded_boundaries_shared,KingHorizontal.coded_boundary,KingHorizontal.coded_boundary_left,KingHorizontal.coded_boundary_right,KingHorizontal.coded_boundary_valid,KingHorizontal.cut_slots_equiv,KingHorizontal.interiorDecode,KingHorizontal.interiorEncode,KingHorizontal.interiorEncode_decode,KingHorizontal.interior_one_column_count
BoundaryValid: proof_shape=bind-only; consumers=KingHorizontal.InteriorSlots,KingHorizontal.boundary_bottom_shared,KingHorizontal.boundary_bottom_slot_equiv,KingHorizontal.boundary_build_raw,KingHorizontal.boundary_extract_valid,KingHorizontal.boundary_slot_equiv,KingHorizontal.boundary_slots_one_column,KingHorizontal.boundary_top_shared,KingHorizontal.boundary_word_build_valid,KingHorizontal.boundary_word_equiv,KingHorizontal.boundary_word_map,KingHorizontal.boundary_word_map_injective,KingHorizontal.boundary_word_map_surjective,KingHorizontal.coded_boundary_valid,KingHorizontal.cut_slots_equiv,KingHorizontal.interiorDecode,KingHorizontal.interiorEncode,KingHorizontal.interiorEncode_decode,KingHorizontal.interior_one_column_count
boundary_build: proof_shape=bind-only; consumers=KingHorizontal.boundary_build_raw,KingHorizontal.boundary_reconstruct,KingHorizontal.boundary_slot_equiv
boundary_extract: proof_shape=bind-only; consumers=KingHorizontal.boundary_bottom_shared,KingHorizontal.boundary_extract_valid,KingHorizontal.boundary_reconstruct,KingHorizontal.boundary_slot_equiv
boundary_h: proof_shape=bind-only; consumers=KingHorizontal.boundary_extract_valid,KingHorizontal.boundary_reconstruct,KingHorizontal.boundary_top_shared
boundary_v: proof_shape=bind-only; consumers=KingHorizontal.boundary_extract_valid,KingHorizontal.boundary_reconstruct
boundary_build_raw: proof_shape=bind-only; consumers=KingHorizontal.boundary_slot_equiv
boundary_extract_valid: proof_shape=bind-only; consumers=KingHorizontal.boundary_bottom_shared,KingHorizontal.boundary_slot_equiv
boundary_reconstruct: proof_shape=bind-only; consumers=KingHorizontal.boundary_slot_equiv
boundary_slot_equiv: proof_shape=bind-only; consumers=KingHorizontal.boundary_bottom_shared,KingHorizontal.boundary_bottom_slot_equiv,KingHorizontal.boundary_slots_one_column,KingHorizontal.boundary_top_shared,KingHorizontal.boundary_word_equiv,KingHorizontal.cut_slots_equiv
BoundaryWords: proof_shape=bind-only; consumers=KingHorizontal.boundary_count_pos,KingHorizontal.boundary_count_zero,KingHorizontal.boundary_word_build,KingHorizontal.boundary_word_build_valid,KingHorizontal.boundary_word_equiv,KingHorizontal.boundary_word_map,KingHorizontal.boundary_word_map_injective,KingHorizontal.boundary_word_map_surjective,KingHorizontal.boundary_words_pos_card,KingHorizontal.boundary_words_sum_equiv,KingHorizontal.boundary_words_zero_card,KingHorizontal.boundary_words_zero_equiv
boundary_words_zero_equiv: proof_shape=bind-only; consumers=KingHorizontal.boundary_words_zero_card
boundary_words_sum_equiv: proof_shape=bind-only; consumers=KingHorizontal.boundary_words_pos_card
boundary_words_zero_card: proof_shape=bind-only; consumers=KingHorizontal.boundary_count_zero
boundary_words_pos_card: proof_shape=bind-only; consumers=KingHorizontal.boundary_count_pos
pivot: proof_shape=bind-only; consumers=KingHorizontal.boundary_count,KingHorizontal.boundary_count_at,KingHorizontal.boundary_count_pos,KingHorizontal.boundary_count_zero,KingHorizontal.boundary_one_column,KingHorizontal.boundary_word_build_valid,KingHorizontal.boundary_word_equiv,KingHorizontal.boundary_word_map,KingHorizontal.boundary_word_map_injective,KingHorizontal.boundary_word_map_surjective,KingHorizontal.coded_boundaries_shared,KingHorizontal.coded_boundary_valid,KingHorizontal.cut_row,KingHorizontal.horizontal_three_rows,KingHorizontal.interiorDecode,KingHorizontal.interiorEncode,KingHorizontal.interiorEncode_decode,KingHorizontal.interior_code_equiv,KingHorizontal.interior_count,KingHorizontal.interior_count_alphabets,KingHorizontal.interior_count_support,KingHorizontal.interior_row_sum,KingHorizontal.interior_three_rows_count
boundary_word_build: proof_shape=bind-only; consumers=KingHorizontal.boundary_word_build_valid,KingHorizontal.boundary_word_map,KingHorizontal.boundary_word_map_injective,KingHorizontal.boundary_word_map_surjective
boundary_word_build_valid: proof_shape=bind-only; consumers=KingHorizontal.boundary_word_map,KingHorizontal.boundary_word_map_injective,KingHorizontal.boundary_word_map_surjective
boundary_word_map: proof_shape=bind-only; consumers=KingHorizontal.boundary_word_equiv,KingHorizontal.boundary_word_map_injective,KingHorizontal.boundary_word_map_surjective
boundary_word_map_injective: proof_shape=bind-only; consumers=KingHorizontal.boundary_word_equiv
boundary_word_map_surjective: proof_shape=bind-only; consumers=KingHorizontal.boundary_word_equiv
boundary_word_equiv: proof_shape=bind-only; consumers=KingHorizontal.boundary_count_pos,KingHorizontal.boundary_count_zero
boundary_count_zero: proof_shape=bind-only; consumers=KingHorizontal.boundary_count
boundary_count_pos: proof_shape=bind-only; consumers=KingHorizontal.boundary_count
horizontal_count_row_reflect: proof_shape=bind-only; consumers=KingHorizontal.boundary_rows_count,KingHorizontal.horizontal_sum,KingHorizontal.horizontal_three_rows,KingHorizontal.horizontal_two_columns
E: proof_shape=bind-only; consumers=KingHorizontal.P,KingHorizontal.boundary_count,KingHorizontal.boundary_count_at,KingHorizontal.boundary_one_column,KingHorizontal.boundary_row_sum,KingHorizontal.boundary_rows_count,KingHorizontal.horizontal_three_rows,KingHorizontal.horizontal_two_rows,KingHorizontal.interior_count,KingHorizontal.interior_endpoint_value,KingHorizontal.interior_middle_value,KingHorizontal.interior_row_sum,KingHorizontal.interior_three_rows_count,KingHorizontal.six_case_value,KingHorizontal.support_case_eval
boundary_count: proof_shape=bind-only; consumers=KingHorizontal.boundary_count_at,KingHorizontal.boundary_one_column
boundary_count_at: proof_shape=bind-only; consumers=KingHorizontal.boundary_row_sum,KingHorizontal.boundary_rows_count,KingHorizontal.horizontal_three_rows
boundary_rows_count: proof_shape=bind-only; consumers=KingHorizontal.horizontal_two_rows
row_reflect: proof_shape=bind-only; consumers=KingHorizontal.boundary_bottom_shared,KingHorizontal.row_reflect_differentiate,KingHorizontal.row_reflect_equiv,KingHorizontal.row_reflect_raw
row_reflect_differentiate: proof_shape=bind-only; consumers=KingHorizontal.row_reflect_raw
row_reflect_raw: proof_shape=bind-only; consumers=KingHorizontal.boundary_bottom_shared,KingHorizontal.row_reflect_equiv
row_reflect_equiv: proof_shape=bind-only; consumers=KingHorizontal.boundary_bottom_slot_equiv
boundary_bottom_slot_equiv: proof_shape=bind-only; consumers=KingHorizontal.boundary_bottom_shared,KingHorizontal.cut_slots_equiv
top_row: proof_shape=bind-only; consumers=KingHorizontal.join_restrict,KingHorizontal.top_edge,KingHorizontal.top_field,KingHorizontal.top_field_join
bottom_row: proof_shape=bind-only; consumers=KingHorizontal.bottom_edge,KingHorizontal.bottom_field,KingHorizontal.bottom_field_join,KingHorizontal.bottom_field_raw,KingHorizontal.join_restrict,KingHorizontal.raw_of_halves
top_field: proof_shape=bind-only; consumers=KingHorizontal.horizontal_cut_equiv,KingHorizontal.join_restrict,KingHorizontal.raw_of_halves,KingHorizontal.top_edge_value,KingHorizontal.top_field_join,KingHorizontal.top_field_raw
bottom_field: proof_shape=bind-only; consumers=KingHorizontal.bottom_edge_value,KingHorizontal.bottom_field_join,KingHorizontal.bottom_field_raw,KingHorizontal.horizontal_cut_equiv,KingHorizontal.join_restrict,KingHorizontal.raw_of_halves
top_edge: proof_shape=bind-only; consumers=KingHorizontal.raw_of_halves,KingHorizontal.top_edge_value,KingHorizontal.top_field_raw
bottom_edge: proof_shape=bind-only; consumers=KingHorizontal.bottom_edge_value,KingHorizontal.bottom_field_raw,KingHorizontal.raw_of_halves
top_edge_value: proof_shape=bind-only; consumers=KingHorizontal.raw_of_halves,KingHorizontal.top_field_raw
bottom_edge_value: proof_shape=bind-only; consumers=KingHorizontal.bottom_field_raw,KingHorizontal.raw_of_halves
cut_row: proof_shape=bind-only; consumers=KingHorizontal.bottom_field_raw,KingHorizontal.horizontal_cut_equiv,KingHorizontal.horizontal_sum,KingHorizontal.horizontal_two_columns,KingHorizontal.interior_count,KingHorizontal.interior_count_alphabets,KingHorizontal.interior_count_support,KingHorizontal.interior_one_column_count,KingHorizontal.interior_row_sum,KingHorizontal.interior_slot_equiv,KingHorizontal.interior_three_rows_count,KingHorizontal.raw_of_halves,KingHorizontal.top_field_raw
top_field_raw: proof_shape=bind-only; consumers=KingHorizontal.horizontal_cut_equiv
bottom_field_raw: proof_shape=bind-only; consumers=KingHorizontal.horizontal_cut_equiv
raw_of_halves: proof_shape=bind-only; consumers=KingHorizontal.horizontal_cut_equiv
join_field: proof_shape=bind-only; consumers=KingHorizontal.bottom_field_join,KingHorizontal.horizontal_cut_equiv,KingHorizontal.join_restrict,KingHorizontal.top_field_join
top_field_join: proof_shape=bind-only; consumers=KingHorizontal.horizontal_cut_equiv
bottom_field_join: proof_shape=bind-only; consumers=KingHorizontal.horizontal_cut_equiv
join_restrict: proof_shape=bind-only; consumers=KingHorizontal.horizontal_cut_equiv
CutFields: proof_shape=bind-only; consumers=KingHorizontal.cut_slots_equiv,KingHorizontal.horizontal_cut_equiv,KingHorizontal.interior_slot_equiv
horizontal_cut_equiv: proof_shape=bind-only; consumers=KingHorizontal.interior_slot_equiv
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fin.Tuple.Basic

/-! Horizontal defects, with dimensions expressed as numbers of steps. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal

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
  h := Fin.cons (Function.update b.h s 0) (fun _ => b.h)
  v := Fin.cons (fun j => if j.val ≤ s.val then b.p else b.q) (fun i _ => b.v i)

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
private theorem boundary_v {m M : ℕ} (s : Fin M) (t : DiffField (m + 1) M)
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
private theorem boundary_build_raw {m M : ℕ} (s : Fin M) (b : BoundaryData m M)
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
    · simp [boundary_build, add_comm]
  refine ⟨hc, ?_⟩
  intro e
  cases e with
  | H i j =>
    refine Fin.cases ?_ (fun a => ?_) i <;>
      simp [edgeValue, boundary_build, Function.update_apply, hh, Edge.H.injEq]
  | V i j =>
    suffices edgeValue (boundary_build s b) (.V i j) ≠ 0 by simpa using this
    dsimp only [edgeValue]
    refine Fin.cases ?_ (fun a => ?_) i
    · simp only [boundary_build, Fin.cons_zero]
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
private theorem boundary_extract_valid {m M : ℕ} (s : Fin M) (t : DiffField (m + 1) M)
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
private theorem boundary_reconstruct {m M : ℕ} (s : Fin M) (t : DiffField (m + 1) M)
    (ht : RawAdmissible (.H 0 s) t) : boundary_build s (boundary_extract s t) = t := by
  apply DiffField.ext
  · funext i j
    refine Fin.cases ?_ (fun a => ?_) i
    · simpa [boundary_build, boundary_extract, Function.update_apply] using
        (boundary_h s t ht 0 j).symm
    · simpa [boundary_build, boundary_extract] using (boundary_h s t ht a.succ j).symm
  · funext i j
    refine Fin.cases ?_ (fun a => ?_) i
    · simpa [boundary_build, boundary_extract] using (boundary_v s t ht 0 j).symm
    · simpa [boundary_build, boundary_extract] using (boundary_v s t ht a.succ j).symm

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

/-- Binary encoding of ordinary vertical slots and the two horizontal words. -/
def BoundaryWords (m c d : ℕ) :=
  {w : (Fin m → Bool) × (Fin c → Bool) × (Fin d → Bool) //
    (w.1 ≠ (fun _ => false) → w.2.1 = (fun _ => true)) ∧
    (w.1 ≠ (fun _ => true) → w.2.2 = (fun _ => true))}

private def boundary_words_zero_equiv (c d : ℕ) :
    BoundaryWords 0 c d ≃ (Fin c → Bool) × (Fin d → Bool) :=
  (Equiv.subtypeUnivEquiv (by
    intro w
    constructor <;> intro h <;>
      exact (h (funext fun i => Fin.elim0 i)).elim)).trans (Equiv.uniqueProd _ _)


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
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two hm
  omega

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
    simpa using (Bool.injective_iff (f := fun b : Bool => if b then p else q)).mpr hpq.symm
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
private noncomputable def boundary_word_equiv (m c d : ℕ) :
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

def row_reflect {N M : ℕ} (t : DiffField N M) : DiffField N M where
  h i j := t.h i.rev j
  v i j := t.v i.rev j

private theorem row_reflect_differentiate {N M : ℕ}
    (f : Cell (N + 1) (M + 1) → K) :
    row_reflect (differentiate f) = differentiate (fun p => f (p.1.rev,p.2)) := by
  apply DiffField.ext
  · rfl
  · funext i j
    simp [row_reflect, differentiate, Fin.rev_castSucc, Fin.rev_succ, add_comm]

theorem row_reflect_raw {N M : ℕ} (r : Fin (N + 1)) (s : Fin M)
    (t : DiffField N M) (ht : RawAdmissible (.H r s) t) :
    RawAdmissible (.H r.rev s) (row_reflect t) := by
  let e : Edge (N + 1) (M + 1) := .H r s
  let f := (defectIntegrationEquiv e).symm (0,⟨t,ht⟩)
  let g := ((transposeDefectEquiv (C := K) e).trans
    ((reflectDefectEquiv (C := K) (transposeEdge e)).trans
      (transposeDefectEquiv (C := K) (reflectEdge (transposeEdge e))))) f
  have hg : DefectAt (.H r.rev s : Edge (N + 1) (M + 1))
      (fun p => integrate 0 t (p.1.rev,p.2)) := g.property
  have hraw := (raw_differentiate_iff _ _).mpr hg
  rw [← row_reflect_differentiate, differentiate_integrate 0 t ht.1] at hraw
  exact hraw

def row_reflect_equiv {N M : ℕ} (r : Fin (N + 1)) (s : Fin M) :
    {t : DiffField N M // RawAdmissible (.H r s) t} ≃
      {t : DiffField N M // RawAdmissible (.H r.rev s) t} where
  toFun t := ⟨row_reflect t.val, row_reflect_raw r s t.val t.property⟩
  invFun t := ⟨row_reflect t.val, by
    simpa using row_reflect_raw r.rev s t.val t.property⟩
  left_inv t := by apply Subtype.ext; apply DiffField.ext <;> simp [row_reflect]
  right_inv t := by apply Subtype.ext; apply DiffField.ext <;> simp [row_reflect]

/-- The bottom-boundary slot equivalence uses reflection of the complete field. -/
def boundary_bottom_slot_equiv (m M : ℕ) (s : Fin M) :
    {t : DiffField (m + 1) M // RawAdmissible (.H (Fin.last (m + 1)) s) t} ≃
      {b : BoundaryData m M // BoundaryValid s b} := by
  let transport :
      {t : DiffField (m + 1) M // RawAdmissible (.H (Fin.last (m + 1)).rev s) t} ≃
      {t : DiffField (m + 1) M // RawAdmissible (.H 0 s) t} :=
    Equiv.subtypeEquivRight (fun _ => by rw [Fin.rev_last])
  exact (row_reflect_equiv (Fin.last (m + 1)) s).trans
    (transport.trans (boundary_slot_equiv m M s))

private def top_row {A : ℕ} (B : ℕ) (i : Fin (A + 1)) : Fin (A + B + 1) :=
  Fin.castLE (by omega) i

private def bottom_row (A : ℕ) {B : ℕ} (i : Fin (B + 1)) : Fin (A + B + 1) :=
  Fin.natAdd A i

private def top_field {A B M : ℕ} (t : DiffField (A + B) M) : DiffField A M where
  h i j := t.h (top_row B i) j
  v i j := t.v (i.castAdd B) j

private def bottom_field {A B M : ℕ} (t : DiffField (A + B) M) : DiffField B M where
  h i j := t.h (bottom_row A i) j
  v i j := t.v (i.natAdd A) j

private def top_edge {A M : ℕ} (B : ℕ) : Edge (A + 1) (M + 1) →
    Edge (A + B + 1) (M + 1)
  | .H i j => .H (top_row B i) j
  | .V i j => .V (i.castAdd B) j
  | .D i j => .D (i.castAdd B) j
  | .A i j => .A (i.castAdd B) j

private def bottom_edge (A : ℕ) {B M : ℕ} : Edge (B + 1) (M + 1) →
    Edge (A + B + 1) (M + 1)
  | .H i j => .H (bottom_row A i) j
  | .V i j => .V (i.natAdd A) j
  | .D i j => .D (i.natAdd A) j
  | .A i j => .A (i.natAdd A) j

private theorem top_edge_value {A B M : ℕ} (t : DiffField (A + B) M)
    (e : Edge (A + 1) (M + 1)) : edgeValue (top_field t) e = edgeValue t (top_edge B e) := by
  cases e <;> rfl

private theorem bottom_edge_value {A B M : ℕ} (t : DiffField (A + B) M)
    (e : Edge (B + 1) (M + 1)) : edgeValue (bottom_field t) e =
      edgeValue t (bottom_edge A e) := by
  cases e <;> rfl

def cut_row (A B : ℕ) : Fin (A + B + 1) := pivot A B

private theorem top_field_raw {A B M : ℕ} (s : Fin M) (t : DiffField (A + B) M)
    (ht : RawAdmissible (.H (cut_row A B) s) t) :
    RawAdmissible (.H (Fin.last A) s) (top_field t) := by
  refine ⟨?_, ?_⟩
  · intro i j
    exact ht.1 (i.castAdd B) j
  · intro e
    rw [top_edge_value, ht.2]
    cases e <;> simp [top_edge, top_row, cut_row, pivot, Fin.ext_iff]

private theorem bottom_field_raw {A B M : ℕ} (s : Fin M) (t : DiffField (A + B) M)
    (ht : RawAdmissible (.H (cut_row A B) s) t) :
    RawAdmissible (.H 0 s) (bottom_field t) := by
  refine ⟨?_, ?_⟩
  · intro i j
    exact ht.1 (i.natAdd A) j
  · intro e
    rw [bottom_edge_value, ht.2]
    cases e with
    | H i j =>
      simp only [bottom_edge, Edge.H.injEq]
      constructor
      · rintro ⟨he,hj⟩
        refine ⟨?_,hj⟩
        apply Fin.ext
        have h := congrArg Fin.val he
        dsimp only [bottom_row, cut_row, pivot] at h
        simpa using h
      · rintro ⟨rfl,rfl⟩
        exact ⟨rfl,rfl⟩
    | V i j => simp [bottom_edge]
    | D i j => simp [bottom_edge]
    | A i j => simp [bottom_edge]

private theorem raw_of_halves {A B M : ℕ} (s : Fin M) (t : DiffField (A + B) M)
    (hu : RawAdmissible (.H (Fin.last A) s) (top_field t))
    (hl : RawAdmissible (.H (0 : Fin (B + 1)) s) (bottom_field t)) :
    RawAdmissible (.H (cut_row A B) s) t := by
  refine ⟨?_, ?_⟩
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · exact hu.1 i j
    · exact hl.1 i j
  · intro e
    have upper (d : Edge (A + 1) (M + 1)) := hu.2 d
    have lower (d : Edge (B + 1) (M + 1)) := hl.2 d
    simp_rw [top_edge_value] at upper
    simp_rw [bottom_edge_value] at lower
    cases e with
    | H i j =>
      by_cases hi : i.val ≤ A
      · have h := upper (.H ⟨i.val, by omega⟩ j)
        simpa [top_edge, top_row, cut_row, pivot, Fin.ext_iff] using h
      · have h := lower (.H ⟨i.val - A, by have := i.isLt; omega⟩ j)
        have hir : A + (i.val - A) = i.val := by omega
        have he : bottom_row A (⟨i.val - A, by omega⟩ : Fin (B + 1)) = i :=
          Fin.ext hir
        simpa [bottom_edge, he, cut_row, pivot, Fin.ext_iff, hir, hi, show i.val - A ≠ 0 by omega,
          show i.val ≠ A by omega] using h
    | V i j =>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa [top_edge] using upper (.V i j)
      · simpa [bottom_edge] using lower (.V i j)
    | D i j =>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa [top_edge] using upper (.D i j)
      · simpa [bottom_edge] using lower (.D i j)
    | A i j =>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa [top_edge] using upper (.A i j)
      · simpa [bottom_edge] using lower (.A i j)

private def join_field {A B M : ℕ} (u : DiffField A M) (l : DiffField B M) :
    DiffField (A + B) M where
  h := Fin.append (m := A) (n := B + 1) (Fin.init u.h) l.h
  v := Fin.append u.v l.v

private theorem top_field_join {A B M : ℕ} (u : DiffField A M) (l : DiffField B M)
    (hshare : ∀ j, u.h (Fin.last A) j = l.h 0 j) : top_field (join_field u l) = u := by
  apply DiffField.ext
  · funext i j
    refine Fin.lastCases ?_ (fun k => ?_) i
    · have he : top_row B (Fin.last A) = Fin.natAdd A (0 : Fin (B + 1)) :=
        Fin.ext (by simp [top_row])
      simpa only [top_field, join_field, he, Fin.append_right] using (hshare j).symm
    · have he : top_row B k.castSucc = k.castAdd (B + 1) := Fin.ext rfl
      simp [top_field, join_field, he, Fin.init]
  · funext i j
    simp [top_field, join_field]

private theorem bottom_field_join {A B M : ℕ} (u : DiffField A M) (l : DiffField B M) :
    bottom_field (join_field u l) = l := by
  apply DiffField.ext
  · funext i j
    simp [bottom_field, join_field, bottom_row]
  · funext i j
    simp [bottom_field, join_field]

private theorem join_restrict {A B M : ℕ} (t : DiffField (A + B) M) :
    join_field (top_field t) (bottom_field t) = t := by
  apply DiffField.ext
  · funext i j
    refine Fin.addCases (m := A) (n := B + 1) (fun k => ?_) (fun k => ?_) i <;>
      simp [join_field, Fin.init, top_field, bottom_field, top_row, bottom_row]
    rfl
  · funext i j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      simp [join_field, top_field, bottom_field]

def CutFields (A B M : ℕ) (s : Fin M) :=
  {q : DiffField A M × DiffField B M //
    RawAdmissible (.H (Fin.last A) s) q.1 ∧ RawAdmissible (.H 0 s) q.2 ∧
      ∀ j, q.1.h (Fin.last A) j = q.2.h 0 j}

def horizontal_cut_equiv (A B M : ℕ) (s : Fin M) :
    {t : DiffField (A + B) M // RawAdmissible (.H (cut_row A B) s) t} ≃
      CutFields A B M s where
  toFun t := ⟨(top_field t.val,bottom_field t.val),
    top_field_raw s t.val t.property, bottom_field_raw s t.val t.property, fun _ => rfl⟩
  invFun q := ⟨join_field q.val.1 q.val.2, by
    apply raw_of_halves s
    · rw [top_field_join _ _ q.property.2.2]
      exact q.property.1
    · rw [bottom_field_join]
      exact q.property.2.1⟩
  left_inv t := Subtype.ext (join_restrict t.val)
  right_inv q := by
    apply Subtype.ext
    exact Prod.ext (top_field_join _ _ q.property.2.2) (bottom_field_join _ _)

end D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal
