/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingGrid
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Literal king-grid colourings and decomposition by the unique defective edge. -/
/-
admission_basis: open-problem-resolution (#30641; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229571.result, HardinA229573.result, HardinA229574.result, HardinA229575.result, HardinA229576.result, HardinA229577.result, HardinA229578.result)
Cell: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.canonical_transpose_twice,KingClosedForm.normal_exists_unique,KingClosedForm.normal_unique,KingClosedForm.normalize,KingClosedForm.normalize_spec,KingClosedForm.symmetry,KingClosedForm.transpose_one,KingDifference.N_reflect,KingDifference.N_transpose,KingDifference.count_fixed_edge,KingDifference.count_from_fields,KingDifference.defectIntegrationEquiv,KingDifference.difference_unique,KingDifference.differentiate,KingDifference.differentiate_cocycle,KingDifference.differentiate_edgeValue,KingDifference.good_differentiate,KingDifference.integrate,KingDifference.integrate_differentiate,KingDifference.integrationEquiv,KingDifference.rainbow_block,KingDifference.raw_differentiate_iff,KingDifference.relabelDefectEquiv,KingGrid.DefectAt,KingGrid.L,KingGrid.OneDefect,KingGrid.T,KingGrid.corner,KingGrid.count_by_edge,KingGrid.defectAt_iff,KingGrid.defectEquiv,KingGrid.end0,KingGrid.end1,KingGrid.endpoints_distinct,KingGrid.goodBlock_surjective,KingGrid.labelled_count,KingGrid.labelled_eq_twentyFour,KingGrid.mono,KingGrid.normal,KingGrid.oneDefect_iff,KingGrid.oneDefect_surjective,KingGrid.oneDefect_usesThree,KingGrid.reflect,KingGrid.reflectDefectEquiv,KingGrid.reflect_mono,KingGrid.transpose,KingGrid.transposeDefectEquiv,KingGrid.transpose_mono,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_differentiate,KingHorizontal.row_reflect_raw,KingPath.literal_count,KingPath.literal_words,KingPath.normal_path,KingPath.oneDefect_path
Edge: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.transpose_one,KingDiagonal.N_D_closed,KingDiagonal.N_D_two_columns,KingDiagonal.diagonalSlotEquiv,KingDiagonal.diagonal_clear,KingDiagonal.diagonal_count,KingDiagonal.extract_valid,KingDiagonal.raw_h_ordinary,KingDiagonal.raw_h_special,KingDiagonal.raw_v_ordinary,KingDiagonal.raw_v_special,KingDiagonal.slot_raw,KingDiagonal.slot_reconstruction,KingDiagonal.special_block,KingDifference.BlockAvoids,KingDifference.N_D,KingDifference.N_H,KingDifference.N_e,KingDifference.N_reflect,KingDifference.N_transpose,KingDifference.RawAdmissible,KingDifference.count_by_kind,KingDifference.count_fixed_edge,KingDifference.count_from_fields,KingDifference.defectIntegrationEquiv,KingDifference.differentiate_edgeValue,KingDifference.edgeValue,KingDifference.fields_eq_six_canonical,KingDifference.goodBlock_of_raw,KingDifference.horizontal_slot_eq,KingDifference.raw_differentiate_iff,KingDifference.relabelDefectEquiv,KingDifference.sum_fields_by_kind,KingDifference.vertical_slot_eq,KingGrid.DefectAt,KingGrid.OneDefect,KingGrid.blockEdges,KingGrid.count_by_edge,KingGrid.defectAt_iff,KingGrid.defectEquiv,KingGrid.edgeSumEquiv,KingGrid.end0,KingGrid.end1,KingGrid.endpoints_distinct,KingGrid.goodBlock_surjective,KingGrid.labelled_eq_twentyFour,KingGrid.mono,KingGrid.oneDefect_iff,KingGrid.oneDefect_surjective,KingGrid.oneDefect_usesThree,KingGrid.reflectDefectEquiv,KingGrid.reflectEdge,KingGrid.reflect_mono,KingGrid.sum_edges,KingGrid.transposeDefectEquiv,KingGrid.transposeEdge,KingGrid.transpose_mono,KingHorizontal.CutFields,KingHorizontal.bottom_edge,KingHorizontal.bottom_edge_value,KingHorizontal.bottom_field_raw,KingHorizontal.boundary_bottom_shared,KingHorizontal.boundary_bottom_slot_equiv,KingHorizontal.boundary_build_raw,KingHorizontal.boundary_count,KingHorizontal.boundary_count_at,KingHorizontal.boundary_count_pos,KingHorizontal.boundary_count_zero,KingHorizontal.boundary_extract_valid,KingHorizontal.boundary_h,KingHorizontal.boundary_one_column,KingHorizontal.boundary_reconstruct,KingHorizontal.boundary_row_sum,KingHorizontal.boundary_rows_count,KingHorizontal.boundary_slot_equiv,KingHorizontal.boundary_slots_one_column,KingHorizontal.boundary_top_shared,KingHorizontal.boundary_v,KingHorizontal.boundary_word_equiv,KingHorizontal.cut_slots_equiv,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.horizontal_cut_equiv,KingHorizontal.horizontal_sum,KingHorizontal.horizontal_three_rows,KingHorizontal.horizontal_two_columns,KingHorizontal.horizontal_two_rows,KingHorizontal.interior_count,KingHorizontal.interior_count_alphabets,KingHorizontal.interior_count_support,KingHorizontal.interior_one_column_count,KingHorizontal.interior_row_sum,KingHorizontal.interior_slot_equiv,KingHorizontal.interior_three_rows_count,KingHorizontal.raw_of_halves,KingHorizontal.row_reflect_equiv,KingHorizontal.row_reflect_raw,KingHorizontal.top_edge,KingHorizontal.top_edge_value,KingHorizontal.top_field_raw,KingPath.edge_path,KingPath.oneDefect_path
lo: proof_shape=bind-only; reuse=D5.S3.Topology.QuandleMarkovColoring.leftSlot; consumers=KingGrid.blockEdges,KingGrid.corner,KingGrid.end0,KingGrid.end1,KingGrid.goodBlock_surjective,KingGrid.oneDefect_surjective,KingGrid.oneDefect_usesThree,KingGrid.reflect_mono,KingGrid.rev_hi,KingGrid.rev_lo,KingGrid.transpose_mono,KingPath.bad,KingPath.bad_map,KingPath.errors_eq,KingPath.fixed_words
hi: proof_shape=bind-only; reuse=D5.S3.Topology.QuandleMarkovColoring.rightSlot; consumers=KingGrid.blockEdges,KingGrid.corner,KingGrid.end0,KingGrid.end1,KingGrid.goodBlock_surjective,KingGrid.oneDefect_surjective,KingGrid.oneDefect_usesThree,KingGrid.reflect_mono,KingGrid.rev_hi,KingGrid.rev_lo,KingGrid.transpose_mono,KingPath.bad,KingPath.bad_map,KingPath.errors_eq,KingPath.fixed_words
end0: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingDifference.differentiate_edgeValue,KingDifference.raw_differentiate_iff,KingDifference.relabelDefectEquiv,KingGrid.OneDefect,KingGrid.endpoints_distinct,KingGrid.labelled_eq_twentyFour,KingGrid.mono,KingGrid.oneDefect_iff,KingGrid.reflect_mono,KingPath.oneDefect_path
end1: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingDifference.differentiate_edgeValue,KingDifference.raw_differentiate_iff,KingDifference.relabelDefectEquiv,KingGrid.OneDefect,KingGrid.endpoints_distinct,KingGrid.labelled_eq_twentyFour,KingGrid.mono,KingGrid.oneDefect_iff,KingGrid.reflect_mono,KingPath.oneDefect_path
mono: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.transpose_one,KingDifference.relabelDefectEquiv,KingGrid.DefectAt,KingGrid.OneDefect,KingGrid.defectAt_iff,KingGrid.defectEquiv,KingGrid.goodBlock_surjective,KingGrid.labelled_eq_twentyFour,KingGrid.oneDefect_iff,KingGrid.oneDefect_surjective,KingGrid.oneDefect_usesThree,KingGrid.reflectDefectEquiv,KingGrid.reflect_mono,KingGrid.transposeDefectEquiv,KingGrid.transpose_mono,KingPath.oneDefect_path
OneDefect: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.canonical_transpose_twice,KingClosedForm.symmetry,KingClosedForm.transpose_one,KingGrid.L,KingGrid.T,KingGrid.count_by_edge,KingGrid.defectAt_iff,KingGrid.defectEquiv,KingGrid.labelled_count,KingGrid.labelled_eq_twentyFour,KingGrid.oneDefect_iff,KingGrid.oneDefect_surjective,KingGrid.oneDefect_usesThree,KingPath.literal_count,KingPath.literal_words,KingPath.oneDefect_path
DefectAt: proof_shape=bind-only; consumers=KingDifference.N_reflect,KingDifference.N_transpose,KingDifference.count_fixed_edge,KingDifference.count_from_fields,KingDifference.defectIntegrationEquiv,KingDifference.raw_differentiate_iff,KingDifference.relabelDefectEquiv,KingGrid.count_by_edge,KingGrid.defectAt_iff,KingGrid.defectEquiv,KingGrid.reflectDefectEquiv,KingGrid.transposeDefectEquiv,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_raw
normal: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.canonical_transpose_twice,KingClosedForm.normal_exists_unique,KingClosedForm.normal_unique,KingClosedForm.normalize,KingClosedForm.normalize_spec,KingClosedForm.symmetry,KingGrid.T,KingGrid.labelled_eq_twentyFour,KingPath.literal_count,KingPath.literal_words,KingPath.normal_path
L: proof_shape=bind-only; consumers=KingDifference.count_from_fields,KingDifference.fields_eq_six_canonical,KingGrid.count_by_edge,KingGrid.labelled_count,KingGrid.labelled_eq_twentyFour
T: proof_shape=bind-only; consumers=HardinA229571.result,HardinA229573.result,HardinA229574.result,HardinA229575.result,HardinA229576.result,HardinA229577.result,HardinA229578.result,KingClosedForm.closed_form,KingClosedForm.diagonal_closed,KingClosedForm.symmetry,KingClosedForm.width_three,KingClosedForm.width_two,KingDifference.count_by_kind,KingDifference.fields_eq_six_canonical,KingGrid.labelled_eq_twentyFour,KingPath.literal_count,KingPath.width_one_large
oneDefect_iff: proof_shape=bind-only; consumers=KingClosedForm.transpose_one,KingGrid.defectAt_iff,KingGrid.defectEquiv,KingGrid.oneDefect_surjective,KingGrid.oneDefect_usesThree
defectAt_iff: proof_shape=bind-only; consumers=KingGrid.defectEquiv
defectEquiv: proof_shape=bind-only; consumers=KingGrid.count_by_edge
labelled_count: proof_shape=bind-only; consumers=KingGrid.count_by_edge,KingGrid.labelled_eq_twentyFour
count_by_edge: proof_shape=bind-only; consumers=KingDifference.count_from_fields
edgeSumEquiv: proof_shape=bind-only; consumers=KingGrid.sum_edges
sum_edges: proof_shape=bind-only; consumers=KingDifference.sum_fields_by_kind
transposeEdge: proof_shape=bind-only; consumers=KingClosedForm.transpose_one,KingDifference.N_transpose,KingDifference.sum_fields_by_kind,KingGrid.transposeDefectEquiv,KingGrid.transpose_mono,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_raw
transpose: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.canonical_transpose_twice,KingClosedForm.transpose_one,KingGrid.transposeDefectEquiv,KingGrid.transpose_mono
transpose_mono: proof_shape=bind-only; consumers=KingClosedForm.transpose_one,KingGrid.transposeDefectEquiv
transposeDefectEquiv: proof_shape=bind-only; consumers=KingDifference.N_transpose,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_raw
endpoints_distinct: proof_shape=bind-only; reuse=D5.S3.Topology.QuandleMarkovColoring.slots_ne; consumers=KingGrid.oneDefect_usesThree
reflectEdge: proof_shape=bind-only; consumers=KingDifference.N_reflect,KingGrid.reflectDefectEquiv,KingGrid.reflect_mono,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_raw
reflect: proof_shape=bind-only; consumers=KingGrid.reflectDefectEquiv,KingGrid.reflect_mono
rev_lo: proof_shape=bind-only; consumers=KingGrid.reflect_mono
rev_hi: proof_shape=bind-only; consumers=KingGrid.reflect_mono
reflect_mono: proof_shape=bind-only; consumers=KingGrid.reflectDefectEquiv
reflectDefectEquiv: proof_shape=bind-only; consumers=KingDifference.N_reflect,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_raw
UsesThree: proof_shape=bind-only; consumers=KingGrid.perm_ext_three
perm_ext_three: proof_shape=bind-only; consumers=KingGrid.canonical_count_three
canonical_count_three: proof_shape=bind-only; consumers=KingTwoGrid.labelled_eq_twentyFour
oneDefect_usesThree: proof_shape=bind-only; consumers=KingGrid.labelled_eq_twentyFour
blockEdges: proof_shape=bind-only; consumers=KingGrid.goodBlock_surjective,KingGrid.oneDefect_surjective
corner: proof_shape=bind-only; consumers=KingGrid.goodBlock_surjective
goodBlock_surjective: proof_shape=bind-only; consumers=KingGrid.oneDefect_surjective
oneDefect_surjective: proof_shape=bind-only; consumers=KingGrid.labelled_eq_twentyFour
labelled_eq_twentyFour: proof_shape=bind-only; consumers=KingDifference.fields_eq_six_canonical
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Topology.QuandleMarkovColoring
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Prod
import Mathlib.GroupTheory.Perm.Support

/-! Literal edges, restricted-growth words and their finite families. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid

abbrev Cell (n k : ℕ) := Fin n × Fin k

inductive Edge (n k : ℕ)
  | H (i : Fin n) (j : Fin (k - 1))
  | V (i : Fin (n - 1)) (j : Fin k)
  | D (i : Fin (n - 1)) (j : Fin (k - 1))
  | A (i : Fin (n - 1)) (j : Fin (k - 1))
  deriving DecidableEq, Fintype

def lo {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  D5.S3.Topology.QuandleMarkovColoring.leftSlot i
def hi {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  D5.S3.Topology.QuandleMarkovColoring.rightSlot i

def end0 {n k : ℕ} : Edge n k → Cell n k
  | .H i j => (i, lo j)
  | .V i j => (lo i, j)
  | .D i j => (lo i, lo j)
  | .A i j => (lo i, hi j)

def end1 {n k : ℕ} : Edge n k → Cell n k
  | .H i j => (i, hi j)
  | .V i j => (hi i, j)
  | .D i j => (hi i, hi j)
  | .A i j => (hi i, lo j)

abbrev mono {n k : ℕ} {C : Type*} (f : Cell n k → C) (e : Edge n k) : Prop :=
  f (end0 e) = f (end1 e)

def OneDefect {n k : ℕ} {C : Type*} [DecidableEq C] (f : Cell n k → C) : Prop :=
  (Finset.univ.filter (mono f)).card = 1

def DefectAt {n k : ℕ} {C : Type*} (e : Edge n k) (f : Cell n k → C) : Prop :=
  ∀ d, mono f d ↔ d = e

/-- The order on the flattened word is precisely row-major order. -/
def normal {n k : ℕ} (f : Cell n k → Fin 4) : Prop :=
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
    (fun i : Fin (n * k) => f (finProdFinEquiv.symm i))

noncomputable def L (n k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : Cell n k → Fin 4 => OneDefect f)).card

noncomputable def T (n k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : Cell n k → Fin 4 => OneDefect f ∧ normal f)).card

theorem oneDefect_iff {n k : ℕ} {C : Type*} [DecidableEq C] (f : Cell n k → C) :
    OneDefect f ↔ ∃! e, mono f e := by
  simp [OneDefect, Finset.card_eq_one_iff_existsUnique]

private theorem defectAt_iff {n k : ℕ} {C : Type*} [DecidableEq C]
    (e : Edge n k) (f : Cell n k → C) :
    DefectAt e f ↔ OneDefect f ∧ mono f e := by
  rw [oneDefect_iff]
  constructor
  · intro h
    exact ⟨⟨e, (h e).mpr rfl, fun d hd => (h d).mp hd⟩, (h e).mpr rfl⟩
  · rintro ⟨⟨d, hd, hu⟩, he⟩ a
    exact ⟨fun ha => (hu a ha).trans (hu e he).symm, fun ha => ha ▸ he⟩

private noncomputable def defectEquiv {n k : ℕ} {C : Type*} [DecidableEq C] :
    {f : Cell n k → C // OneDefect f} ≃ Σ e : Edge n k, {f : Cell n k → C // DefectAt e f} := by
  let pick (f : {f : Cell n k → C // OneDefect f}) :=
    Classical.choose ((oneDefect_iff f.val).mp f.property)
  refine (Equiv.sigmaFiberEquiv pick).symm.trans (Equiv.sigmaCongrRight fun e => ?_)
  let E : {f : {f : Cell n k → C // OneDefect f} // pick f = e} ≃
      {f : {f : Cell n k → C // OneDefect f} // mono f.val e} :=
    Equiv.subtypeEquivRight (by
      intro f
      constructor
      · intro h
        rw [← h]
        exact (Classical.choose_spec ((oneDefect_iff f.val).mp f.property)).1
      · intro h
        exact ((Classical.choose_spec ((oneDefect_iff f.val).mp f.property)).2 e h).symm)
  exact E.trans ((Equiv.subtypeSubtypeEquivSubtypeInter (fun f => OneDefect f)
    (fun f => mono f e)).trans
      (Equiv.subtypeEquivRight (fun f => (defectAt_iff e f).symm)))

private theorem labelled_count {n k : ℕ} : L n k = Nat.card {f : Cell n k → Fin 4 // OneDefect f} := by
  classical
  simp [L, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem count_by_edge (n k : ℕ) :
    L n k = ∑ e : Edge n k, Nat.card {f : Cell n k → Fin 4 // DefectAt e f} := by
  classical
  rw [labelled_count, Nat.card_congr (defectEquiv (n := n) (k := k))]
  simp [Nat.card_eq_fintype_card, Fintype.card_sigma]


private def edgeSumEquiv (n k : ℕ) : Edge n k ≃
    (Fin n × Fin (k - 1)) ⊕ (Fin (n - 1) × Fin k) ⊕
      (Fin (n - 1) × Fin (k - 1)) ⊕ (Fin (n - 1) × Fin (k - 1)) where
  toFun
    | .H i j => .inl (i,j)
    | .V i j => .inr (.inl (i,j))
    | .D i j => .inr (.inr (.inl (i,j)))
    | .A i j => .inr (.inr (.inr (i,j)))
  invFun
    | .inl (i,j) => .H i j
    | .inr (.inl (i,j)) => .V i j
    | .inr (.inr (.inl (i,j))) => .D i j
    | .inr (.inr (.inr (i,j))) => .A i j
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with _ | (_ | (_ | _)) <;> rfl

theorem sum_edges {n k : ℕ} (F : Edge n k → ℕ) :
    (∑ e, F e) =
      (∑ i : Fin n, ∑ j : Fin (k - 1), F (.H i j)) +
      (∑ i : Fin (n - 1), ∑ j : Fin k, F (.V i j)) +
      (∑ i : Fin (n - 1), ∑ j : Fin (k - 1), F (.D i j)) +
      (∑ i : Fin (n - 1), ∑ j : Fin (k - 1), F (.A i j)) := by
  rw [← (edgeSumEquiv n k).symm.sum_comp F]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, edgeSumEquiv, add_assoc]

/-- Transpose acts on edge types as H↔V, fixing the two diagonal types. -/
def transposeEdge {n k : ℕ} : Edge n k ≃ Edge k n where
  toFun
    | .H i j => .V j i
    | .V i j => .H j i
    | .D i j => .D j i
    | .A i j => .A j i
  invFun
    | .H i j => .V j i
    | .V i j => .H j i
    | .D i j => .D j i
    | .A i j => .A j i
  left_inv e := by cases e <;> rfl
  right_inv e := by cases e <;> rfl

def transpose {n k : ℕ} {C : Type*} (f : Cell n k → C) : Cell k n → C :=
  fun p => f (p.2,p.1)

theorem transpose_mono {n k : ℕ} {C : Type*} (f : Cell n k → C) (e : Edge n k) :
    mono (transpose f) (transposeEdge e) ↔ mono f e := by
  cases e <;> simp [mono, transpose, transposeEdge, end0, end1, eq_comm]

def transposeDefectEquiv {n k : ℕ} {C : Type*} (e : Edge n k) :
    {f : Cell n k → C // DefectAt e f} ≃
      {f : Cell k n → C // DefectAt (transposeEdge e) f} :=
  (Equiv.arrowCongr (Equiv.prodComm (Fin n) (Fin k)) (Equiv.refl C)).subtypeEquiv (by
    intro f
    change DefectAt e f ↔ DefectAt (transposeEdge e) (transpose f)
    constructor
    · intro hf d
      obtain ⟨a,rfl⟩ := transposeEdge.surjective d
      rw [transpose_mono, hf, transposeEdge.injective.eq_iff]
    · intro hf d
      have h := hf (transposeEdge d)
      rw [transpose_mono, transposeEdge.injective.eq_iff] at h
      exact h)

private theorem endpoints_distinct {n k : ℕ} (e : Edge n k) : end0 e ≠ end1 e := by
  cases e with
  | H i j =>
    intro h
    exact D5.S3.Topology.QuandleMarkovColoring.slots_ne (n := k) j (congrArg Prod.snd h)
  | V i j =>
    intro h
    exact D5.S3.Topology.QuandleMarkovColoring.slots_ne (n := n) i (congrArg Prod.fst h)
  | D i j =>
    intro h
    exact D5.S3.Topology.QuandleMarkovColoring.slots_ne (n := n) i (congrArg Prod.fst h)
  | A i j =>
    intro h
    exact D5.S3.Topology.QuandleMarkovColoring.slots_ne (n := n) i (congrArg Prod.fst h)

/-- Reflection reverses H endpoints and exchanges D with A. -/
def reflectEdge {n k : ℕ} : Edge n k ≃ Edge n k where
  toFun
    | .H i j => .H i j.rev
    | .V i j => .V i j.rev
    | .D i j => .A i j.rev
    | .A i j => .D i j.rev
  invFun
    | .H i j => .H i j.rev
    | .V i j => .V i j.rev
    | .D i j => .A i j.rev
    | .A i j => .D i j.rev
  left_inv e := by cases e <;> simp
  right_inv e := by cases e <;> simp

private def reflect {n k : ℕ} {C : Type*} (f : Cell n k → C) : Cell n k → C :=
  fun p => f (p.1,p.2.rev)

private theorem rev_lo {n : ℕ} (i : Fin (n - 1)) : (lo i).rev = hi i.rev := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact Fin.rev_castSucc i

private theorem rev_hi {n : ℕ} (i : Fin (n - 1)) : (hi i).rev = lo i.rev := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact Fin.rev_succ i

private theorem reflect_mono {n k : ℕ} {C : Type*} (f : Cell n k → C) (e : Edge n k) :
    mono (reflect f) (reflectEdge e) ↔ mono f e := by
  cases e <;> simp [mono, reflect, reflectEdge, end0, end1, rev_lo, rev_hi, eq_comm]

def reflectDefectEquiv {n k : ℕ} {C : Type*} (e : Edge n k) :
    {f : Cell n k → C // DefectAt e f} ≃
      {f : Cell n k → C // DefectAt (reflectEdge e) f} :=
  (Equiv.arrowCongr (Equiv.prodCongr (Equiv.refl (Fin n)) Fin.revPerm)
    (Equiv.refl C)).subtypeEquiv (by
    intro f
    change DefectAt e f ↔ DefectAt (reflectEdge e) (reflect f)
    constructor
    · intro hf d
      obtain ⟨a,rfl⟩ := reflectEdge.surjective d
      rw [reflect_mono, hf, reflectEdge.injective.eq_iff]
    · intro hf d
      have h := hf (reflectEdge d)
      rw [reflect_mono, reflectEdge.injective.eq_iff] at h
      exact h)

def UsesThree {X : Type*} (f : X → Fin 4) : Prop :=
  ∃ a b c, f a ≠ f b ∧ f a ≠ f c ∧ f b ≠ f c

private theorem perm_ext_three {X : Type*} (f : X → Fin 4) (hf : UsesThree f)
    (p q : Equiv.Perm (Fin 4)) (h : p ∘ f = q ∘ f) : p = q := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc⟩ := hf
  have fixed (t : X) : (q⁻¹ * p) (f t) = f t := by
    change q.symm (p (f t)) = f t
    have ht : p (f t) = q (f t) := congrFun h t
    rw [ht, q.symm_apply_apply]
  have hs : ({f a, f b, f c} : Finset (Fin 4)) ⊆
      Finset.univ.filter (fun x => (q⁻¹ * p) x = x) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fixed a⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fixed b⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fixed c⟩
  have hc : 3 ≤ (Finset.univ.filter (fun x => (q⁻¹ * p) x = x)).card := by
    calc
      3 = ({f a, f b, f c} : Finset (Fin 4)).card := by simp [hab,hac,hbc]
      _ ≤ _ := Finset.card_le_card hs
  have he : q⁻¹ * p = 1 := by
    by_contra hn
    have hh := Equiv.Perm.fixed_point_card_lt_of_ne_one hn
    norm_num only [Fintype.card_fin] at hh
    omega
  exact (inv_mul_eq_one.mp he).symm

theorem canonical_count_three {X : Type*} [Finite X] [LinearOrder X]
    (S : (X → Fin 4) → Prop)
    (hinv : ∀ p : Equiv.Perm (Fin 4), ∀ f, S (p ∘ f) ↔ S f)
    (hthree : ∀ f, S f → UsesThree f) :
    Nat.card {f // S f} = 24 * Nat.card {f // S f ∧
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical f} := by
  classical
  let _ := Fintype.ofFinite X
  let E : ({f // S f ∧
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical f} ×
      Equiv.Perm (Fin 4)) → {f // S f} :=
    fun q => ⟨q.2 ∘ q.1.val, (hinv q.2 q.1.val).mpr q.1.property.1⟩
  have hE : Function.Bijective E := by
    constructor
    · rintro ⟨Q,p⟩ ⟨R,q⟩ h
      have he : p ∘ Q.val = q ∘ R.val := congrArg Subtype.val h
      obtain ⟨U, hU, hu⟩ :=
        D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.canonical_exists_unique
          (p ∘ Q.val)
      have hQ : Q.val = U := hu _ ⟨Q.property.2,p.symm, by ext i; simp⟩
      have hR : R.val = U := hu _ ⟨R.property.2,q.symm, by rw [he]; ext i; simp⟩
      have hs : Q = R := Subtype.ext (hQ.trans hR.symm)
      subst R
      exact Prod.ext rfl (perm_ext_three Q.val (hthree _ Q.property.1) p q he)
    · intro P
      obtain ⟨Q,⟨hQ,p,hp⟩,_⟩ :=
        D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.canonical_exists_unique P.val
      have hS : S Q := hp ▸ (hinv p P.val).mpr P.property
      refine ⟨(⟨Q,hS,hQ⟩,p.symm), ?_⟩
      apply Subtype.ext
      funext i
      change p.symm (Q i) = P.val i
      rw [hp]
      exact p.symm_apply_apply _
  have hc := Nat.card_congr (Equiv.ofBijective E hE)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 4)),
    Fintype.card_perm, Fintype.card_fin] at hc
  norm_num at hc
  simpa only [Nat.mul_comm, Nat.card_eq_fintype_card] using hc.symm

private theorem oneDefect_usesThree {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k)
    (f : Cell n k → Fin 4) (hf : OneDefect f) : UsesThree f := by
  let r0 : Fin n := ⟨0,by omega⟩
  let r1 : Fin n := ⟨1,by omega⟩
  let c0 : Fin k := ⟨0,by omega⟩
  let c1 : Fin k := ⟨1,by omega⟩
  let ri : Fin (n - 1) := ⟨0,by omega⟩
  let ci : Fin (k - 1) := ⟨0,by omega⟩
  obtain ⟨e,he,hu⟩ := (oneDefect_iff f).mp hf
  have unique {d a : Edge n k} (hd : mono f d) (ha : mono f a) : d = a :=
    (hu d hd).trans (hu a ha).symm
  by_cases hab : f (r0,c0) = f (r0,c1)
  · have htop : mono f (.H r0 ci) := hab
    refine ⟨(r0,c0),(r1,c0),(r1,c1),?_,?_,?_⟩
    · intro h
      have heq := unique htop (show mono f (.V ri c0) from h)
      cases heq
    · intro h
      have heq := unique htop (show mono f (.D ri ci) from h)
      cases heq
    · intro h
      have heq := unique htop (show mono f (.H r1 ci) from h)
      exact endpoints_distinct (.V ri c0)
        (congrArg (fun r => (r,c0)) (Edge.H.inj heq).1)
  by_cases hac : f (r0,c0) = f (r1,c0)
  · have hleft : mono f (.V ri c0) := hac
    refine ⟨(r0,c0),(r0,c1),(r1,c1),hab,?_,?_⟩
    · intro h
      have heq := unique hleft (show mono f (.D ri ci) from h)
      cases heq
    · intro h
      have heq := unique hleft (show mono f (.V ri c1) from h)
      exact endpoints_distinct (.H r0 ci)
        (congrArg (fun c => (r0,c)) (Edge.V.inj heq).2)
  by_cases hbc : f (r0,c1) = f (r1,c0)
  · have hanti : mono f (.A ri ci) := hbc
    refine ⟨(r0,c0),(r0,c1),(r1,c1),hab,?_,?_⟩
    · intro h
      have heq := unique hanti (show mono f (.D ri ci) from h)
      cases heq
    · intro h
      have heq := unique hanti (show mono f (.V ri c1) from h)
      cases heq
  exact ⟨(r0,c0),(r0,c1),(r1,c0),hab,hac,hbc⟩


private def blockEdges {n k : ℕ} (i : Fin (n - 1)) (j : Fin (k - 1)) : Finset (Edge n k) :=
  {.H (lo i) j, .H (hi i) j, .V i (lo j), .V i (hi j), .D i j, .A i j}

private def corner {n k : ℕ} (i : Fin (n - 1)) (j : Fin (k - 1)) : Fin 4 → Cell n k :=
  ![(lo i,lo j), (lo i,hi j), (hi i,lo j), (hi i,hi j)]

private theorem goodBlock_surjective {n k : ℕ} (f : Cell n k → Fin 4)
    (i : Fin (n - 1)) (j : Fin (k - 1))
    (hg : ∀ d ∈ blockEdges i j, ¬ mono f d) : Function.Surjective f := by
  have hht := hg (.H (lo i) j) (by simp [blockEdges])
  have hhb := hg (.H (hi i) j) (by simp [blockEdges])
  have hvl := hg (.V i (lo j)) (by simp [blockEdges])
  have hvr := hg (.V i (hi j)) (by simp [blockEdges])
  have hd := hg (.D i j) (by simp [blockEdges])
  have ha := hg (.A i j) (by simp [blockEdges])
  have hinj : Function.Injective (fun a : Fin 4 => f (corner i j a)) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [corner, mono, end0, end1, eq_comm]
  intro c
  obtain ⟨a,ha⟩ := Finite.surjective_of_injective hinj c
  exact ⟨corner i j a,ha⟩

private theorem oneDefect_surjective {n k : ℕ} (hn : 3 ≤ n) (hk : 3 ≤ k)
    (f : Cell n k → Fin 4) (hf : OneDefect f) : Function.Surjective f := by
  let i0 : Fin (n - 1) := ⟨0,by omega⟩
  let i1 : Fin (n - 1) := ⟨1,by omega⟩
  let j0 : Fin (k - 1) := ⟨0,by omega⟩
  let j1 : Fin (k - 1) := ⟨1,by omega⟩
  have hdis : Disjoint (blockEdges i0 j0) (blockEdges i1 j1) := by
    norm_num [blockEdges, i0, i1, j0, j1, Finset.disjoint_left,
      lo, hi, Fin.ext_iff]
  obtain ⟨e,he,hu⟩ := (oneDefect_iff f).mp hf
  by_cases hm : e ∈ blockEdges i0 j0
  · apply goodBlock_surjective f i1 j1
    intro d hd hmono
    have hed := hu d hmono
    exact (Finset.disjoint_left.mp hdis hm) (hed ▸ hd)
  · apply goodBlock_surjective f i0 j0
    intro d hd hmono
    have hed := hu d hmono
    exact hm (hed ▸ hd)

/-- Three occurring colours already make the four-colour permutation action free. -/
theorem labelled_eq_twentyFour (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    L n k = 24 * T n k := by
  classical
  let word (f : Fin (n * k) → Fin 4) : Cell n k → Fin 4 := fun p => f (finProdFinEquiv p)
  let S (f : Fin (n * k) → Fin 4) := OneDefect (word f)
  have hinv : ∀ p : Equiv.Perm (Fin 4), ∀ f, S (p ∘ f) ↔ S f := by
    intro p f
    simp only [S, word, OneDefect, mono, Function.comp_apply, p.injective.eq_iff]
  have huse : ∀ f, S f → UsesThree f := by
    intro f hf
    obtain ⟨a,b,c,hab,hac,hbc⟩ := oneDefect_usesThree hn hk (word f) hf
    exact ⟨finProdFinEquiv a,finProdFinEquiv b,finProdFinEquiv c,hab,hac,hbc⟩
  have h : Nat.card {f // S f} = 24 * Nat.card {f // S f ∧
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical f} := by
    by_cases hbig : 3 ≤ n ∧ 3 ≤ k
    · apply D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.canonical_pattern_card4
        S hinv
      intro f hf c
      obtain ⟨p,hp⟩ := oneDefect_surjective hbig.1 hbig.2 (word f) hf c
      exact ⟨finProdFinEquiv p,hp⟩
    · exact canonical_count_three S hinv huse
  let E : (Cell n k → Fin 4) ≃ (Fin (n * k) → Fin 4) :=
    Equiv.arrowCongr finProdFinEquiv (Equiv.refl _)
  have hL : L n k = Nat.card {f // S f} := by
    rw [labelled_count]
    exact Nat.card_congr (E.subtypeEquiv (by intro f; simp [E,S,word,OneDefect]))
  have hT : T n k = Nat.card {f // S f ∧
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical f} := by
    rw [show T n k = Nat.card {f : Cell n k → Fin 4 // OneDefect f ∧ normal f} by
      simp [T,Nat.card_eq_fintype_card,Fintype.card_subtype]]
    exact Nat.card_congr (E.subtypeEquiv (by
      intro f
      have he : word (E f) = f := by
        funext p
        exact congrArg f (finProdFinEquiv.symm_apply_apply p)
      change (OneDefect f ∧ normal f) ↔ (OneDefect (word (E f)) ∧ normal f)
      rw [he]))
  rw [hL,hT]
  exact h

#print axioms labelled_eq_twentyFour

end D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
