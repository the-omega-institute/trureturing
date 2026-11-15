/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingGrid
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Literal king-grid colourings and decomposition by the unique defective edge. -/
/-
admission_basis: escape-witness
escape_witness: canonical_count_three (the free four-colour action with only
  three occurring colours), oneDefect_usesThree and oneDefect_surjective
  (the local and global colour constraints imposed by a unique king-edge defect).
Cell: proof_shape=bind-only; consumers=DefectAt,KingClosedForm.canonical_transpose,KingClosedForm.canonical_transpose_twice,KingClosedForm.normal_exists_unique,KingClosedForm.normal_unique,KingClosedForm.normalize,KingClosedForm.normalize_spec,KingClosedForm.symmetry,KingClosedForm.transpose_one,KingDifference.count_fixed_edge,KingDifference.defectIntegrationEquiv,KingDifference.difference_unique,KingDifference.differentiate,KingDifference.differentiate_cocycle,KingDifference.differentiate_edgeValue,KingDifference.good_differentiate,KingDifference.integrate,KingDifference.integrate_differentiate,KingDifference.integrationEquiv,KingDifference.rainbow_block,KingDifference.raw_differentiate_iff,KingDifference.relabelDefectEquiv,KingDifference.rootZeroEquiv,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_differentiate,KingPath.literal_count,KingPath.literal_words,KingPath.normal_path,KingPath.oneDefect_path,L,OneDefect,T,corner,count_by_edge,defectAt_iff,defectEquiv,end0,end1,goodBlock_surjective,labelled_count,labelled_eq_twentyFour,mono,normal,oneDefect_iff,oneDefect_surjective,oneDefect_usesThree,reflect,reflectDefectEquiv,reflect_mono,transpose,transposeDefectEquiv,transpose_mono
Edge: proof_shape=bind-only; consumers=DefectAt,KingDiagonal.N_D_two_columns,KingDiagonal.N_D_two_rows,KingDiagonal.diagonalSlotEquiv,KingDiagonal.diagonal_clear,KingDiagonal.diagonal_count,KingDiagonal.extract_valid,KingDiagonal.raw_h_ordinary,KingDiagonal.raw_h_special,KingDiagonal.raw_v_ordinary,KingDiagonal.raw_v_special,KingDiagonal.slot_raw,KingDiagonal.slot_reconstruction,KingDiagonal.special_block,KingDifference.BlockAvoids,KingDifference.N_D,KingDifference.N_H,KingDifference.N_e,KingDifference.N_reflect,KingDifference.N_transpose,KingDifference.RawAdmissible,KingDifference.count_fixed_edge,KingDifference.count_from_fields,KingDifference.defectIntegrationEquiv,KingDifference.differentiate_edgeValue,KingDifference.edgeValue,KingDifference.fields_eq_six_canonical,KingDifference.goodBlock_of_raw,KingDifference.horizontal_slot_eq,KingDifference.raw_differentiate_iff,KingDifference.relabelDefectEquiv,KingDifference.rootZeroEquiv,KingDifference.sum_fields_by_kind,KingDifference.vertical_slot_eq,KingHorizontal.CutFields,KingHorizontal.bottom_edge,KingHorizontal.bottom_edge_value,KingHorizontal.bottom_field_raw,KingHorizontal.boundary_bottom_shared,KingHorizontal.boundary_bottom_slot_equiv,KingHorizontal.boundary_build_raw,KingHorizontal.boundary_count,KingHorizontal.boundary_count_at,KingHorizontal.boundary_count_pos,KingHorizontal.boundary_count_zero,KingHorizontal.boundary_extract_valid,KingHorizontal.boundary_h,KingHorizontal.boundary_one_column,KingHorizontal.boundary_reconstruct,KingHorizontal.boundary_row_sum,KingHorizontal.boundary_rows_count,KingHorizontal.boundary_slot_equiv,KingHorizontal.boundary_top_shared,KingHorizontal.boundary_v,KingHorizontal.boundary_word_equiv,KingHorizontal.cut_slots_equiv,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.horizontal_cut_equiv,KingHorizontal.horizontal_sum,KingHorizontal.horizontal_three_rows,KingHorizontal.horizontal_two_columns,KingHorizontal.horizontal_two_rows,KingHorizontal.interior_count,KingHorizontal.interior_count_alphabets,KingHorizontal.interior_count_support,KingHorizontal.interior_one_column_count,KingHorizontal.interior_row_sum,KingHorizontal.interior_slot_equiv,KingHorizontal.interior_three_rows_count,KingHorizontal.raw_of_halves,KingHorizontal.row_reflect_equiv,KingHorizontal.row_reflect_raw,KingHorizontal.top_edge,KingHorizontal.top_edge_value,KingHorizontal.top_field_raw,KingPath.edge_path,blockEdges,count_by_edge,defectAt_iff,defectEquiv,edgeSumEquiv,end0,end1,endpoints_distinct,goodBlock_surjective,mono,oneDefect_usesThree,reflectDefectEquiv,reflectEdge,reflect_mono,sum_edges,transposeDefectEquiv,transposeEdge,transpose_mono
lo: proof_shape=bind-only; consumers=KingPath.bad,blockEdges,corner,end0,end1,endpoints_distinct,goodBlock_surjective,oneDefect_surjective,rev_hi,rev_lo
hi: proof_shape=bind-only; consumers=KingPath.bad,blockEdges,corner,end0,end1,endpoints_distinct,goodBlock_surjective,oneDefect_surjective,rev_hi,rev_lo
end0: proof_shape=bind-only; consumers=KingDifference.differentiate_edgeValue,endpoints_distinct,goodBlock_surjective,mono,reflect_mono,transpose_mono
end1: proof_shape=bind-only; consumers=KingDifference.differentiate_edgeValue,endpoints_distinct,goodBlock_surjective,mono,reflect_mono,transpose_mono
mono: proof_shape=bind-only; consumers=DefectAt,KingClosedForm.canonical_transpose,KingDifference.raw_differentiate_iff,KingDifference.relabelDefectEquiv,KingPath.oneDefect_path,OneDefect,defectAt_iff,goodBlock_surjective,labelled_eq_twentyFour,oneDefect_iff,oneDefect_usesThree,reflect_mono,transpose_mono
OneDefect: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.canonical_transpose_twice,KingClosedForm.symmetry,KingClosedForm.transpose_one,KingPath.literal_count,KingPath.literal_words,KingPath.oneDefect_path,L,T,defectAt_iff,defectEquiv,labelled_count,labelled_eq_twentyFour,oneDefect_iff,oneDefect_surjective,oneDefect_usesThree
DefectAt: proof_shape=bind-only; consumers=KingDifference.count_fixed_edge,KingDifference.defectIntegrationEquiv,KingDifference.raw_differentiate_iff,KingDifference.relabelDefectEquiv,KingDifference.rootZeroEquiv,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_raw,count_by_edge,defectAt_iff,defectEquiv,reflectDefectEquiv,transposeDefectEquiv
normal: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.canonical_transpose_twice,KingClosedForm.normal_exists_unique,KingClosedForm.normal_unique,KingClosedForm.normalize_spec,KingClosedForm.symmetry,KingPath.literal_count,KingPath.literal_words,KingPath.normal_path,T,labelled_eq_twentyFour
L: proof_shape=bind-only; consumers=KingDifference.count_from_fields,count_by_edge,labelled_count,labelled_eq_twentyFour
T: proof_shape=bind-only; consumers=HardinA229571.result,HardinA229572.result,HardinA229573.result,HardinA229574.result,HardinA229575.result,HardinA229576.result,HardinA229577.result,HardinA229578.result,KingClosedForm.closed_form,KingClosedForm.diagonal_closed,KingClosedForm.symmetry,KingClosedForm.width_three,KingClosedForm.width_two,KingDifference.count_by_kind,KingDifference.fields_eq_six_canonical,KingPath.literal_count,KingPath.one_vertex,KingPath.two_vertices,KingPath.width_one,KingPath.width_one_large,labelled_eq_twentyFour
oneDefect_iff: proof_shape=bind-only; consumers=KingClosedForm.transpose_one,defectAt_iff,defectEquiv,oneDefect_surjective,oneDefect_usesThree
defectAt_iff: proof_shape=bind-only; consumers=defectEquiv
defectEquiv: proof_shape=bind-only; consumers=count_by_edge
labelled_count: proof_shape=bind-only; consumers=count_by_edge,labelled_eq_twentyFour
count_by_edge: proof_shape=bind-only; consumers=KingDifference.count_from_fields
edgeSumEquiv: proof_shape=bind-only; consumers=sum_edges
sum_edges: proof_shape=bind-only; consumers=KingDifference.sum_fields_by_kind
transposeEdge: proof_shape=bind-only; consumers=KingClosedForm.transpose_one,KingDifference.N_transpose,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_raw,transposeDefectEquiv,transpose_mono
transpose: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.canonical_transpose_twice,KingClosedForm.transpose_one,transposeDefectEquiv,transpose_mono
transpose_mono: proof_shape=bind-only; consumers=KingClosedForm.transpose_one,transposeDefectEquiv
transposeDefectEquiv: proof_shape=bind-only; consumers=KingDifference.N_transpose,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_raw
endpoints_distinct: proof_shape=bind-only; consumers=oneDefect_usesThree
reflectEdge: proof_shape=bind-only; consumers=KingDifference.N_reflect,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_raw,reflectDefectEquiv,reflect_mono
reflect: proof_shape=bind-only; consumers=reflectDefectEquiv,reflect_mono
rev_lo: proof_shape=bind-only; consumers=reflect_mono
rev_hi: proof_shape=bind-only; consumers=reflect_mono
reflect_mono: proof_shape=bind-only; consumers=reflectDefectEquiv
reflectDefectEquiv: proof_shape=bind-only; consumers=KingDifference.N_reflect,KingHorizontal.horizontal_count_row_reflect,KingHorizontal.row_reflect_raw
UsesThree: proof_shape=bind-only; consumers=canonical_count_three,labelled_eq_twentyFour,oneDefect_usesThree,perm_ext_three
perm_ext_three: proof_shape=bind-only; consumers=canonical_count_three
canonical_count_three: proof_shape=content; consumers=labelled_eq_twentyFour
oneDefect_usesThree: proof_shape=content; consumers=labelled_eq_twentyFour
blockEdges: proof_shape=bind-only; consumers=goodBlock_surjective,oneDefect_surjective
corner: proof_shape=bind-only; consumers=goodBlock_surjective
goodBlock_surjective: proof_shape=bind-only; consumers=oneDefect_surjective
oneDefect_surjective: proof_shape=content; consumers=labelled_eq_twentyFour
labelled_eq_twentyFour: proof_shape=content; consumers=KingDifference.fields_eq_six_canonical
The declarations describe finite families uniformly in both dimensions; no bounded
enumeration, checker, numerical reduction or certified instance is asserted.
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Prod

/-! Literal edges, restricted-growth words and their finite families. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid

abbrev Cell (n k : ℕ) := Fin n × Fin k

inductive Edge (n k : ℕ)
  | H (i : Fin n) (j : Fin (k - 1))
  | V (i : Fin (n - 1)) (j : Fin k)
  | D (i : Fin (n - 1)) (j : Fin (k - 1))
  | A (i : Fin (n - 1)) (j : Fin (k - 1))
  deriving DecidableEq, Fintype

def lo {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i.val, by omega⟩
def hi {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i.val + 1, by omega⟩

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
    {f : Cell n k → C // OneDefect f} ≃ Σ e : Edge n k, {f : Cell n k → C // DefectAt e f} where
  toFun f := by
    let e := Classical.choose ((oneDefect_iff f.val).mp f.property)
    have he := Classical.choose_spec ((oneDefect_iff f.val).mp f.property)
    exact ⟨e, f.val, (defectAt_iff e f.val).mpr ⟨f.property, he.1⟩⟩
  invFun q := ⟨q.2.val, ((defectAt_iff q.1 q.2.val).mp q.2.property).1⟩
  left_inv f := Subtype.ext rfl
  right_inv q := by
    apply Sigma.subtype_ext
    · exact (q.2.property _).mp
        (Classical.choose_spec ((oneDefect_iff q.2.val).mp
          ((defectAt_iff q.1 q.2.val).mp q.2.property).1)).1
    · rfl

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
  cases e <;> simp [end0, end1, lo, hi, Fin.ext_iff, Prod.mk.injEq]

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
  apply Fin.ext
  dsimp [lo, hi, Fin.rev]
  omega

private theorem rev_hi {n : ℕ} (i : Fin (n - 1)) : (hi i).rev = lo i.rev := by
  apply Fin.ext
  dsimp [lo, hi, Fin.rev]
  omega

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

private def UsesThree {X : Type*} (f : X → Fin 4) : Prop :=
  ∃ a b c, f a ≠ f b ∧ f a ≠ f c ∧ f b ≠ f c

private theorem perm_ext_three {X : Type*} (f : X → Fin 4) (hf : UsesThree f)
    (p q : Equiv.Perm (Fin 4)) (h : p ∘ f = q ∘ f) : p = q := by
  obtain ⟨a,b,c,hab,hac,hbc⟩ := hf
  have he (t : X) : p (f t) = q (f t) := congrFun h t
  apply Equiv.ext
  intro x
  by_cases ha : x = f a
  · simpa [ha] using he a
  by_cases hb : x = f b
  · simpa [hb] using he b
  by_cases hc : x = f c
  · simpa [hc] using he c
  by_contra hn
  have hcard : ({p (f a),p (f b),p (f c),p x,q x} : Finset (Fin 4)).card ≤ 4 := by
    simpa using (Finset.card_le_card
      (Finset.subset_univ ({p (f a),p (f b),p (f c),p x,q x} : Finset (Fin 4))))
  have hpa : p (f a) ≠ q x := by rw [he a]; exact q.injective.ne (Ne.symm ha)
  have hpb : p (f b) ≠ q x := by rw [he b]; exact q.injective.ne (Ne.symm hb)
  have hpc : p (f c) ≠ q x := by rw [he c]; exact q.injective.ne (Ne.symm hc)
  simp [Finset.card_insert_of_notMem, p.injective.ne hab, p.injective.ne hac,
    p.injective.ne hbc, p.injective.ne (Ne.symm ha), p.injective.ne (Ne.symm hb),
    p.injective.ne (Ne.symm hc), hpa, hpb, hpc, hn] at hcard

private theorem canonical_count_three {X : Type*} [Finite X] [LinearOrder X]
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
