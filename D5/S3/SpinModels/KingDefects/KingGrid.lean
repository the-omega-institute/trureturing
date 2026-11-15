/- GID: D5/S3/SpinModels/KingDefects/KingGrid
   generality: G
   mirror-B: D5/B/S3/SpinModels/KingDefects/KingGrid
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Literal king-grid colourings and decomposition by the unique defective edge. -/
/-
admission_basis: escape-witness
escape_witness: defectEquiv (extracting the unique defective edge).
The declarations describe finite families uniformly in both dimensions; no bounded
enumeration, checker, numerical reduction or certified instance is asserted.
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fin.Rev

namespace D5.S3.SpinModels.KingDefects.KingGrid

abbrev Cell (n k : ℕ) := Fin n × Fin k

inductive Edge (n k : ℕ)
  | H (i : Fin n) (j : Fin (k-1))
  | V (i : Fin (n-1)) (j : Fin k)
  | D (i : Fin (n-1)) (j : Fin (k-1))
  | A (i : Fin (n-1)) (j : Fin (k-1))
  deriving DecidableEq, Fintype

def lo {n : ℕ} (i : Fin (n-1)) : Fin n := ⟨i.val, by omega⟩
def hi {n : ℕ} (i : Fin (n-1)) : Fin n := ⟨i.val+1, by omega⟩

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

def mono {n k : ℕ} {C : Type*} (f : Cell n k → C) (e : Edge n k) : Prop :=
  f (end0 e) = f (end1 e)

def OneDefect {n k : ℕ} {C : Type*} [DecidableEq C] (f : Cell n k → C) : Prop :=
  (Finset.univ.filter (mono f)).card = 1

def DefectAt {n k : ℕ} {C : Type*} (e : Edge n k) (f : Cell n k → C) : Prop :=
  ∀ d, mono f d ↔ d = e

/-- The order on the flattened word is precisely row-major order. -/
def normal {n k : ℕ} (f : Cell n k → Fin 4) : Prop :=
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
    (fun i : Fin (n*k) => f (finProdFinEquiv.symm i))

noncomputable def L (n k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : Cell n k → Fin 4 => OneDefect f)).card

noncomputable def T (n k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : Cell n k → Fin 4 => OneDefect f ∧ normal f)).card

theorem oneDefect_iff {n k : ℕ} {C : Type*} [DecidableEq C] (f : Cell n k → C) :
    OneDefect f ↔ ∃! e, mono f e := by
  simp [OneDefect, Finset.card_eq_one_iff_existsUnique]

theorem defectAt_iff {n k : ℕ} {C : Type*} [DecidableEq C]
    (e : Edge n k) (f : Cell n k → C) :
    DefectAt e f ↔ OneDefect f ∧ mono f e := by
  rw [oneDefect_iff]
  constructor
  · intro h
    exact ⟨⟨e, (h e).mpr rfl, fun d hd => (h d).mp hd⟩, (h e).mpr rfl⟩
  · rintro ⟨⟨d, hd, hu⟩, he⟩ a
    exact ⟨fun ha => (hu a ha).trans (hu e he).symm, fun ha => ha ▸ he⟩

noncomputable def defectEquiv {n k : ℕ} {C : Type*} [DecidableEq C] :
    {f : Cell n k → C // OneDefect f} ≃ Σ e : Edge n k, {f // DefectAt e f} where
  toFun f := by
    let e := Classical.choose ((oneDefect_iff f.val).mp f.property)
    have he := Classical.choose_spec ((oneDefect_iff f.val).mp f.property)
    exact ⟨e, f.val, (defectAt_iff e f.val).mpr ⟨f.property, he.1⟩⟩
  invFun q := ⟨q.2.val, ((defectAt_iff q.1 q.2.val).mp q.2.property).1⟩
  left_inv f := Subtype.ext rfl
  right_inv q := by
    apply Sigma.ext
    · exact (q.2.property _).mp
        (Classical.choose_spec ((oneDefect_iff q.2.val).mp
          ((defectAt_iff q.1 q.2.val).mp q.2.property).1)).1
    · apply HEq_of_eq
      rfl

theorem labelled_count {n k : ℕ} : L n k = Nat.card {f : Cell n k → Fin 4 // OneDefect f} := by
  classical
  simp [L, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem count_by_edge (n k : ℕ) :
    L n k = ∑ e : Edge n k, Nat.card {f : Cell n k → Fin 4 // DefectAt e f} := by
  classical
  rw [labelled_count, Nat.card_congr (defectEquiv (n := n) (k := k))]
  simp [Nat.card_eq_fintype_card, Fintype.card_sigma]

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
      {f : Cell k n → C // DefectAt (transposeEdge e) f} where
  toFun f := ⟨transpose f.val, by
    intro d
    obtain ⟨a, rfl⟩ := transposeEdge.surjective d
    rw [transpose_mono, f.property, transposeEdge.injective.eq_iff]⟩
  invFun f := ⟨transpose f.val, by
    intro d
    have h := f.property (transposeEdge d)
    have he : transposeEdge (transposeEdge d) = d := by cases d <;> rfl
    rw [← transpose_mono f.val (transposeEdge d), he,
      transposeEdge.injective.eq_iff] at h
    exact h⟩
  left_inv f := Subtype.ext rfl
  right_inv f := Subtype.ext rfl

end D5.S3.SpinModels.KingDefects.KingGrid
