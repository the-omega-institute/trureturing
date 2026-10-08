/- GID: D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/QubitSupportCoefficientForms
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Composition]
   utility: kind=none
   digest: Ordered complementary two-row supports have one form per composition. -/

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.QubitSupportCoefficientForms

/-- Binary basis strings, ordered by their natural-number values. -/
abbrev BasisString (n : ℕ) := Fin (2 ^ n)

/-- A string has no nonzero bit outside the given qubit set. -/
def Supported {n : ℕ} (P : Finset (Fin n)) (x : BasisString n) : Prop :=
  ∀ i : Fin n, i ∉ P → x.val.testBit i.val = false

/-- The complementary row factor and increasing column factor, with no fixed qubit. -/
structure Config (n p : ℕ) where
  P : Finset (Fin n)
  nonempty : P.Nonempty
  x : BasisString n
  y : BasisString n
  x_supported : Supported P x
  y_bits : ∀ i : Fin n, y.val.testBit i.val =
    if i ∈ P then !(x.val.testBit i.val) else false
  first_zero : ∀ q ∈ P, (∀ i ∈ P, i ≤ q) → x.val.testBit q.val = false
  sigma : Fin p → BasisString n
  increasing : StrictMono sigma
  sigma_supported : ∀ j, Supported Pᶜ (sigma j)
  varying : ∀ i : Fin n, i ∉ P →
    (∃ j, (sigma j).val.testBit i.val = false) ∧
    (∃ j, (sigma j).val.testBit i.val = true)

/-- The occupied basis string at a row and column. The supports are disjoint. -/
def occupied {n p : ℕ} (c : Config n p) (r : Fin 2) (j : Fin p) : ℕ :=
  (if r = 0 then c.x.val else c.y.val) + (c.sigma j).val

/-- The index of an occupied basis string in increasing binary order, starting at zero. -/
noncomputable def form {n p : ℕ} (c : Config n p) :
    Fin 2 → Fin p → Fin (2 * p) := fun r j =>
  ⟨(Finset.univ.filter fun z : Fin 2 × Fin p =>
      occupied c z.1 z.2 < occupied c r j).card, by
    have h := Finset.card_lt_card (Finset.filter_ssubset.mpr
      (show ∃ z ∈ (Finset.univ : Finset (Fin 2 × Fin p)),
        ¬ occupied c z.1 z.2 < occupied c r j from
        ⟨(r, j), Finset.mem_univ _, lt_irrefl _⟩))
    simpa using h⟩

/-- All coefficient-index matrices obtained at an arbitrary number of qubits. -/
def forms (p : ℕ) : Set (Fin 2 → Fin p → Fin (2 * p)) :=
  {f | ∃ n, ∃ c : Config n p, form c = f}

/-- The coefficient-index matrices obtained at a fixed number of qubits. -/
def formsAt (n p : ℕ) : Set (Fin 2 → Fin p → Fin (2 * p)) :=
  {f | ∃ c : Config n p, form c = f}

/-- A composition contributes a top run and a bottom run of each part's size. -/
def formOf {p : ℕ} (d : Composition p) : Fin 2 → Fin p → Fin (2 * p) :=
  fun r j => ⟨j.val + d.sizeUpTo ((d.index j).val + r.val), by
    have := d.sizeUpTo_le ((d.index j).val + r.val)
    omega⟩

private theorem index_lt_iff {p : ℕ} (d : Composition p) (i : Fin p)
    (b : Fin d.length) :
    d.index i < b ↔ i.val < d.sizeUpTo b.val := by
  constructor
  · intro h
    have hi := d.lt_sizeUpTo_index_succ i
    change i.val < d.sizeUpTo ((d.index i).val + 1) at hi
    exact hi.trans_le
      (d.monotone_sizeUpTo (by change (d.index i).val < b.val at h; omega))
  · intro h
    by_contra hn
    have hb : b.val ≤ (d.index i).val := by simpa using not_lt.mp hn
    have := (d.monotone_sizeUpTo hb).trans (d.sizeUpTo_index_le i)
    omega

private theorem index_le_iff {p : ℕ} (d : Composition p) (i : Fin p)
    (b : Fin d.length) :
    d.index i ≤ b ↔ i.val < d.sizeUpTo (b.val + 1) := by
  constructor
  · intro h
    have hi := d.lt_sizeUpTo_index_succ i
    change i.val < d.sizeUpTo ((d.index i).val + 1) at hi
    exact hi.trans_le
      (d.monotone_sizeUpTo (by change (d.index i).val ≤ b.val at h; omega))
  · intro h
    by_contra hn
    have hb : b.val + 1 ≤ (d.index i).val := by
      change ¬ (d.index i).val ≤ b.val at hn
      omega
    have := (d.monotone_sizeUpTo hb).trans (d.sizeUpTo_index_le i)
    omega

private theorem boundary_iff {p : ℕ} (d : Composition p) (j : Fin (p + 1)) :
    j ∈ d.boundaries ↔ j.val = p ∨
      ∃ i : Fin p, i.val = j.val ∧ d.sizeUpTo (d.index i).val = i.val := by
  constructor
  · intro hj
    obtain ⟨b, hb, heq⟩ :=
      d.toCompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq.mp hj
    rw [Composition.toCompositionAsSet_blocks] at heq
    change d.sizeUpTo b = j.val at heq
    have hbl : b ≤ d.length := by
      simpa only [Composition.toCompositionAsSet_boundaries,
        d.card_boundaries_eq_succ_length, Nat.lt_succ_iff] using hb
    by_cases hlast : b = d.length
    · left
      simpa [hlast] using heq.symm
    · right
      let bi : Fin d.length := ⟨b, by omega⟩
      let t : Fin (d.blocksFun bi) := ⟨0, d.one_le_blocksFun bi⟩
      refine ⟨d.embedding bi t, ?_, ?_⟩
      · simpa [t, bi] using heq
      · simp [d.index_embedding, t]
  · rintro (h | ⟨i, hi, heq⟩)
    · have hj : j = Fin.last p := Fin.ext h
      rw [hj]
      exact d.toCompositionAsSet.getLast_mem
    · apply d.toCompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq.mpr
      refine ⟨(d.index i).val, ?_, ?_⟩
      · rw [Composition.toCompositionAsSet_boundaries, d.card_boundaries_eq_succ_length]
        omega
      · rw [Composition.toCompositionAsSet_blocks]
        change d.sizeUpTo (d.index i).val = j.val
        omega

/-- The top-row indices recover all the boundaries of the composition. -/
theorem formOf_injective (p : ℕ) : Function.Injective (@formOf p) := by
  intro c d h
  apply (compositionEquiv p).injective
  apply CompositionAsSet.ext
  ext j
  change j ∈ c.boundaries ↔ j ∈ d.boundaries
  rw [boundary_iff, boundary_iff]
  have hs (i : Fin p) : c.sizeUpTo (c.index i).val = d.sizeUpTo (d.index i).val := by
    have hv := congrArg Fin.val (congrFun (congrFun h 0) i)
    change i.val + c.sizeUpTo ((c.index i).val + 0) =
      i.val + d.sizeUpTo ((d.index i).val + 0) at hv
    simpa using hv
  simp_rw [hs]

private theorem index_counts {p : ℕ} (d : Composition p) (j : Fin p) :
    (Finset.univ.filter fun i : Fin p => d.index i < d.index j).card =
      d.sizeUpTo (d.index j).val ∧
    (Finset.univ.filter fun i : Fin p => d.index i ≤ d.index j).card =
      d.sizeUpTo ((d.index j).val + 1) := by
  constructor
  · simp_rw [index_lt_iff]
    rw [Fin.card_filter_val_lt, min_eq_right (d.sizeUpTo_le _)]
  · simp_rw [index_le_iff]
    rw [Fin.card_filter_val_lt, min_eq_right (d.sizeUpTo_le _)]

end D5.S3.Quantum.Entanglement.QubitSupportCoefficientForms
