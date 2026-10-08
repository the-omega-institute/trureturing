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

end D5.S3.Quantum.Entanglement.QubitSupportCoefficientForms
