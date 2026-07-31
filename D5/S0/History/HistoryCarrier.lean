/- GID: D5/S0/History/HistoryCarrier
   generality: G
   mirror-B: D5/B/S0/History/HistoryCarrier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite marker and event histories with faithful append and low-level encoding. -/

import Mathlib.Algebra.FreeMonoid.Basic

namespace D5.S0.History

/-- The two primitive markers of Definition 2.1. -/
inductive Marker where
  | E₀
  | E₁
  deriving DecidableEq, Repr

/-- Finite marker histories. The list order is outermost marker first. -/
abbrev MarkerHistory := FreeMonoid Marker

/-- Definition 2.1's append. Reversed free-monoid multiplication preserves the
    source convention that `E_ε` extends the left end of an expression. -/
def splice (h g : MarkerHistory) : MarkerHistory := g * h

@[simp] theorem splice_empty_right (h : MarkerHistory) : splice h 1 = h := by
  simp [splice]

@[simp] theorem splice_extend (h g : MarkerHistory) (ε : Marker) :
    splice h (FreeMonoid.of ε * g) = FreeMonoid.of ε * splice h g := by
  simp [splice, mul_assoc]

/-- The instruction set named in Definition 15.1. -/
inductive Opcode where
  | gen | enc | norm | decode | length | phase
  | read | ledger | renorm | complete | reflect | certify
  deriving DecidableEq, Repr

/-- Definition 2.2, with both codes represented in the marker carrier. -/
structure Event where
  src : MarkerHistory
  op : Opcode
  arg : MarkerHistory
  tag : Marker

/-- Definition 2.3's finite event histories. -/
abbrev EventHistory := FreeMonoid Event

/-- Append one event after an event history. -/
def generate (h : EventHistory) (u : Event) : EventHistory :=
  h * FreeMonoid.of u

/-- A prefix-free fixed-width opcode field for the finite instruction set. -/
def opcodeCode : Opcode → MarkerHistory
  | .gen => [.E₀, .E₀, .E₀, .E₀]
  | .enc => [.E₀, .E₀, .E₀, .E₁]
  | .norm => [.E₀, .E₀, .E₁, .E₀]
  | .decode => [.E₀, .E₀, .E₁, .E₁]
  | .length => [.E₀, .E₁, .E₀, .E₀]
  | .phase => [.E₀, .E₁, .E₀, .E₁]
  | .read => [.E₀, .E₁, .E₁, .E₀]
  | .ledger => [.E₀, .E₁, .E₁, .E₁]
  | .renorm => [.E₁, .E₀, .E₀, .E₀]
  | .complete => [.E₁, .E₀, .E₀, .E₁]
  | .reflect => [.E₁, .E₀, .E₁, .E₀]
  | .certify => [.E₁, .E₀, .E₁, .E₁]

/-- Definition 14.1's literal low-level marker pairing. -/
def pairMarker : Marker → MarkerHistory
  | .E₀ => [.E₀, .E₀]
  | .E₁ => [.E₀, .E₁]

/-- Encode a marker field using `0 ↦ 00` and `1 ↦ 01`. -/
def encodeField : MarkerHistory → MarkerHistory :=
  FreeMonoid.lift pairMarker

/-- Definition 14.1's field separator `11`. -/
def fieldSeparator : MarkerHistory := [.E₁, .E₁]

/-- Low-level encoding bridge from a Definition 2.2 event to marker history. -/
def encodeEvent (u : Event) : MarkerHistory :=
  encodeField u.src * fieldSeparator *
    encodeField (opcodeCode u.op) * fieldSeparator *
    encodeField u.arg * fieldSeparator * encodeField [u.tag]

/-- The Definition 2.3 unification bridge from event histories into `MarkerHistory`. -/
def encodeEventHistory : EventHistory → MarkerHistory :=
  FreeMonoid.lift encodeEvent

@[simp] theorem encodeEventHistory_generate (h : EventHistory) (u : Event) :
    encodeEventHistory (generate h u) =
      encodeEventHistory h * encodeEvent u := by
  simp [encodeEventHistory, generate]

/-- Definition 2.4's three laws, kept as one atomic acceptance declaration. -/
theorem marker_splice_laws :
    (∀ a b c : MarkerHistory, splice (splice a b) c = splice a (splice b c)) ∧
      (∀ h : MarkerHistory, splice 1 h = h) ∧
      (∀ h : MarkerHistory, splice h 1 = h) := by
  simp [splice, mul_assoc]

end D5.S0.History
