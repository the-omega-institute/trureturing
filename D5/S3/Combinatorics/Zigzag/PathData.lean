/- GID: D5/S3/Combinatorics/Zigzag/PathData
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/PathData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Label-preserving five-state retirement data for both signed sectors. -/

import D5.S3.Combinatorics.Zigzag.Choices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

/-- The five frontier-charge states `(A,D,E,H,I)`. -/
abbrev State := Fin 5

namespace State

def A : State := 0
def D : State := 1
def E : State := 2
def H : State := 3
def I : State := 4

end State

/-- The two sectors are kept separate because reflection changes the labels. -/
inductive Half where
  | positive | negative
  deriving DecidableEq, Repr

/-- One labelled retirement step. `charge` is the change of imbalance at `+1`. -/
structure Transition where
  low : Form
  high : Form
  target : State
  charge : Int
  deriving DecidableEq, Repr

/-- Sector-specific labels and charges on one shared topology index. -/
structure StepLabel where
  low : Form
  high : Form
  charge : Int
  deriving DecidableEq, Repr

/-- The common target topology of the positive and negative labelled sectors. -/
def stepTargets : State -> List State
  | ⟨0, _⟩ => [State.A, State.D, State.E, State.I]
  | ⟨1, _⟩ => [State.A, State.D, State.E, State.H]
  | ⟨2, _⟩ => [State.A, State.D]
  | ⟨3, _⟩ => [State.D]
  | ⟨4, _⟩ => [State.A]

abbrev StepIndex (s : State) := Fin (stepTargets s).length

def stepTarget {s : State} (i : StepIndex s) : State := (stepTargets s).get i

/-- The complete positive-sector labels and charges, indexed by shared topology. -/
def positiveStepLabel : (s : State) -> StepIndex s -> StepLabel
  | ⟨0, _⟩, i =>
      [⟨Form.I, Form.VI, 1⟩, ⟨Form.I, Form.I, 2⟩,
       ⟨Form.III, Form.IV, 0⟩, ⟨Form.V, Form.IV, -1⟩].get i
  | ⟨1, _⟩, i =>
      [⟨Form.VI, Form.VI, 0⟩, ⟨Form.VI, Form.I, 1⟩,
       ⟨Form.V, Form.II, -1⟩, ⟨Form.III, Form.II, 0⟩].get i
  | ⟨2, _⟩, i => [⟨Form.II, Form.V, -1⟩, ⟨Form.IV, Form.III, 0⟩].get i
  | ⟨3, _⟩, i => [⟨Form.IV, Form.V, -1⟩].get i
  | ⟨4, _⟩, i => [⟨Form.II, Form.III, 0⟩].get i

/-- The complete negative-sector labels and charges, on the same indices. -/
def negativeStepLabel : (s : State) -> StepIndex s -> StepLabel
  | ⟨0, _⟩, i =>
      [⟨Form.III, Form.V, -1⟩, ⟨Form.V, Form.V, -2⟩,
       ⟨Form.IV, Form.VI, 0⟩, ⟨Form.IV, Form.I, 1⟩].get i
  | ⟨1, _⟩, i =>
      [⟨Form.III, Form.III, 0⟩, ⟨Form.V, Form.III, -1⟩,
       ⟨Form.II, Form.I, 1⟩, ⟨Form.II, Form.VI, 0⟩].get i
  | ⟨2, _⟩, i => [⟨Form.I, Form.II, 1⟩, ⟨Form.VI, Form.IV, 0⟩].get i
  | ⟨3, _⟩, i => [⟨Form.I, Form.IV, 1⟩].get i
  | ⟨4, _⟩, i => [⟨Form.VI, Form.II, 0⟩].get i

def stepValue {h : Half} {s : State} (i : StepIndex s) : Transition :=
  let label := match h with
    | .positive => positiveStepLabel s i
    | .negative => negativeStepLabel s i
  ⟨label.low, label.high, stepTarget i, label.charge⟩

/-- The class-two choice, resulting state, and initial `+1` charge. -/
structure Start where
  label : Form
  charge : Int
  deriving DecidableEq, Repr

def starts : Half -> List Start
  | .positive => [⟨Form.II, 0⟩, ⟨Form.IV, 1⟩]
  | .negative => [⟨Form.III, 0⟩, ⟨Form.V, -1⟩]

/-- The common two-state topology of both signed start sectors. -/
def startTargets : List State := [State.A, State.D]

/-- The even antipodal pair and its last charge change. -/
structure EvenTerminal where
  low : Form
  high : Form
  charge : Int
  deriving DecidableEq, Repr

/-- The odd singleton and its last charge change. -/
structure OddTerminal where
  label : Form
  charge : Int
  deriving DecidableEq, Repr

abbrev StartIndex (_h : Half) := Fin 2

def startValue {h : Half} (i : StartIndex h) : Start :=
  match h with
  | .positive => (starts .positive).get i
  | .negative => (starts .negative).get i

def startTarget (i : Fin 2) : State :=
  startTargets.get i

def EvenTerminalIndex (_h : Half) (s : State) : Type :=
  match s with
  | ⟨0, _⟩ => Fin 1
  | ⟨1, _⟩ => Fin 1
  | ⟨2, _⟩ => Fin 0
  | ⟨3, _⟩ => Fin 0
  | ⟨4, _⟩ => Fin 0

instance (h : Half) (s : State) : Fintype (EvenTerminalIndex h s) := by
  exact match s with
  | ⟨0, _⟩ => inferInstanceAs (Fintype (Fin 1))
  | ⟨1, _⟩ => inferInstanceAs (Fintype (Fin 1))
  | ⟨2, _⟩ => inferInstanceAs (Fintype (Fin 0))
  | ⟨3, _⟩ => inferInstanceAs (Fintype (Fin 0))
  | ⟨4, _⟩ => inferInstanceAs (Fintype (Fin 0))

def evenTerminalValue {h : Half} {s : State}
    (i : EvenTerminalIndex h s) : EvenTerminal :=
  match h, s with
  | .positive, ⟨0, _⟩ => ⟨Form.III, Form.IV, 0⟩
  | .positive, ⟨1, _⟩ => ⟨Form.V, Form.II, -1⟩
  | .positive, ⟨2, _⟩ => Fin.elim0 i
  | .positive, ⟨3, _⟩ => Fin.elim0 i
  | .positive, ⟨4, _⟩ => Fin.elim0 i
  | .negative, ⟨0, _⟩ => ⟨Form.IV, Form.VI, 0⟩
  | .negative, ⟨1, _⟩ => ⟨Form.II, Form.I, 1⟩
  | .negative, ⟨2, _⟩ => Fin.elim0 i
  | .negative, ⟨3, _⟩ => Fin.elim0 i
  | .negative, ⟨4, _⟩ => Fin.elim0 i

def OddTerminalIndex (_h : Half) (s : State) : Type :=
  match s with
  | ⟨0, _⟩ => Fin 1
  | ⟨1, _⟩ => Fin 1
  | ⟨2, _⟩ => Fin 0
  | ⟨3, _⟩ => Fin 0
  | ⟨4, _⟩ => Fin 0

instance (h : Half) (s : State) : Fintype (OddTerminalIndex h s) := by
  exact match s with
  | ⟨0, _⟩ => inferInstanceAs (Fintype (Fin 1))
  | ⟨1, _⟩ => inferInstanceAs (Fintype (Fin 1))
  | ⟨2, _⟩ => inferInstanceAs (Fintype (Fin 0))
  | ⟨3, _⟩ => inferInstanceAs (Fintype (Fin 0))
  | ⟨4, _⟩ => inferInstanceAs (Fintype (Fin 0))

def oddTerminalValue {h : Half} {s : State}
    (i : OddTerminalIndex h s) : OddTerminal :=
  match h, s with
  | .positive, ⟨0, _⟩ => ⟨Form.I, 1⟩
  | .positive, ⟨1, _⟩ => ⟨Form.VI, 0⟩
  | .positive, ⟨2, _⟩ => Fin.elim0 i
  | .positive, ⟨3, _⟩ => Fin.elim0 i
  | .positive, ⟨4, _⟩ => Fin.elim0 i
  | .negative, ⟨0, _⟩ => ⟨Form.V, -1⟩
  | .negative, ⟨1, _⟩ => ⟨Form.III, 0⟩
  | .negative, ⟨2, _⟩ => Fin.elim0 i
  | .negative, ⟨3, _⟩ => Fin.elim0 i
  | .negative, ⟨4, _⟩ => Fin.elim0 i

/-- A labelled even tail with `m` interior retirement steps. -/
def EvenTail (h : Half) : Nat -> State -> Type
  | 0, s => EvenTerminalIndex h s
  | m + 1, s => (i : StepIndex s) ×' EvenTail h m (stepTarget i)

/-- A labelled odd tail with `m` interior retirement steps. -/
def OddTail (h : Half) : Nat -> State -> Type
  | 0, s => OddTerminalIndex h s
  | m + 1, s => (i : StepIndex s) ×' OddTail h m (stepTarget i)

/-- Complete labelled even paths, including the class-two start. -/
def EvenPath (h : Half) (m : Nat) :=
  (i : StartIndex h) ×' EvenTail h m (startTarget i)

/-- Complete labelled odd paths, including the class-two start. -/
def OddPath (h : Half) (m : Nat) :=
  (i : StartIndex h) ×' OddTail h m (startTarget i)

def evenTailCharge {h : Half} : {m : Nat} -> {s : State} -> EvenTail h m s -> Int
  | 0, _, e => (evenTerminalValue (h := h) e).charge
  | _ + 1, _, ⟨i, p⟩ =>
      (stepValue (h := h) i).charge + evenTailCharge p

def oddTailCharge {h : Half} : {m : Nat} -> {s : State} -> OddTail h m s -> Int
  | 0, _, e => (oddTerminalValue (h := h) e).charge
  | _ + 1, _, ⟨i, p⟩ =>
      (stepValue (h := h) i).charge + oddTailCharge p

def evenPathCharge {h : Half} {m : Nat} (p : EvenPath h m) : Int :=
  (startValue (h := h) p.1).charge + evenTailCharge p.2

def oddPathCharge {h : Half} {m : Nat} (p : OddPath h m) : Int :=
  (startValue (h := h) p.1).charge + oddTailCharge p.2

noncomputable instance (h : Half) (m : Nat) (s : State) :
    Fintype (EvenTail h m s) := by
  induction m generalizing s with
  | zero =>
      unfold EvenTail
      infer_instance
  | succ m ih =>
      unfold EvenTail
      letI (i : StepIndex s) :
          Fintype (EvenTail h m (stepTarget i)) := ih _
      infer_instance

noncomputable instance (h : Half) (m : Nat) (s : State) :
    Fintype (OddTail h m s) := by
  induction m generalizing s with
  | zero =>
      unfold OddTail
      infer_instance
  | succ m ih =>
      unfold OddTail
      letI (i : StepIndex s) :
          Fintype (OddTail h m (stepTarget i)) := ih _
      infer_instance

noncomputable instance (h : Half) (m : Nat) : Fintype (EvenPath h m) := by
  unfold EvenPath
  letI (i : StartIndex h) :
      Fintype (EvenTail h m (startTarget i)) := inferInstance
  infer_instance

noncomputable instance (h : Half) (m : Nat) : Fintype (OddPath h m) := by
  unfold OddPath
  letI (i : StartIndex h) :
      Fintype (OddTail h m (startTarget i)) := inferInstance
  infer_instance

end D5.S3.Combinatorics.Zigzag
