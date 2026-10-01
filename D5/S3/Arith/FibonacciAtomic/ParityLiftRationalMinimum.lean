/- GID: D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The rational lift of five-window parity has attained minimum dimension four. -/

import D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum

open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity

/-- A linear representation of finite words, with one operator per letter.
The state space need not be reachable, observable or finite dimensional. -/
structure WordRepresentation (K : Type*) [Field K] (Alphabet : Type*)
    (V Y : Type*) [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module K Y] where
  transition : Alphabet → V →ₗ[K] V
  initial : V
  output : V →ₗ[K] Y

/-- Operators act in chronological order, starting at the leftmost letter. -/
def wordMap {K : Type*} [Field K] {Alphabet V : Type*}
    [AddCommGroup V] [Module K V] (T : Alphabet → V →ₗ[K] V) :
    List Alphabet → V →ₗ[K] V
  | [] => LinearMap.id
  | b :: w => (wordMap T w).comp (T b)

def wordBehavior {K : Type*} [Field K] {Alphabet V Y : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module K Y]
    (R : WordRepresentation K Alphabet V Y) (w : List Alphabet) : Y :=
  R.output (wordMap R.transition w R.initial)

/-- Standard representatives are taken before embedding into the rational numbers. -/
def parityEncode : Option (ZMod 2) → ℚ × ℚ
  | none => (0, 0)
  | some b => (1, b.val)

def parityTask (w : List Window) : ℚ × ℚ := parityEncode (task 2 w)

/-- Legality and the complete integer quantity, before selecting a coefficient field. -/
def integerTask (w : List Window) : ℤ × ℤ :=
  match task 0 w with
  | none => (0, 0)
  | some x => (1, x)

/-- Coordinatewise natural embedding of the integer response into any field. -/
def integerFieldTask (K : Type*) [Field K] (w : List Window) : K × K :=
  ((integerTask w).1, (integerTask w).2)

/-- The integer-induced rational task keeps the complete integer quantity. -/
def integerRationalTask (w : List Window) : ℚ × ℚ := integerFieldTask ℚ w

abbrev BlockState := Fin 4 → ℚ

/-- Coordinates are (b₀,c₀,b₁,c₁); illegal source blocks are discarded.
A flip uses J(b,c)=(c-b,c), including away from actual Boolean states. -/
def blockUpdate (b : Window) (x : BlockState) : BlockState :=
  match b with
  | .zero => ![x 0 + x 2, x 1 + x 3, 0, 0]
  | .low => ![0, 0, x 0 + x 2, x 1 + x 3]
  | .middle => ![x 1 + x 3 - (x 0 + x 2), x 1 + x 3, 0, 0]
  | .ends => ![0, 0, x 1 - x 0, x 1]
  | .high => ![x 1 - x 0, x 1, 0, 0]

def blockTransition (b : Window) : BlockState →ₗ[ℚ] BlockState where
  toFun := blockUpdate b
  map_add' x y := by
    cases b <;> ext i <;> fin_cases i <;> simp [blockUpdate] <;> ring
  map_smul' r x := by
    cases b <;> ext i <;> fin_cases i <;> simp [blockUpdate] <;> ring

def blockOutput : BlockState →ₗ[ℚ] (ℚ × ℚ) where
  toFun x := (x 1 + x 3, x 0 + x 2)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp <;> ring

def fourDimensional : WordRepresentation ℚ Window BlockState (ℚ × ℚ) where
  transition := blockTransition
  initial := ![0, 1, 0, 0]
  output := blockOutput

/-- Embed the actual mod-two reader, including its absorbing error. -/
def embed : RawState 2 → BlockState
  | none => 0
  | some (s, x) => if s then ![0, 0, (x.2.val : ℚ), 1] else ![(x.2.val : ℚ), 1, 0, 0]

/-- The four actual histories used in the lower bound. -/
def prefixes : Fin 4 → List Window := ![[], [.middle], [.low], [.middle, .low]]

/-- Two output coordinates, queried after each of two actual continuations. -/
def suffixes : Fin 4 → List Window := ![[.high], [.high], [.zero, .high], [.zero, .high]]

def selectOutput (i : Fin 4) : (ℚ × ℚ) →ₗ[ℚ] ℚ :=
  if i = 0 ∨ i = 2 then LinearMap.fst ℚ ℚ ℚ else LinearMap.snd ℚ ℚ ℚ

def responseMinor : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => selectOutput i (parityTask (prefixes j ++ suffixes i))

/-- A four-dimensional all-word implementation is minimal among arbitrary
finite-dimensional rational linear representations. The parity lift and
integer-induced rational task have different responses already on [3]. -/
theorem result :
    (∀ w : List Window, wordBehavior fourDimensional w = parityTask w) ∧
    Module.finrank ℚ BlockState = 4 ∧
    (∀ (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (R : WordRepresentation ℚ Window V (ℚ × ℚ)),
      (∀ w : List Window, wordBehavior R w = parityTask w) → 4 ≤ Module.finrank ℚ V) ∧
    parityTask [.middle] = (1, 1) ∧ integerRationalTask [.middle] = (1, 3) ∧
    responseMinor = !![1, 1, 0, 0; 1, 0, 0, 0; 1, 1, 1, 1; 1, 0, 1, 0] ∧
    responseMinor.det = 1 := by
  classical
  have commute (q : RawState 2) (b : Window) :
      blockTransition b (embed q) = embed (rawTransition q b) := by
    cases q with
    | none => cases b <;> ext i <;> fin_cases i <;> decide +kernel
    | some q =>
      rcases q with ⟨s, a, c⟩
      fin_cases a <;> fin_cases c <;> cases s <;> cases b <;>
        ext i <;> fin_cases i <;> decide +kernel
  have simulation (w : List Window) (q : RawState 2) :
      wordMap blockTransition w (embed q) =
        embed ((rawMachine 2).toDFA.evalFrom q w) := by
    induction w generalizing q with
    | nil => rfl
    | cons b w ih =>
      simp only [wordMap, LinearMap.comp_apply, DFA.evalFrom_cons]
      rw [commute]
      exact ih (rawTransition q b)
  have observe (q : RawState 2) :
      blockOutput (embed q) = parityEncode (rawOutput q) := by
    cases q with
    | none => decide +kernel
    | some q =>
      rcases q with ⟨s, a, c⟩
      fin_cases a <;> fin_cases c <;> cases s <;> decide +kernel
  have upper (w : List Window) : wordBehavior fourDimensional w = parityTask w := by
    change blockOutput (wordMap blockTransition w (embed (some (false, (0, 0))))) = _
    rw [simulation, observe]
    rfl
  have minor : responseMinor =
      !![1, 1, 0, 0; 1, 0, 0, 0; 1, 1, 1, 1; 1, 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have detValue : responseMinor.det = 1 := by
    rw [minor]
    decide +kernel
  refine ⟨upper, by simp [BlockState], ?_, ?_, ?_, minor, detValue⟩
  · intro V _ _ _ R correct
    have append (u w : List Window) :
        wordMap R.transition (u ++ w) =
          (wordMap R.transition w).comp (wordMap R.transition u) := by
      induction u with
      | nil => simp [wordMap]
      | cons b u ih =>
        simp only [List.cons_append, wordMap, ih, LinearMap.comp_assoc]
    let reach : Fin 4 → V := fun j => wordMap R.transition (prefixes j) R.initial
    let observe : V →ₗ[ℚ] (Fin 4 → ℚ) :=
      LinearMap.pi fun i =>
        (selectOutput i).comp (R.output.comp (wordMap R.transition (suffixes i)))
    have factor (i j : Fin 4) : observe (reach j) i = responseMinor i j := by
      change selectOutput i (R.output (wordMap R.transition (suffixes i)
        (wordMap R.transition (prefixes j) R.initial))) = _
      change selectOutput i (R.output (((wordMap R.transition (suffixes i)).comp
        (wordMap R.transition (prefixes j))) R.initial)) = _
      rw [← append]
      exact congrArg (selectOutput i) (correct (prefixes j ++ suffixes i))
    have det : responseMinor.det ≠ 0 := by rw [detValue]; norm_num
    have independent : LinearIndependent ℚ (observe ∘ reach) := by
      have columns := Matrix.linearIndependent_cols_of_det_ne_zero det
      have eq : observe ∘ reach = responseMinor.col := by
        ext j i
        exact factor i j
      rw [eq]
      exact columns
    have statesIndependent := independent.of_comp observe
    simpa using statesIndependent.fintype_card_le_finrank
  · decide +kernel
  · decide +kernel

end D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
