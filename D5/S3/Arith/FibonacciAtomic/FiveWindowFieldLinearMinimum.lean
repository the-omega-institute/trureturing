/- GID: D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fibonacci responses admit homogeneous field realizations. -/

import D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FiveWindowFieldLinearMinimum

open D5.S0.Automata.DFAOStateLowerBound
open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity)
open D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity
open D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
  (WordRepresentation wordMap wordBehavior integerTask integerFieldTask)
open D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound (wordOperator)

abbrev SixState (K : Type*) := Fin 6 → K

/-- Coordinates are (a₀,b₀,c₀,a₁,b₁,c₁). Only allowed source blocks contribute. -/
def sixUpdate {K : Type*} [Field K] (b : Window) (x : SixState K) : SixState K :=
  match b with
  | .zero => ![x 0 + x 3 + 2 * (x 1 + x 4),
      2 * (x 0 + x 3) + 3 * (x 1 + x 4), x 2 + x 5, 0, 0, 0]
  | .low => ![0, 0, 0, x 0 + x 3 + 2 * (x 1 + x 4) + x 2 + x 5,
      2 * (x 0 + x 3) + 3 * (x 1 + x 4), x 2 + x 5]
  | .middle => ![x 0 + x 3 + 2 * (x 1 + x 4),
      2 * (x 0 + x 3) + 3 * (x 1 + x 4) + x 2 + x 5, x 2 + x 5, 0, 0, 0]
  | .ends => ![0, 0, 0, x 0 + 2 * x 1 + 2 * x 2, 2 * x 0 + 3 * x 1 + x 2, x 2]
  | .high => ![x 0 + 2 * x 1 + x 2, 2 * x 0 + 3 * x 1 + x 2, x 2, 0, 0, 0]

def sixTransition {K : Type*} [Field K] (b : Window) : SixState K →ₗ[K] SixState K where
  toFun := sixUpdate b
  map_add' x y := by
    cases b <;> ext i <;> fin_cases i <;> simp [sixUpdate] <;> ring
  map_smul' r x := by
    cases b <;> ext i <;> fin_cases i <;> simp [sixUpdate] <;> ring

def sixOutput {K : Type*} [Field K] : SixState K →ₗ[K] (K × K) where
  toFun x := (x 2 + x 5, 2 * (x 0 + x 3) + 3 * (x 1 + x 4))
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp <;> ring

def sixDimensional (K : Type*) [Field K] :
    WordRepresentation K Window (SixState K) (K × K) where
  transition := sixTransition
  initial := ![0, 0, 1, 0, 0, 0]
  output := sixOutput

/-- The absorbing error becomes zero; a legal integer composition occupies its seam block. -/
def sixEmbed {K : Type*} [Field K] : RawState 0 → SixState K
  | none => 0
  | some (s, a, b) =>
    if s then ![0, 0, 0, (Int.castRingHom K) a, (Int.castRingHom K) b, 1]
    else ![(Int.castRingHom K) a, (Int.castRingHom K) b, 1, 0, 0, 0]

/-- Six actual input histories, rather than arbitrary prescribed state vectors. -/
def sixPrefixes : Fin 6 → List Window :=
  ![[], [.middle], [.high], [.low], [.middle, .low], [.high, .low]]

set_option maxHeartbeats 800000 in
/-- Every integer-induced response is realized over any field, and actual
input histories span the whole six-dimensional homogeneous state space. -/
theorem result (K : Type*) [Field K] :
    (∀ w : List Window, wordBehavior (sixDimensional K) w = integerFieldTask K w) ∧
    Module.finrank K (SixState K) = 6 ∧
    LinearIndependent K (fun j : Fin 6 =>
      wordMap (sixDimensional K).transition (sixPrefixes j) (sixDimensional K).initial) ∧
    Submodule.span K (Set.range (fun w : List Window =>
      wordMap (sixDimensional K).transition w (sixDimensional K).initial)) = ⊤ := by
  classical
  have commute (q : RawState 0) (b : Window) :
      sixTransition b (sixEmbed (K := K) q) = sixEmbed (K := K) (rawTransition q b) := by
    cases q with
    | none => cases b <;> ext i <;> fin_cases i <;> simp [sixTransition, sixUpdate,
        sixEmbed, rawTransition]
    | some q =>
      rcases q with ⟨s, a, c⟩
      cases s <;> cases b <;> ext i <;> fin_cases i <;>
        simp [sixTransition, sixUpdate, sixEmbed, rawTransition, clock,
          step, displacement, first, last] <;> push_cast <;> ring
  have simulation (w : List Window) (q : RawState 0) :
      wordMap (sixTransition (K := K)) w (sixEmbed (K := K) q) =
        sixEmbed (K := K) ((rawMachine 0).toDFA.evalFrom q w) := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w b ih =>
      simp only [wordMap, List.reverse_append, List.reverse_singleton,
        List.singleton_append, wordOperator, LinearMap.comp_apply,
        DFA.evalFrom_append_singleton]
      change sixTransition b (wordMap (sixTransition (K := K)) w (sixEmbed (K := K) q)) =
        sixEmbed (K := K) (rawTransition ((rawMachine 0).toDFA.evalFrom q w) b)
      rw [ih, commute]
  have observe (q : RawState 0) :
      sixOutput (sixEmbed (K := K) q) =
        match rawOutput q with
        | none => (0, 0)
        | some n => (1, (Int.castRingHom K) n) := by
    cases q with
    | none => simp [sixOutput, sixEmbed, rawOutput]
    | some q =>
      rcases q with ⟨s, a, b⟩
      cases s <;> simp [sixOutput, sixEmbed, rawOutput, quantity] <;> push_cast <;> ring
  have correct (w : List Window) :
      wordBehavior (sixDimensional K) w = integerFieldTask K w := by
    have initial : (sixDimensional K).initial =
        sixEmbed (K := K) (rawMachine 0).start := by
      ext i
      fin_cases i <;> simp [sixDimensional, sixEmbed, rawMachine]
    unfold wordBehavior
    rw [initial]
    change sixOutput (wordMap (sixTransition (K := K)) w
      (sixEmbed (K := K) (rawMachine 0).start)) = _
    rw [simulation, observe]
    simp only [integerFieldTask, integerTask, task, DFAO.evalOutput]
    change (match rawOutput ((rawMachine 0).toDFA.eval w) with
      | none => (0, 0)
      | some n => (1, (Int.castRingHom K) n)) = _
    cases h : rawOutput ((rawMachine 0).toDFA.eval w) <;> simp [h]
  let reach : Fin 6 → SixState K := fun j =>
    wordMap (sixDimensional K).transition (sixPrefixes j) (sixDimensional K).initial
  let P : Matrix (Fin 6) (Fin 6) K := fun i j => reach j i
  have values : P =
      !![0, 0, 1, 0, 0, 0;
         0, 1, 1, 0, 0, 0;
         1, 1, 1, 0, 0, 0;
         0, 0, 0, 1, 3, 4;
         0, 0, 0, 0, 3, 5;
         0, 0, 0, 1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, reach, sixPrefixes, wordMap, wordOperator, sixDimensional,
        sixTransition, sixUpdate, LinearMap.comp_apply] <;> ring
  have determinant : P.det = -1 := by
    rw [values]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove] <;> ring
  have nonzero : P.det ≠ 0 := by rw [determinant]; exact neg_ne_zero.mpr one_ne_zero
  have independent : LinearIndependent K reach := by
    change LinearIndependent K P.col
    exact Matrix.linearIndependent_cols_of_det_ne_zero nonzero
  refine ⟨correct, by simp [SixState], independent, ?_⟩
  apply top_unique
  rw [← independent.span_eq_top_of_card_eq_finrank' (by simp [SixState])]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨sixPrefixes j, rfl⟩

#print axioms result

end D5.S3.Arith.FibonacciAtomic.FiveWindowFieldLinearMinimum
