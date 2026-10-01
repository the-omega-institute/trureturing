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
  (WordRepresentation wordMap wordBehavior integerTask integerFieldTask prefixes suffixes
    response_minor_le_finrank)
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

abbrev FourState (K : Type*) := Fin 4 → K

/-- Retain (b,c) in each seam block. This is a projection on the whole state space. -/
def fourTrim {K : Type*} [Field K] : SixState K →ₗ[K] FourState K where
  toFun x := ![x 1, x 2, x 4, x 5]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp

/-- Homogeneous updates of the characteristic-two quotient. -/
def fourUpdate {K : Type*} [Field K] (b : Window) (x : FourState K) : FourState K :=
  match b with
  | .zero => ![x 0 + x 2, x 1 + x 3, 0, 0]
  | .low => ![0, 0, x 0 + x 2, x 1 + x 3]
  | .middle => ![x 0 + x 2 + x 1 + x 3, x 1 + x 3, 0, 0]
  | .ends => ![0, 0, x 0 + x 1, x 1]
  | .high => ![x 0 + x 1, x 1, 0, 0]

def fourTransition {K : Type*} [Field K] (b : Window) : FourState K →ₗ[K] FourState K where
  toFun := fourUpdate b
  map_add' x y := by
    cases b <;> ext i <;> fin_cases i <;> simp [fourUpdate] <;> ring
  map_smul' r x := by
    cases b <;> ext i <;> fin_cases i <;> simp [fourUpdate] <;> ring

def fourOutput {K : Type*} [Field K] : FourState K →ₗ[K] (K × K) where
  toFun x := (x 1 + x 3, x 0 + x 2)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp <;> ring

def fourDimensional (K : Type*) [Field K] :
    WordRepresentation K Window (FourState K) (K × K) where
  transition := fourTransition
  initial := ![0, 1, 0, 0]
  output := fourOutput

/-- Six scalar queries made after actual continuations. -/
def sixSuffixes : Fin 6 → List Window :=
  ![[.high], [.high], [.high, .zero], [.zero, .high],
    [.zero, .high], [.zero, .high, .zero]]

/-- Actual task responses, with legality selected in rows zero and three. -/
def sixResponseMinor (K : Type*) [Field K] : Matrix (Fin 6) (Fin 6) K :=
  fun i j => (if i = 0 ∨ i = 3 then LinearMap.fst K K K else LinearMap.snd K K K)
    (integerFieldTask K (sixPrefixes j ++ sixSuffixes i))

/-- Four actual task queries, using the existing four prefixes and suffixes. -/
def fourResponseMinor (K : Type*) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  fun i j => (if i = 0 ∨ i = 2 then LinearMap.fst K K K else LinearMap.snd K K K)
    (integerFieldTask K (prefixes j ++ suffixes i))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Every integer-induced response is realized over any field, and actual
input histories span the six-dimensional homogeneous state space. The
attained minimum is six when two is nonzero, and four when two is zero.
Actual prefix/suffix response matrices give the lower bounds for arbitrary
finite-dimensional representations. -/
theorem result (K : Type*) [Field K] :
    (∀ w : List Window, wordBehavior (sixDimensional K) w = integerFieldTask K w) ∧
    Module.finrank K (SixState K) = 6 ∧
    LinearIndependent K (fun j : Fin 6 =>
      wordMap (sixDimensional K).transition (sixPrefixes j) (sixDimensional K).initial) ∧
    Submodule.span K (Set.range (fun w : List Window =>
      wordMap (sixDimensional K).transition w (sixDimensional K).initial)) = ⊤ ∧
    ((2 : K) ≠ 0 →
      (sixResponseMinor K).det ≠ 0 ∧
      ∀ (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
        (R : WordRepresentation K Window V (K × K)),
        (∀ w : List Window, wordBehavior R w = integerFieldTask K w) →
          6 ≤ Module.finrank K V) ∧
    ((2 : K) = 0 →
      (∀ w : List Window, wordBehavior (fourDimensional K) w = integerFieldTask K w) ∧
      Module.finrank K (FourState K) = 4 ∧
      LinearIndependent K (fun j : Fin 4 =>
        wordMap (fourDimensional K).transition (prefixes j) (fourDimensional K).initial) ∧
      Submodule.span K (Set.range (fun w : List Window =>
        wordMap (fourDimensional K).transition w (fourDimensional K).initial)) = ⊤ ∧
      (fourResponseMinor K).det ≠ 0 ∧
      ∀ (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
        (R : WordRepresentation K Window V (K × K)),
        (∀ w : List Window, wordBehavior R w = integerFieldTask K w) →
          4 ≤ Module.finrank K V) := by
  classical
  have castOne : Int.cast (R := K) (1 : ZMod 0) = 1 := Int.cast_one
  have castAdd (a b : ZMod 0) : Int.cast (R := K) (a + b) =
      Int.cast (R := K) a + Int.cast (R := K) b := Int.cast_add a b
  have castMul (a b : ZMod 0) : Int.cast (R := K) (a * b) =
      Int.cast (R := K) a * Int.cast (R := K) b := Int.cast_mul a b
  have commute (q : RawState 0) (b : Window) :
      sixTransition b (sixEmbed (K := K) q) = sixEmbed (K := K) (rawTransition q b) := by
    cases q with
    | none => cases b <;> ext i <;> fin_cases i <;> simp [sixTransition, sixUpdate,
        sixEmbed, rawTransition]
    | some q =>
      rcases q with ⟨s, a, c⟩
      cases s <;> cases b <;> ext i <;> fin_cases i <;>
        simp [sixTransition, sixUpdate, sixEmbed, rawTransition, clock,
          step, displacement, first, last, castOne, castAdd, castMul] <;> ring
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
      cases s <;> simp [sixOutput, sixEmbed, rawOutput, quantity, castAdd, castMul]
  have correct (w : List Window) :
      wordBehavior (sixDimensional K) w = integerFieldTask K w := by
    have initial : (sixDimensional K).initial =
        sixEmbed (K := K) (rawMachine 0).start := by
      ext i
      fin_cases i <;> simp [sixDimensional, sixEmbed, rawMachine, Int.cast_zero]
    unfold wordBehavior
    rw [initial]
    change sixOutput (wordMap (sixTransition (K := K)) w
      (sixEmbed (K := K) (rawMachine 0).start)) = _
    rw [simulation, observe]
    have evaluated : (rawMachine 0).toDFA.evalFrom (rawMachine 0).start w =
        (rawMachine 0).toDFA.eval w := rfl
    have readback : rawOutput ((rawMachine 0).toDFA.eval w) = task 0 w := rfl
    rw [evaluated, readback]
    simp only [integerFieldTask, integerTask]
    cases task 0 w <;> simp
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
  let O : Matrix (Fin 6) (Fin 6) K :=
    !![0, 0, 1, 0, 0, 0;
       8, 13, 5, 0, 0, 0;
       34, 55, 21, 0, 0, 0;
       0, 0, 1, 0, 0, 1;
       34, 55, 5, 34, 55, 5;
       144, 233, 21, 144, 233, 21]
  have observationDet : O.det = -4 := by
    simp [O, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Matrix.submatrix, Fin.succAbove] <;> ring
  have responseFactor : sixResponseMinor K = O * P := by
    rw [values]
    ext i j
    simp only [sixResponseMinor]
    rw [← correct]
    fin_cases i <;> fin_cases j <;>
      simp [O, sixPrefixes, sixSuffixes, wordBehavior, wordMap, wordOperator,
        sixDimensional, sixOutput, sixTransition, sixUpdate, LinearMap.comp_apply,
        Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  have responseDet : (sixResponseMinor K).det = 4 := by
    rw [responseFactor, Matrix.det_mul, observationDet, determinant]
    ring
  refine ⟨correct, by simp [SixState], independent, ?_, ?_, ?_⟩
  · apply top_unique
    rw [← independent.span_eq_top_of_card_eq_finrank' (by simp [SixState])]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨sixPrefixes j, rfl⟩
  · intro htwo
    have minorNonzero : (sixResponseMinor K).det ≠ 0 := by
      rw [responseDet]
      convert mul_ne_zero htwo htwo using 1 <;> norm_num
    refine ⟨minorNonzero, ?_⟩
    intro V _ _ _ R realized
    exact response_minor_le_finrank R (integerFieldTask K) realized
      sixPrefixes sixSuffixes
      (fun i => if i = 0 ∨ i = 3 then LinearMap.fst K K K else LinearMap.snd K K K)
      minorNonzero
  · intro htwo
    have three : (3 : K) = 1 := by
      calc
        (3 : K) = 2 + 1 := by norm_num
        _ = 1 := by rw [htwo, zero_add]
    have trimLetter (b : Window) (x : SixState K) :
        fourTransition b (fourTrim x) = fourTrim (sixTransition b x) := by
      cases b <;> ext i <;> fin_cases i <;>
        simp [fourTransition, fourUpdate, fourTrim, sixTransition, sixUpdate, htwo, three]
    have trimWords (w : List Window) (x : SixState K) :
        wordMap fourTransition w (fourTrim x) =
          fourTrim (wordMap sixTransition w x) := by
      induction w using List.reverseRecOn with
      | nil => rfl
      | append_singleton w b ih =>
        simp only [wordMap, List.reverse_append, List.reverse_singleton,
          List.singleton_append, wordOperator, LinearMap.comp_apply]
        change fourTransition b (wordMap fourTransition w (fourTrim x)) =
          fourTrim (sixTransition b (wordMap sixTransition w x))
        rw [ih, trimLetter]
    have trimOutput (x : SixState K) : fourOutput (fourTrim x) = sixOutput x := by
      ext <;> simp [fourOutput, fourTrim, sixOutput, htwo, three]
    have fourCorrect (w : List Window) :
        wordBehavior (fourDimensional K) w = integerFieldTask K w := by
      have initial : (fourDimensional K).initial = fourTrim (sixDimensional K).initial := by
        ext i
        fin_cases i <;> simp [fourDimensional, fourTrim, sixDimensional]
      unfold wordBehavior
      rw [initial]
      change fourOutput (wordMap fourTransition w (fourTrim (sixDimensional K).initial)) = _
      rw [trimWords, trimOutput]
      exact correct w
    let fourReach : Fin 4 → FourState K := fun j =>
      wordMap (fourDimensional K).transition (prefixes j) (fourDimensional K).initial
    let Q : Matrix (Fin 4) (Fin 4) K := fun i j => fourReach j i
    have fourValues : Q = !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Q, fourReach, prefixes, wordMap, wordOperator, fourDimensional,
          fourTransition, fourUpdate, LinearMap.comp_apply]
    have fourDeterminant : Q.det = 1 := by
      rw [fourValues]
      simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]
    have fourNonzero : Q.det ≠ 0 := by rw [fourDeterminant]; exact one_ne_zero
    have fourIndependent : LinearIndependent K fourReach := by
      change LinearIndependent K Q.col
      exact Matrix.linearIndependent_cols_of_det_ne_zero fourNonzero
    have fourMinorValues : fourResponseMinor K =
        !![1, 1, 0, 0; 1, 2, 0, 0; 1, 1, 1, 1; 1, 2, 1, 2] := by
      ext i j
      simp only [fourResponseMinor]
      rw [← fourCorrect]
      fin_cases i <;> fin_cases j <;>
        simp [prefixes, suffixes, wordBehavior, wordMap, wordOperator,
          fourDimensional, fourOutput, fourTransition, fourUpdate, LinearMap.comp_apply] <;> ring
    have fourMinorDet : (fourResponseMinor K).det = 1 := by
      rw [fourMinorValues]
      simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix,
        Fin.succAbove] <;> ring
    have fourMinorNonzero : (fourResponseMinor K).det ≠ 0 := by
      rw [fourMinorDet]
      exact one_ne_zero
    refine ⟨fourCorrect, by simp [FourState], fourIndependent, ?_, fourMinorNonzero, ?_⟩
    · apply top_unique
      rw [← fourIndependent.span_eq_top_of_card_eq_finrank' (by simp [FourState])]
      apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨prefixes j, rfl⟩
    · intro V _ _ _ R realized
      exact response_minor_le_finrank R (integerFieldTask K) realized
        prefixes suffixes
        (fun i => if i = 0 ∨ i = 2 then LinearMap.fst K K K else LinearMap.snd K K K)
        fourMinorNonzero

end D5.S3.Arith.FibonacciAtomic.FiveWindowFieldLinearMinimum
