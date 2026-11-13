/- GID: D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Joint five-window Hankel rank and minimum dimension are four in characteristic two. -/

import D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum

/-! # Characteristic-two joint rank of the integer-induced five-window task -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum

open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity)
open D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
  (WordRepresentation wordMap wordBehavior integerTask integerFieldTask)
open D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound (wordOperator)

variable (K : Type*) [Field K]

/-- Two homogeneous seam blocks, in the order (b₀,c₀,b₁,c₁). -/
abbrev BlockState := Fin 4 → K

/-- The reduced Fibonacci clock fixes b. A nonzero b-displacement adds c;
only legal source blocks contribute to the destination seam. -/
def blockUpdate (b : Window) (x : BlockState K) : BlockState K :=
  match b with
  | .zero => ![x 0 + x 2, x 1 + x 3, 0, 0]
  | .low => ![0, 0, x 0 + x 2, x 1 + x 3]
  | .middle => ![x 0 + x 2 + (x 1 + x 3), x 1 + x 3, 0, 0]
  | .ends => ![0, 0, x 0 + x 1, x 1]
  | .high => ![x 0 + x 1, x 1, 0, 0]

def blockTransition (b : Window) : BlockState K →ₗ[K] BlockState K where
  toFun := blockUpdate K b
  map_add' x y := by
    cases b <;> ext i <;> fin_cases i <;> simp [blockUpdate] <;> ring
  map_smul' r x := by
    cases b <;> ext i <;> fin_cases i <;> simp [blockUpdate] <;> ring

/-- Legality and quantity are separate output coordinates. -/
def blockOutput : BlockState K →ₗ[K] (K × K) where
  toFun x := (x 1 + x 3, x 0 + x 2)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp <;> ring

def fourDimensional : WordRepresentation K Window (BlockState K) (K × K) where
  transition := blockTransition K
  initial := ![0, 1, 0, 0]
  output := blockOutput K

/-- Reduce an integer raw state, retaining its historical seam and its error.
The first integer composition coordinate is discarded only in this embedding. -/
def embed : RawState 0 → BlockState K
  | none => 0
  | some (s, x) =>
    if s then ![0, 0, Int.cast (x.2 : ℤ), 1] else ![Int.cast (x.2 : ℤ), 1, 0, 0]

/-- Select one of the two output channels. -/
def channel (i : Fin 2) : (K × K) →ₗ[K] K :=
  if i = 0 then LinearMap.fst K K K else LinearMap.snd K K K

/-- A joint residual is one function of both a continuation and a channel. -/
def jointResidual (f : List Window → K × K) (u : List Window) :
    (List Window × Fin 2) → K :=
  fun t => channel K t.2 (f (u ++ t.1))

/-- The span of all joint residuals, without a bound on prefix or suffix length. -/
def jointHankelSpace (f : List Window → K × K) :
    Submodule K ((List Window × Fin 2) → K) :=
  Submodule.span K (Set.range (jointResidual K f))

/-- All future observations of a state in an arbitrary representation. -/
def futureObservation {V : Type*} [AddCommGroup V] [Module K V]
    (R : WordRepresentation K Window V (K × K)) :
    V →ₗ[K] ((List Window × Fin 2) → K) :=
  LinearMap.pi fun t => (channel K t.2).comp (R.output.comp (wordMap R.transition t.1))

/-- The same four actual histories work over every characteristic-two field. -/
def prefixes : Fin 4 → List Window := ![[], [.middle], [.low], [.middle, .low]]

/-- Each of two continuations is queried through both output channels. -/
def tests : Fin 4 → List Window × Fin 2 :=
  ![([.high], 0), ([.high], 1), ([.zero, .high], 0), ([.zero, .high], 1)]

/-- Tests index rows and actual histories index columns. -/
def responseMinor : Matrix (Fin 4) (Fin 4) K :=
  fun i j => jointResidual K (integerFieldTask K) (prefixes j) (tests i)

private theorem wordMap_append {V : Type*} [AddCommGroup V] [Module K V]
    (T : Window → V →ₗ[K] V) (u v : List Window) :
    wordMap T (u ++ v) = (wordMap T v).comp (wordMap T u) := by
  have productAppend (a c : List Window) :
      wordOperator T (a ++ c) = (wordOperator T a).comp (wordOperator T c) := by
    induction a with
    | nil => simp [wordOperator]
    | cons b a ih => simp only [List.cons_append, wordOperator, ih, LinearMap.comp_assoc]
  simpa only [wordMap, List.reverse_append] using productAppend v.reverse u.reverse

/-- In characteristic two the actual integer process is realized on K⁴ on
every finite word. Its joint two-channel residual span is finite dimensional
of dimension four, which is also a lower bound for every finite-dimensional
linear representation of the same task. No reachability hypothesis is used. -/
theorem result [CharP K 2] :
    (∀ w : List Window,
      wordBehavior (fourDimensional K) w = integerFieldTask K w) ∧
    FiniteDimensional K (jointHankelSpace K (integerFieldTask K)) ∧
    Module.finrank K (jointHankelSpace K (integerFieldTask K)) = 4 ∧
    Module.finrank K (BlockState K) = 4 ∧
    (∀ (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (R : WordRepresentation K Window V (K × K)),
      (∀ w : List Window, wordBehavior R w = integerFieldTask K w) →
        4 ≤ Module.finrank K V) := by
  classical
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have clock_second (x : ℤ × ℤ) :
      (Int.cast ((clock (m := 0) x).2 : ℤ) : K) = (x.2 : K) := by
    simp only [clock, step, Int.cast_add]
    linear_combination ((x.1 : K) + (x.2 : K)) * htwo
  have commute (q : RawState 0) (b : Window) :
      blockTransition K b (embed K q) = embed K (rawTransition q b) := by
    cases q with
    | none => cases b <;> ext i <;> fin_cases i <;>
        simp [blockTransition, blockUpdate, embed, rawTransition]
    | some q =>
      rcases q with ⟨s, a, c⟩
      cases s <;> cases b <;> ext i <;> fin_cases i <;>
        simp [blockTransition, blockUpdate, embed, rawTransition, first, last,
          displacement, clock_second]
  have simulation (w : List Window) (q : RawState 0) :
      wordMap (blockTransition K) w (embed K q) =
        embed K ((rawMachine 0).toDFA.evalFrom q w) := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w b ih =>
      simp only [wordMap, List.reverse_append, List.reverse_singleton,
        List.singleton_append, wordOperator, LinearMap.comp_apply,
        DFA.evalFrom_append_singleton]
      change blockTransition K b (wordMap (blockTransition K) w (embed K q)) =
        embed K (rawTransition ((rawMachine 0).toDFA.evalFrom q w) b)
      rw [ih, commute]
  have observe (q : RawState 0) :
      blockOutput K (embed K q) =
        match rawOutput q with
        | none => (0, 0)
        | some z => (1, Int.cast (z : ℤ)) := by
    cases q with
    | none => simp [blockOutput, embed, rawOutput]
    | some q =>
      rcases q with ⟨s, a, c⟩
      cases s <;> simp [blockOutput, embed, rawOutput, quantity, Int.cast_add,
        Int.cast_mul, htwo]
      all_goals linear_combination (c : K) * htwo
  have upper (w : List Window) :
      wordBehavior (fourDimensional K) w = integerFieldTask K w := by
    change blockOutput K
      (wordMap (blockTransition K) w (embed K (some (false, (0, 0))))) = _
    rw [simulation, observe]
    change (match task 0 w with
      | none => (0, 0)
      | some z => (1, Int.cast (z : ℤ))) = _
    cases h : task 0 w <;> simp [integerFieldTask, integerTask, h]
  have residual_factor (u : List Window) :
      jointResidual K (integerFieldTask K) u =
        futureObservation K (fourDimensional K)
          (wordMap (blockTransition K) u (fourDimensional K).initial) := by
    ext t
    rw [jointResidual, ← upper]
    simp only [wordBehavior, wordMap_append, LinearMap.comp_apply,
      futureObservation, LinearMap.pi_apply]
    rfl
  have contained : jointHankelSpace K (integerFieldTask K) ≤
      LinearMap.range (futureObservation K (fourDimensional K)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    exact ⟨wordMap (blockTransition K) u (fourDimensional K).initial,
      (residual_factor u).symm⟩
  have finite : FiniteDimensional K (jointHankelSpace K (integerFieldTask K)) :=
    Submodule.finiteDimensional_of_le contained
  haveI := finite
  have dimension_upper : Module.finrank K (jointHankelSpace K (integerFieldTask K)) ≤ 4 := by
    calc
      _ ≤ Module.finrank K (LinearMap.range (futureObservation K (fourDimensional K))) :=
        Submodule.finrank_mono contained
      _ ≤ Module.finrank K (BlockState K) := LinearMap.finrank_range_le _
      _ = 4 := by simp [BlockState]
  have minor : responseMinor K =
      !![1, 1, 0, 0; 1, 0, 0, 0; 1, 1, 1, 1; 1, 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [responseMinor, jointResidual, prefixes, tests, channel, ← upper,
        wordBehavior, fourDimensional, wordMap, wordOperator, blockTransition,
        blockUpdate, blockOutput] <;> exact htwo
  have detValue : (responseMinor K).det = 1 := by
    rw [minor]
    norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_three, Fin.sum_univ_succ]
  have columns : LinearIndependent K (responseMinor K).col :=
    Matrix.linearIndependent_cols_of_det_ne_zero (by rw [detValue]; exact one_ne_zero)
  let sample : ((List Window × Fin 2) → K) →ₗ[K] (Fin 4 → K) :=
    LinearMap.pi fun i => LinearMap.proj (tests i)
  let rows : Fin 4 → jointHankelSpace K (integerFieldTask K) := fun j =>
    ⟨jointResidual K (integerFieldTask K) (prefixes j),
      Submodule.subset_span ⟨prefixes j, rfl⟩⟩
  have independent_rows : LinearIndependent K rows := by
    let observation := sample.comp (jointHankelSpace K (integerFieldTask K)).subtype
    have factor : observation ∘ rows = (responseMinor K).col := by rfl
    exact (factor.symm ▸ columns).of_comp observation
  have dimension_lower : 4 ≤ Module.finrank K (jointHankelSpace K (integerFieldTask K)) := by
    simpa using independent_rows.fintype_card_le_finrank
  refine ⟨upper, finite, Nat.le_antisymm dimension_upper dimension_lower,
    by simp [BlockState], ?_⟩
  intro V _ _ _ R correct
  let reach : Fin 4 → V := fun j => wordMap R.transition (prefixes j) R.initial
  let observation := sample.comp (futureObservation K R)
  have factor : observation ∘ reach = (responseMinor K).col := by
    ext j i
    change channel K (tests i).2
      (R.output (wordMap R.transition (tests i).1
        (wordMap R.transition (prefixes j) R.initial))) = _
    change channel K (tests i).2
      (R.output (((wordMap R.transition (tests i).1).comp
        (wordMap R.transition (prefixes j))) R.initial)) = _
    rw [← wordMap_append]
    exact congrArg (channel K (tests i).2) (correct (prefixes j ++ (tests i).1))
  have independent_states : LinearIndependent K reach :=
    (factor.symm ▸ columns).of_comp observation
  simpa using independent_states.fintype_card_le_finrank

end D5.S3.Arith.FibonacciAtomic.LinearRealization.WindowCharTwoMinimum
