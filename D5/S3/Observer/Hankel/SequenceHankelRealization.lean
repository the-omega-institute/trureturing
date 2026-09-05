/- GID: D5/S3/Observer/Hankel/SequenceHankelRealization
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/SequenceHankelRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite-dimensional span of data tails yields an attained minimal realization. -/

import D5.S3.Observer.Hankel.HankelMinimalStateDimension
import Mathlib.LinearAlgebra.Dimension.Constructions

/- Library search (2026-09-05): the imported D5 owner constructs the minimal
   quotient of an already supplied realization. It does not construct a
   realization from a sequence. Reuse its FiniteLinearRealization bundle,
   markovParameter, reachableSubspace, eventualKernel and stable-Hankel theorem.
   Pinned Mathlib supplies span, linear-map ranges, finiteDimensional_of_le,
   finrank_mono and rank-nullity. No diagonalization or modal decomposition is
   assumed here. Finite rank means finite-dimensional tail span; unguarded
   natural-valued finrank is not used as a test for finite dimensionality. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.SequenceHankelRealization

open Module
open D5.S3.Observer.Hankel.HankelRankMinimality
open D5.S3.Observer.Hankel.HankelMinimalStateDimension
open D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability
open D5.S3.Observer.LinearMemory.ZeroMemoryCriterion

universe u

variable {K U Y : Type u} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup Y] [Module K Y]

/-- The future output after an input direction at age `j`, defined from data. -/
def dataTail (m : ℕ → (U →ₗ[K] Y)) (j : ℕ) (input : U) : ℕ → Y :=
  fun i => m (i + j) input

/-- The column span of the infinite block Hankel object of the data. -/
def tailSpace (m : ℕ → (U →ₗ[K] Y)) : Submodule K (ℕ → Y) :=
  Submodule.span K (Set.range fun p : ℕ × U => dataTail m p.1 p.2)

/-- A one-step left shift on output sequences. -/
def sequenceShift : (ℕ → Y) →ₗ[K] (ℕ → Y) where
  toFun x := fun i => x (i + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem shift_dataTail (m : ℕ → (U →ₗ[K] Y)) (j : ℕ) (input : U) :
    sequenceShift (K := K) (dataTail m j input) = dataTail m (j + 1) input := by
  funext i
  change m (i + 1 + j) input = m (i + (j + 1)) input
  have index : i + 1 + j = i + (j + 1) := by omega
  rw [index]

private theorem shift_mem_tailSpace (m : ℕ → (U →ₗ[K] Y))
    {x : ℕ → Y} (hx : x ∈ tailSpace m) : sequenceShift (K := K) x ∈ tailSpace m := by
  have invariant : tailSpace m ≤ (tailSpace m).comap (sequenceShift (K := K)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨j, input⟩, rfl⟩
    change sequenceShift (K := K) (dataTail m j input) ∈ tailSpace m
    rw [shift_dataTail]
    exact Submodule.subset_span ⟨(j + 1, input), rfl⟩
  exact invariant hx

/-- A data tail as an actual state in the canonical carrier. -/
def tailState (m : ℕ → (U →ₗ[K] Y)) (j : ℕ) (input : U) : tailSpace m :=
  ⟨dataTail m j input, Submodule.subset_span ⟨(j, input), rfl⟩⟩

/-- Dynamics constructed by restricting the shift to the data-tail span. -/
def sequenceDynamics (m : ℕ → (U →ₗ[K] Y)) : tailSpace m →ₗ[K] tailSpace m where
  toFun x := ⟨sequenceShift (K := K) x, shift_mem_tailSpace m x.property⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

/-- The input injects the unshifted future output sequence. -/
def sequenceInput (m : ℕ → (U →ₗ[K] Y)) : U →ₗ[K] tailSpace m where
  toFun input := tailState m 0 input
  map_add' x y := by
    apply Subtype.ext
    funext i
    exact (m (i + 0)).map_add x y
  map_smul' scalar x := by
    apply Subtype.ext
    funext i
    exact (m (i + 0)).map_smul scalar x

/-- Read the present coordinate of a state. -/
def sequenceOutput (m : ℕ → (U →ₗ[K] Y)) : tailSpace m →ₗ[K] Y where
  toFun x := x.val 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The constructed dynamics really advances every future coordinate. -/
theorem sequenceDynamics_pow_apply (m : ℕ → (U →ₗ[K] Y))
    (n : ℕ) (x : tailSpace m) (i : ℕ) :
    ((sequenceDynamics m ^ n) x).val i = x.val (i + n) := by
  induction n generalizing i with
  | zero =>
      change x.val i = x.val (i + 0)
      rw [Nat.add_zero]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      change ((sequenceDynamics m ^ n) x).val (i + 1) = x.val (i + (n + 1))
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1)

/-- Each input iterate is the corresponding data tail. -/
theorem sequenceDynamics_pow_input (m : ℕ → (U →ₗ[K] Y)) (n : ℕ) (input : U) :
    (sequenceDynamics m ^ n) (sequenceInput m input) = tailState m n input := by
  apply Subtype.ext
  funext i
  rw [sequenceDynamics_pow_apply]
  rfl

/-- Every future observation of a canonical state is its corresponding coordinate. -/
theorem sequenceOutput_pow (m : ℕ → (U →ₗ[K] Y)) (n : ℕ) (x : tailSpace m) :
    sequenceOutput m ((sequenceDynamics m ^ n) x) = x.val n := by
  change ((sequenceDynamics m ^ n) x).val 0 = x.val n
  simpa only [Nat.zero_add] using sequenceDynamics_pow_apply m n x 0

/-- The construction reproduces all of the input data, not only a finite sample. -/
theorem sequence_markovParameter_eq (m : ℕ → (U →ₗ[K] Y)) (n : ℕ) :
    markovParameter (sequenceDynamics m) (sequenceInput m) (sequenceOutput m) n =
      m n := by
  ext input
  change sequenceOutput m ((sequenceDynamics m ^ n) (sequenceInput m input)) =
    m n input
  rw [sequenceOutput_pow]
  rfl

/-- The data-tail carrier has no unreachable directions. -/
theorem sequence_reachable_eq_top (m : ℕ → (U →ₗ[K] Y)) :
    reachableSubspace (sequenceDynamics m) (sequenceInput m) = ⊤ := by
  let R := reachableSubspace (sequenceDynamics m) (sequenceInput m)
  have generated : tailSpace m ≤ R.map (tailSpace m).subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨j, input⟩, rfl⟩
    refine ⟨tailState m j input, ?_, rfl⟩
    rw [← sequenceDynamics_pow_input]
    exact Submodule.subset_span ⟨j, input, rfl⟩
  change R = ⊤
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨y, hy, heq⟩ := generated x.property
  have statesEqual : y = x := Subtype.ext heq
  exact statesEqual ▸ hy

/-- Distinct canonical states can always be distinguished at a finite future time. -/
theorem sequence_eventualKernel_eq_bot (m : ℕ → (U →ₗ[K] Y)) :
    eventualKernel (sequenceOutput m) (sequenceDynamics m) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have stateZero : x = 0 := by
    apply Subtype.ext
    funext n
    have coordinate := sequenceOutput_pow m n x
    rw [Module.End.pow_apply] at coordinate
    exact coordinate.symm.trans (hx n)
  exact Submodule.mem_bot.mpr stateZero

/-- The all-future observation map of an arbitrary competing state model. -/
def futureOutput {V : Type u} [AddCommGroup V] [Module K V]
    (A : V →ₗ[K] V) (C : V →ₗ[K] Y) : V →ₗ[K] (ℕ → Y) :=
  LinearMap.pi fun i => C.comp (A ^ i)

/-- Every realization must contain the complete data-tail span in its observation range. -/
theorem tailSpace_le_futureOutput_range
    (m : ℕ → (U →ₗ[K] Y)) {V : Type u} [AddCommGroup V] [Module K V]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (matches : ∀ n, markovParameter A B C n = m n) :
    tailSpace m ≤ LinearMap.range (futureOutput A C) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨j, input⟩, rfl⟩
  refine ⟨(A ^ j) (B input), ?_⟩
  funext i
  change C ((A ^ i) ((A ^ j) (B input))) = m (i + j) input
  calc
    _ = C ((A ^ (i + j)) (B input)) := by rw [pow_add, Module.End.mul_apply]
    _ = m (i + j) input := LinearMap.congr_fun (matches (i + j)) input

/-- A finite state realization forces finite rank of the infinite data Hankel object. -/
theorem finite_tailSpace_of_realization
    (m : ℕ → (U →ₗ[K] Y)) (system : FiniteLinearRealization K U Y)
    (matches : system.behavior = m) : FiniteDimensional K (tailSpace m) := by
  apply Submodule.finiteDimensional_of_le
    (tailSpace_le_futureOutput_range m system.dynamics system.input system.output
      (fun n => congrFun matches n))

/-- The data Hankel rank is a lower bound for every finite state realization. -/
theorem tailSpace_finrank_le_stateDimension
    (m : ℕ → (U →ₗ[K] Y)) (system : FiniteLinearRealization K U Y)
    (matches : system.behavior = m) :
    finrank K (tailSpace m) ≤ system.stateDimension := by
  calc
    finrank K (tailSpace m) ≤
        finrank K (LinearMap.range (futureOutput system.dynamics system.output)) :=
      Submodule.finrank_mono
        (tailSpace_le_futureOutput_range m system.dynamics system.input system.output
          (fun n => congrFun matches n))
    _ ≤ system.stateDimension := by
      exact (futureOutput system.dynamics system.output).finrank_range_le

/-- A finite realization constructed from finite-rank data without a supplied model. -/
def realizationFromSequence (m : ℕ → (U →ₗ[K] Y))
    [FiniteDimensional K (tailSpace m)] : FiniteLinearRealization K U Y where
  State := tailSpace m
  dynamics := sequenceDynamics m
  input := sequenceInput m
  output := sequenceOutput m

/-- Finite Hankel rank and the existence of a finite linear realization are equivalent. -/
theorem finite_tailSpace_iff_exists_realization (m : ℕ → (U →ₗ[K] Y)) :
    FiniteDimensional K (tailSpace m) ↔
      ∃ system : FiniteLinearRealization K U Y, system.behavior = m := by
  constructor
  · intro finite
    letI : FiniteDimensional K (tailSpace m) := finite
    refine ⟨realizationFromSequence m, ?_⟩
    funext n
    exact sequence_markovParameter_eq m n
  · rintro ⟨system, matches⟩
    exact finite_tailSpace_of_realization m system matches

/-- The constructed model attains the lower bound among all linear realizations. -/
theorem realizationFromSequence_is_minimal (m : ℕ → (U →ₗ[K] Y))
    [FiniteDimensional K (tailSpace m)] :
    (realizationFromSequence m).behavior = m ∧
    (realizationFromSequence m).stateDimension = finrank K (tailSpace m) ∧
    ∀ system : FiniteLinearRealization K U Y, system.behavior = m →
      (realizationFromSequence m).stateDimension ≤ system.stateDimension := by
  refine ⟨funext (sequence_markovParameter_eq m), rfl, ?_⟩
  intro system matches
  exact tailSpace_finrank_le_stateDimension m system matches

/-- The finite block Hankel map written directly from the data. -/
def dataHankel (m : ℕ → (U →ₗ[K] Y)) (rows columns : ℕ) :
    (Fin columns → U) →ₗ[K] (Fin rows → Y) :=
  LinearMap.pi fun row : Fin rows =>
    LinearMap.lsum K (fun _ : Fin columns => U) K fun column =>
      m ((row : ℕ) + (column : ℕ))

private theorem dataHankel_eq_canonical (m : ℕ → (U →ₗ[K] Y)) (rows columns : ℕ) :
    dataHankel m rows columns =
      finiteHankel (sequenceDynamics m) (sequenceInput m) (sequenceOutput m)
        rows columns := by
  simp only [dataHankel, finiteHankel, sequence_markovParameter_eq]

/-- Finite windows at least as large as the tail-space dimension attain that rank.
This consumes the existing stable-Hankel theorem on the newly constructed model. -/
theorem dataHankel_rank_eq_tailSpace (m : ℕ → (U →ₗ[K] Y))
    [FiniteDimensional K (tailSpace m)] (rows columns : ℕ)
    (rowsLarge : finrank K (tailSpace m) ≤ rows)
    (columnsLarge : finrank K (tailSpace m) ≤ columns) :
    finrank K (LinearMap.range (dataHankel m rows columns)) =
      finrank K (tailSpace m) := by
  rw [dataHankel_eq_canonical]
  rw [hankel_rank_eq_reachable_dim_sub_inter_unobservable_dim
    (sequenceDynamics m) (sequenceInput m) (sequenceOutput m)
    rows columns rowsLarge columnsLarge]
  rw [sequence_reachable_eq_top, sequence_eventualKernel_eq_bot]
  simp

/-- A compression below the minimal dimension loses a state direction that a
finite future output detects. The state is a finite linear combination of data
histories; the theorem does not assert a collision between two discrete words. -/
theorem smaller_compression_has_future_witness (m : ℕ → (U →ₗ[K] Y))
    [FiniteDimensional K (tailSpace m)]
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (compress : tailSpace m →ₗ[K] W)
    (smaller : finrank K W < finrank K (tailSpace m)) :
    ∃ x : tailSpace m, compress x = 0 ∧
      ∃ n : ℕ, sequenceOutput m ((sequenceDynamics m ^ n) x) ≠ 0 := by
  classical
  by_contra noWitness
  have kernelZero : LinearMap.ker compress = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have invisible : ∀ n : ℕ, sequenceOutput m ((sequenceDynamics m ^ n) x) = 0 := by
      intro n
      by_contra detected
      exact noWitness ⟨x, hx, n, detected⟩
    have stateZero : x = 0 := by
      apply Subtype.ext
      funext n
      simpa only [sequenceOutput_pow] using invisible n
    exact Submodule.mem_bot.mpr stateZero
  have dimensions := compress.finrank_range_add_finrank_ker
  rw [kernelZero, finrank_bot, Nat.add_zero] at dimensions
  have rankBound := (LinearMap.range compress).finrank_le
  omega

#print axioms finite_tailSpace_iff_exists_realization
#print axioms realizationFromSequence_is_minimal
#print axioms dataHankel_rank_eq_tailSpace
#print axioms smaller_compression_has_future_witness

end D5.S3.Observer.Hankel.SequenceHankelRealization
