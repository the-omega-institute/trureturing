/- GID: D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace
   mirror-E: none(waiver:no-numerical-evidence)
   anchors: []
   utility: none
   digest: Boolean run languages, coherent prefixes and the fair independent product law. -/

import D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import Mathlib.Probability.Independence.InfinitePi


namespace D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
open D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

abbrev Stream := Nat → Bool
abbrev Word (n : Nat) := Fin n → Bool

/-- A readout is applied to each actual coordinate bit. -/
def bounded (read : Bool → Bool) (k : Nat) : Set Stream :=
  {x | ∀ j, ∃ i : Fin k, read (x (j + i)) = false}

def language (read : Bool → Bool) (k n : Nat) : Set (Word n) :=
  {w | ∀ j (h : j + k ≤ n), ∃ i : Fin k,
    read (w ⟨j + i, by omega⟩) = false}

def union (read : Bool → Bool) : Set Stream := ⋃ k ≥ 2, bounded read k

def truncate {m n : Nat} (h : m ≤ n) (w : Word n) : Word m :=
  fun i => w ⟨i, lt_of_lt_of_le i.isLt h⟩

def zeroExtend {n : Nat} (w : Word n) : Stream :=
  fun j => if h : j < n then w ⟨j, h⟩ else false

/-- All inverse limits below are subsets of this one coherent-prefix space. -/
def Threads := {w : ∀ n, Word n | ∀ n, truncate (Nat.le_succ n) (w (n + 1)) = w n}

def prefixes (x : Stream) : Threads := ⟨fun n => finiteTranscript n x, fun _ => rfl⟩

def threadStream (w : Threads) : Stream := fun j => w.val (j + 1) ⟨j, by omega⟩

def fixedLimit (read : Bool → Bool) (k : Nat) : Set Threads :=
  {w | ∀ n, w.val n ∈ language read k n}

def unionLimits (read : Bool → Bool) : Set Threads := ⋃ k ≥ 2, fixedLimit read k

def limitUnions (read : Bool → Bool) : Set Threads :=
  {w | ∀ n, ∃ k ≥ 2, w.val n ∈ language read k n}

def comparison (read : Bool → Bool) : unionLimits read → limitUnions read := fun w =>
  ⟨w.val, by
    rcases mem_iUnion.mp w.property with ⟨k, hk⟩
    rcases mem_iUnion.mp hk with ⟨hk, hw⟩
    exact fun n => ⟨k, hk, hw n⟩⟩

noncomputable def fairBias : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

noncomputable abbrev fairMeasure : Measure Stream := productLaw fairBias

def aligned (read : Bool → Bool) (k m : Nat) : Set Stream :=
  {x | ∀ r : Fin m, ∃ i : Fin k, read (x (r * k + i)) = false}

/-- The complete boundary, with the comparison map on coherent prefixes retained. -/
def Boundary (read : Bool → Bool) : Prop :=
  (∀ k, 2 ≤ k → IsClosed (bounded read k) ∧ bounded read k ⊂ bounded read (k + 1)) ∧
  (∀ k, 2 ≤ k → ∀ n, finiteTranscript n '' bounded read k = language read k n) ∧
  (∀ k n, n < k → language read k n = univ) ∧
  (∀ k n, language read k n ⊆ language read (k + 1) n) ∧
  (∀ k m n (h : m ≤ n), truncate h '' language read k n ⊆ language read k m) ∧
  (union read).Nonempty ∧ Dense (union read) ∧ union read ⊂ univ ∧
  MeasurableSet (union read) ∧ (∀ n, finiteTranscript n '' union read = univ) ∧
  closure (union read) = univ ∧
  (∀ k, 2 ≤ k → fairMeasure (bounded read k) = 0) ∧
  fairMeasure (union read) = 0 ∧ fairMeasure (closure (union read)) = 1 ∧
  Function.Bijective prefixes ∧ Continuous prefixes ∧ Continuous threadStream ∧
  (∀ w : Threads, prefixes (threadStream w) = w) ∧
  (∀ k x, x ∈ bounded read k ↔ prefixes x ∈ fixedLimit read k) ∧
  prefixes '' union read = unionLimits read ∧ limitUnions read = univ ∧
  Function.Injective (comparison read) ∧ ¬ Function.Surjective (comparison read) ∧
  (∀ w : unionLimits read, threadStream (comparison read w).val = threadStream w.val) ∧
  union read = {x | ∃ k ≥ 2, ∀ n, finiteTranscript n x ∈ language read k n} ∧
  {x : Stream | ∀ n, ∃ k ≥ 2, finiteTranscript n x ∈ language read k n} = univ ∧
  (∀ k m, 2 ≤ k → bounded read k ⊆ aligned read k m ∧
    fairMeasure (aligned read k m) = (1 - (2 : ℝ≥0∞)⁻¹ ^ k) ^ m)

def bitArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := Boundary (r.readout ())

def bitRealization := cutRealization (fun b : Bool => b)


end D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace
