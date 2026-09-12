/- GID: D5/S3/ConceptDynamics/Observation/ContextDepthBoundary
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Observation/ContextDepthBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Observation/ContextDepthBoundary.DepthAdequacyClaim; result=D5/S3/ConceptDynamics/Observation/ContextDepthBoundary.depth_adequacy_refutation; claim=D5/S3/ConceptDynamics/Observation/ContextDepthBoundary.DepthAdequacyClaim
   digest: Finite depth can miss a distinction and fail to preserve the unary operation. -/

import D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
import D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Observation.ContextDepthBoundary

open D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization

/-- Two disjoint chains, each including its stopped endpoint. -/
def Chain (k : Nat) := Bool × Fin (k + 2)

/-- Advance within a branch, stopping at its endpoint. -/
def update (k : Nat) (_ : Unit) (x : Chain k) : Chain k :=
  (x.1, ⟨min (x.2.val + 1) (k + 1), by omega⟩)

/-- Only the endpoint of the true branch has readout one. -/
def readout (k : Nat) (x : Chain k) : Bool := x.1 && (x.2.val == k + 1)

/-- The single total unary operation on the two chains. -/
def signature (k : Nat) : PartialSignature (Chain k) Unit :=
  ⟨fun _ => 1, fun _ a => some (update k () (a 0))⟩

/-- The initial state of either chain. -/
def start (k : Nat) (branch : Bool) : Chain k := (branch, ⟨0, by omega⟩)

private def generator (k : Nat) : Generator (signature k) :=
  ⟨(), (0 : Fin 1), fun j => False.elim (j.property (Fin.eq_zero j.val))⟩

private theorem generator_unique (k : Nat) (g : Generator (signature k)) :
    g = generator k := by
  obtain ⟨⟨⟩, slot, parameters⟩ := g
  have hs : slot = (0 : Fin 1) := Fin.eq_zero slot
  subst slot
  congr
  funext j
  exact False.elim (j.property (Fin.eq_zero j.val))

private theorem context_word (k : Nat) (word : List (Generator (signature k)))
    (x : Chain k) :
    contextDenote (signature k) word x =
      some (runWord (update k) (word.map fun _ => ()) x) := by
  induction word generalizing x with
  | nil => rfl
  | cons g word ih =>
    rw [generator_unique k g]
    change contextDenote (signature k) word (update k () x) =
      some (runWord (update k) (word.map fun _ => ()) (update k () x))
    exact ih _

private theorem stopped_chain_runWord (k : Nat) (word : List Unit) (x : Chain k) :
    (runWord (update k) word x).1 = x.1 ∧
    (runWord (update k) word x).2.val = min (x.2.val + word.length) (k + 1) := by
  induction word generalizing x with
  | nil =>
    refine ⟨rfl, ?_⟩
    have hx := x.2.isLt
    simp only [runWord, List.length_nil, Nat.add_zero]
    omega
  | cons u word ih =>
    obtain ⟨branch, position⟩ := ih (update k u x)
    refine ⟨branch, ?_⟩
    simp only [runWord, List.length_cons]
    rw [position]
    change min (min (x.2.val + 1) (k + 1) + word.length) (k + 1) =
      min (x.2.val + (word.length + 1)) (k + 1)
    omega

/-- Depth-limited agreement tests every word of that length or less. -/
def AtDepth (k depth : Nat) (x y : Chain k) : Prop :=
  boundedWordEquivalent (update k) (readout k) depth x y

/-- Depth k would be complete if it detected all actual one-hole observations. -/
def CompleteAt (k : Nat) : Prop :=
  ∀ x y : Chain k, AtDepth k k x y → (contextualSetoid (signature k) (readout k)).r x y

/-- Depth k would be stable if the unary operation preserved it. -/
def StableAt (k : Nat) : Prop :=
  ∀ x y : Chain k, AtDepth k k x y → AtDepth k k (update k () x) (update k () y)

/-- The claim that some member's designated depth is complete or stable. -/
def DepthAdequacyClaim : Prop := (∃ k : Nat, CompleteAt k) ∨ (∃ k : Nat, StableAt k)

private theorem read_word (k : Nat) (word : List Unit) (x : Chain k) :
    readout k (runWord (update k) word x) =
      (x.1 && (min (x.2.val + word.length) (k + 1) == k + 1)) := by
  obtain ⟨hb, hp⟩ := stopped_chain_runWord k word x
  simp only [readout, hb, hp]

/-- At every k, the starts agree through k, separate at k+1, and their
successors already separate through k. All words denote actual contexts. -/
theorem stopped_chain_boundary (k : Nat) :
    AtDepth k k (start k true) (start k false) ∧
    (∀ word : List (Generator (signature k)), word.length ≤ k →
      contextObserve (readout k) (contextDenote (signature k) word) (start k true) =
        contextObserve (readout k) (contextDenote (signature k) word) (start k false)) ∧
    (∃ word : List (Generator (signature k)), word.length = k + 1 ∧
      contextObserve (readout k) (contextDenote (signature k) word) (start k true) = some true ∧
      contextObserve (readout k) (contextDenote (signature k) word) (start k false) = some false) ∧
    ¬ AtDepth k k (update k () (start k true)) (update k () (start k false)) := by
  have agree : AtDepth k k (start k true) (start k false) := by
    intro word hw
    rw [read_word, read_word]
    simp [start]
    omega
  refine ⟨agree, ?_, ?_, ?_⟩
  · intro word hw
    simp only [contextObserve, context_word, Option.map_some]
    exact congrArg some (agree (word.map fun _ => ()) (by simpa using hw))
  · refine ⟨List.replicate (k + 1) (generator k), by simp, ?_, ?_⟩ <;>
      simp only [contextObserve, context_word, Option.map_some] <;>
      rw [read_word] <;> simp [start]
  · intro stable
    have h := stable (List.replicate k ()) (by simp)
    rw [read_word, read_word] at h
    simp [update, start] at h
    omega

/-- No designated finite depth in this family is complete or operation-stable. -/
theorem depth_adequacy_refutation : Not DepthAdequacyClaim := by
  intro claim
  rcases claim with ⟨k, complete⟩ | ⟨k, stable⟩
  · obtain ⟨agree, _, ⟨word, _, ha, hb⟩, _⟩ := stopped_chain_boundary k
    have equal := (forall_contexts_iff_words (signature k) (readout k) _ _).mp
      (complete _ _ agree) word
    rw [ha, hb] at equal
    cases equal
  · obtain ⟨agree, _, _, nonstable⟩ := stopped_chain_boundary k
    exact nonstable (stable _ _ agree)

end D5.S3.ConceptDynamics.Observation.ContextDepthBoundary
