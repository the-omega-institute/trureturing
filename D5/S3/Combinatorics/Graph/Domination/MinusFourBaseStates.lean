/- GID: D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/MinusFourBaseStates
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Local weighted domination states of the eight actual source components. -/

import D5.S3.Combinatorics.Graph.Domination.MinusFourFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.MinusFourBaseStates

open Finset DominatingSetAverage MinusFourReplication MinusFourFamily

/-- Component sizes after removing the actual four-cycle. -/
def branchSize : Fin 8 → ℕ := ![2,2,2,2,6,3,3,9]

/-- Each component occupies an interval in the published vertex labels. -/
def branchStart : Fin 8 → ℕ := ![4,6,8,10,12,18,21,24]

private theorem branch_bound : ∀ i : Fin 8, branchStart i + branchSize i ≤ 33 := by decide

/-- Exact source labels, with no vertices added or discarded. -/
def branchLabel (i : Fin 8) (v : Fin (branchSize i)) : Fin 33 :=
  ⟨branchStart i + v.val, by have := branch_bound i; omega⟩

/-- Internal adjacency is pulled back from the actual source edges. -/
def branchGraph (i : Fin 8) : SimpleGraph (Fin (branchSize i)) :=
  sourceGraph.comap (branchLabel i)

instance (i : Fin 8) : DecidableRel (branchGraph i).Adj := fun _ _ => inferInstanceAs
  (Decidable (sourceGraph.Adj _ _))

/-- The root is the first vertex of every interval. -/
def root (i : Fin 8) : Fin (branchSize i) :=
  ⟨0, by fin_cases i <;> decide⟩

/-- A computationally transparent form of ordinary internal domination. -/
def localDominating (i : Fin 8) (S : Finset (Fin (branchSize i))) : Prop :=
  ∀ v, v ∈ S ∨ ∃ w ∈ S, (branchGraph i).Adj v w

instance (i : Fin 8) (S : Finset (Fin (branchSize i))) : Decidable (localDominating i S) := by
  unfold localDominating
  infer_instance

/-- Root-selected and root-omitted internally dominating configurations. -/
def message (i : Fin 8) (b : Bool) : ℤ :=
  ∑ S ∈ (univ : Finset (Fin (branchSize i))).powerset,
    if localDominating i S ∧ decide (root i ∈ S) = b then (-4 : ℤ) ^ S.card else 0

/-- Core neighbors of each component root. -/
def rootNeighbors : Fin 8 → Finset (Fin 4) :=
  ![{0},{2},{2},{2},{0,1},{1,2},{2,3},{3}]

/-- The four-cycle is covered by core choices and selected component roots. -/
def coreCovered (Z : Finset (Fin 4)) (A : Finset (Fin 8)) : Prop :=
  ∀ c : Fin 4, c ∈ Z ∨
    (∃ d ∈ Z, sourceGraph.Adj ⟨c.val, by omega⟩ ⟨d.val, by omega⟩) ∨
    ∃ i ∈ A, c ∈ rootNeighbors i

instance (Z : Finset (Fin 4)) (A : Finset (Fin 8)) : Decidable (coreCovered Z A) := by
  unfold coreCovered
  infer_instance

/-- The finite core-and-root expression whose exact reassembly bridge is required. -/
def stateEvaluation : ℤ :=
  ∑ Z ∈ (univ : Finset (Fin 4)).powerset,
    (-4 : ℤ) ^ Z.card *
      ∑ A ∈ (univ : Finset (Fin 8)).powerset,
        if coreCovered Z A then ∏ i : Fin 8, message i (decide (i ∈ A)) else 0

private def messageTable (i : Fin 8) (b : Bool) : ℤ :=
  if b then ![12,12,12,12,972,-36,-36,-20736] i
  else ![-4,-4,-4,-4,-1024,16,16,5888] i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem local_messages : ∀ (i : Fin 8) (b : Bool), message i b = messageTable i b := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem core_cancellation :
    (∑ Z ∈ (univ : Finset (Fin 4)).powerset,
      (-4 : ℤ) ^ Z.card *
        ∑ A ∈ (univ : Finset (Fin 8)).powerset,
          if coreCovered Z A then ∏ i : Fin 8, messageTable i (decide (i ∈ A)) else 0) = 0 := by
  decide

/-- This reduction consumes the small kernel computations but leaves the exact
restriction/reassembly equality explicit until that equality has a proof. -/
theorem result_of_reassembly (hbridge : evaluation sourceGraph (-4) = stateEvaluation) :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ G : SimpleGraph (Fin n),
      G.Connected ∧ ∑ S ∈ domSets G, (-4 : ℤ) ^ S.card = 0 := by
  apply result_of_base_root
  rw [hbridge]
  unfold stateEvaluation
  simp_rw [local_messages]
  exact core_cancellation

end D5.S3.Combinatorics.Graph.Domination.MinusFourBaseStates
