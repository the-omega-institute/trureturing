/- GID: D5/S1/Digit/GoldenBase4ZeroResponse
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenBase4ZeroResponse
   mirror-E: none(waiver:exact-labelled-response-minor)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   digest: The existing golden base-four machine has fourteen independent joint zero responses, certified by an integer-valued inverse and tied to its original transition table. -/

import D5.S0.Certificates.SkeletonSlotZeroResponse
import D5.S1.Digit.GoldenBase4IntervalMachine

/- This is a fixed labelled-profile result. Correctness on powers alone does
   not prescribe the slot readouts used here. The same reference matrix must
   not be inserted as oracle data for other candidates. The generic companion
   instead imposes rank constraints on each candidate's own completion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenBase4ZeroResponse

open D5.S0.Automata.BinaryZeckendorfBlockSkeleton
open D5.S0.Certificates.SkeletonSlotCNF
open D5.S0.Certificates.SkeletonSlotZeroResponse

/-- Embedding the previous-zero carrier into the existing full machine. -/
def recurrent (q : Fin 14) : Fin 21 := ⟨q.val, Nat.lt_trans q.isLt (by decide)⟩

/-- Embedding the seven transient slots into the existing full machine. -/
def transient (t : Fin 7) : Fin 21 := ⟨14 + t.val, by have := t.isLt; omega⟩

/-- The recurrent zero row of the already specified full table. -/
def zero : Fin 14 → Fin 14 := ![0,9,8,7,7,6,5,5,4,4,3,2,2,1]

/-- Slot requested by each recurrent one edge. -/
def select : Fin 14 → Fin 7 := ![4,6,5,5,4,4,4,3,3,2,1,1,0,0]

/-- Return target of each existing transient slot. -/
def returnTo : Fin 7 → Fin 14 := ![13,12,12,11,10,9,9]

/-- The displayed zero table is exactly the original machine's row. -/
theorem zero_matches : ∀ q : Fin 14,
    GoldenBase4IntervalMachine.machine.step (recurrent q) 0 =
      some (recurrent (zero q)) := by decide

/-- The selector table agrees with the original machine's one transitions. -/
theorem select_matches : ∀ q : Fin 14,
    GoldenBase4IntervalMachine.machine.step (recurrent q) 1 =
      some (transient (select q)) := by decide

/-- The slot returns agree with the original machine's zero transitions. -/
theorem return_matches : ∀ t : Fin 7,
    GoldenBase4IntervalMachine.machine.step (transient t) 0 =
      some (recurrent (returnTo t)) := by decide

/-- Original outputs are reused without a second digit oracle. -/
def skeleton : Skeleton (Fin 4) (Fin 14) where
  start := 0
  zeroStep := fun q => some (zero q)
  oneSignature := fun q => some
    (GoldenBase4IntervalMachine.machine.output (transient (select q)),
      some (returnTo (select q)))
  zeroOutput := fun q => GoldenBase4IntervalMachine.machine.output (recurrent q)

/-- An explicit serialization in the existing slot witness type. -/
def slots : SlotWitness skeleton 7 where
  zeroTarget := zero
  slotOf := select
  returnTarget := returnTo
  transientOutput := fun t => GoldenBase4IntervalMachine.machine.output (transient t)
  zero_eq := fun _ => rfl
  one_eq := fun _ => rfl

/-- Row origins: the initial state followed by named transient returns. -/
def origin : Fin 14 → Fin 14 := ![0,13,12,10,9,13,13,9,12,9,10,11,12,13]

/-- Number of zeroes after the row origin. -/
def rowDelay : Fin 14 → Nat := ![0,1,1,1,1,5,6,2,2,0,0,0,0,0]

/-- Column zero depths; only depths zero through three are needed. -/
def columnDelay : Fin 14 → Nat := ![0,0,0,1,0,0,0,0,0,0,1,1,2,3]

/-- Joint probes distinguish output digits and selected transient slots. -/
def test : Fin 14 → Fin 4 ⊕ Fin 7 := ![.inl 0,.inl 1,.inl 3,.inl 0,.inr 0,.inr 1,.inr 2,.inr 3,.inr 4,.inr 5,.inr 3,.inr 5,.inr 3,.inr 3]

/-- Every recurrent state has the recorded access by a transient return or start. -/
theorem access_exhausts_recurrent : ∀ i : Fin 14,
    advance slots (rowDelay i) (origin i) = i := by decide

/-- This matrix is computed from the existing machine, not assumed data. -/
def profileMinor : Matrix (Fin 14) (Fin 14) Rat :=
  response slots origin rowDelay columnDelay test

/-- An exact integer-valued right inverse; no approximate rank is used. -/
def profileInverse : Matrix (Fin 14) (Fin 14) Rat := ![
    ![0,1,-1,1,0,-1,1,0,0,0,0,0,0,0],
    ![0,1,-1,1,0,-1,1,0,0,0,-1,1,0,0],
    ![-1,1,-1,1,0,0,1,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,-1,0,0,0,0,0,0,0],
    ![0,-1,1,-1,0,1,-1,0,0,0,1,-1,0,1],
    ![0,-1,1,-1,0,1,-1,0,0,0,1,0,-1,1],
    ![0,-1,1,-1,0,1,-1,1,-1,1,0,0,0,0],
    ![0,-1,1,-1,0,1,-1,1,0,0,0,0,0,0],
    ![0,-1,1,-1,0,1,0,0,0,0,0,0,0,0],
    ![0,-1,1,0,-1,1,0,0,0,0,0,0,0,0],
    ![0,0,0,0,1,-1,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,1,-1,0,0,0,1,-1],
    ![0,0,0,0,0,0,0,-1,1,0,0,0,0,0],
    ![0,0,1,-1,0,0,0,0,0,0,0,0,0,0]]

/-- Finite rational calculation certifies the whole matrix product. -/
theorem profile_inverse_certificate : profileMinor * profileInverse = 1 := by decide

/-- Fourteen independent responses are forced for this labelled profile. -/
theorem profile_rank_fourteen : profileMinor.rank = 14 := by
  apply Nat.le_antisymm (Matrix.rank_le_width profileMinor)
  have h := Matrix.rank_mul_le_left profileMinor profileInverse
  simpa only [profile_inverse_certificate, Matrix.rank_one, Fintype.card_fin] using h

/-- Any deterministic slot realization of the same labelled profile requires
at least fourteen recurrent states. This premise is stronger than fitting powers. -/
theorem same_profile_recurrent_lower_bound {r : Nat}
    {K : Skeleton (Fin 4) (Fin r)} (W : SlotWitness K 7)
    (candidateOrigin : Fin 14 → Fin r)
    (same : response W candidateOrigin rowDelay columnDelay test = profileMinor) :
    14 ≤ r := by
  have h := response_rank_le W candidateOrigin rowDelay columnDelay test
  rw [same, profile_rank_fourteen] at h
  exact h

#print axioms profile_inverse_certificate
#print axioms profile_rank_fourteen
#print axioms same_profile_recurrent_lower_bound

end D5.S1.Digit.GoldenBase4ZeroResponse
