/- GID: D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/GangulyCircuitAccess/Recovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.claim; result=D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.result; claim=D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.claim
   digest: A circuit-authorized player set lacks a recovery channel for the dealer-slice encoding. -/

import D5.S3.Quantum.Information.GangulyCircuitAccess.Encoding
import D5.S3.Quantum.Foundation.FiniteStateChannel

/-! A single recovery channel cannot recover two distinct logical states from
equal reductions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GangulyCircuitAccess

open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)

/-- A single CPTP recovery map must recover every matrix in the logical qubit algebra. -/
def reconstructs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (d : Fin n) (A : Finset (Fin n)) : Prop :=
  ∃ recovery : QuantumChannel (Config A) (Fin 2),
    ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix (reducedEncoding G d A ρ)) =
        CStarMatrix.ofMatrix ρ

/-- The universal circuit-access inclusion for the graph-state dealer slices. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : Fin n),
    quantumAccess (G.adjMatrix (ZMod 2)) d →
    ∀ A, circuitAuthorized (G.adjMatrix (ZMod 2)) d A → reconstructs G d A

private theorem witness_no_recovery :
    ¬ reconstructs witnessGraph witnessDealer witnessPlayers := by
  rintro ⟨R, hR⟩
  apply logical_x_distinct
  apply CStarMatrix.ofMatrix.injective
  rw [← hR (logicalDensity 1), ← hR (logicalDensity (-1)), witness_reduced_density_eq]

theorem result : ¬ claim := by
  intro h
  exact witness_no_recovery
    (h 7 witnessGraph witnessDealer witness_quantum_access witnessPlayers witness_authorized)

#print axioms result

end D5.S3.Quantum.Information.GangulyCircuitAccess
