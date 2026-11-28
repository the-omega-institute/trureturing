/- GID: D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/GangulyCircuitAccess/Recovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.claim; result=D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.result; claim=D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.claim
   digest: A circuit-authorized player set lacks a recovery channel for the dealer-slice encoding. -/

/-
Admission basis: open-problem-resolution (https://github.com/the-omega-institute/trureturing/issues/35163).
reconstructs is consumed by claim, claim is consumed by result,
witness_no_common_recovery is consumed by the private witness_no_recovery
step, and witness_no_recovery is consumed by result. The live result path is
witness_quantum_access → witness_authorized → result's seven-vertex
instantiation, then witness_reduced_density_eq and logical_x_distinct →
witness_no_common_recovery → witness_no_recovery. The direct frozen dependency
is D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel, statement_id
sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05.
The result is the sole utility settlement and is exempt from four-slot escape
registration. Four-slot escape registration was attempted for
witness_no_common_recovery. No enrolled template matches the finite
function-equality obstruction, so the unfinished audit is disclosed at the
linked issue with the missing realization, variation, and sensitivity evidence
named there. The Scribe scope is the seven-vertex refutation. No Problems
dossier is included in this source checkpoint.
-/

import D5.S3.Quantum.Information.GangulyCircuitAccess.DealerCode
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

/-- Even an arbitrary function of the retained matrix cannot recover both inputs. -/
theorem witness_no_common_recovery :
    ¬ ∃ R : Matrix (Config witnessPlayers) (Config witnessPlayers) ℂ → Matrix (Fin 2) (Fin 2) ℂ,
      R (reducedEncoding witnessGraph witnessDealer witnessPlayers (logicalDensity 1)) =
        logicalDensity 1 ∧
      R (reducedEncoding witnessGraph witnessDealer witnessPlayers (logicalDensity (-1))) =
        logicalDensity (-1) := by
  rintro ⟨R, hPlus, hMinus⟩
  apply logical_x_distinct
  exact hPlus.symm.trans ((congrArg R witness_reduced_density_eq).trans hMinus)

private theorem witness_no_recovery :
    ¬ reconstructs witnessGraph witnessDealer witnessPlayers := by
  rintro ⟨R, hR⟩
  apply witness_no_common_recovery
  refine ⟨fun ρ => CStarMatrix.ofMatrix.symm (R.toCompletelyPositiveMap (CStarMatrix.ofMatrix ρ)),
    ?_, ?_⟩
  · exact congrArg CStarMatrix.ofMatrix.symm (hR (logicalDensity 1))
  · exact congrArg CStarMatrix.ofMatrix.symm (hR (logicalDensity (-1)))

theorem result : ¬ claim := by
  intro h
  exact witness_no_recovery
    (h 7 witnessGraph witnessDealer witness_quantum_access witnessPlayers witness_authorized)

#print axioms witness_no_common_recovery
#print axioms result

end D5.S3.Quantum.Information.GangulyCircuitAccess
