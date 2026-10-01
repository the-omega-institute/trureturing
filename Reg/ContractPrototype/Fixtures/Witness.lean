import D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord

namespace Reg.ContractPrototype.Fixtures.Witness
open D5.S3.ConceptDynamics.InformationEscape CounterexampleRecord EscapeRecord
open D5.S3.ConceptDynamics.CIRPT

def claim : Prop := ∀ n : Nat, n ≠ 0 ∧ ∀ b : Bool, b = b
theorem result : ¬ claim := fun h => (h 0).1 rfl
theorem second : ¬ claim := result
theorem third : ¬ claim := result
def arena := WitnessArena.ofCarrier (Fin 2) Nat
  (fun n => n ≠ 0 ∧ ∀ b : Bool, b = b) (fun _ => 0)
  (fun _ => .isFalse (fun h => h.1 rfl))
def reads := counterexampleRealization (fun _ : Fin 2 => false)
theorem law : arena.Law reads := ⟨(0 : Fin 2), rfl⟩
theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads := ⟨arena.law_refutes⟩
theorem secondBridge : WitnessPrimitiveRealization arena (¬ claim) reads := ⟨arena.law_refutes⟩
theorem thirdBridge : WitnessPrimitiveRealization arena (¬ claim) reads := ⟨arena.law_refutes⟩
theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue := arena.variation law
theorem sensitivity : LeanInformationAudit.FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

def residualChain : LayerChain arena.toArena where
  length := 0
  kernel := fun _ => cutKernel (fun _ : Fin 2 => false)
  refines := fun r => Fin.elim0 r
local instance : DecidableEq arena.State := arena.stateDecidableEq
def residual : EscapeResidualWitness residualChain := ⟨(0 : Fin 2), (1 : Fin 2), by decide +kernel⟩
end Reg.ContractPrototype.Fixtures.Witness
