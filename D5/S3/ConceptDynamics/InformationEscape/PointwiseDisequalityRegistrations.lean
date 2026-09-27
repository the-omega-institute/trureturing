/- GID: D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrent_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrentRealization
   digest: Recurrent and transient channel exclusions share a pointwise disequality template and one digit arena. -/

import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S0.Certificates.SkeletonChannelRetraction


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations

open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord D5.S3.ConceptDynamics.CIRPT


open D5.S0.Certificates.SkeletonChannelRetraction

def digitZero : Fin 4 := (⟨Nat.zero, (let h : Nat.lt 0 4 := (by change 0 < 4; omega); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))
def digitOne : Fin 4 := (⟨Nat.succ (Nat.zero), (let h : Nat.lt 1 4 := (by change 1 < 4; omega); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))
def digitTwo : Fin 4 := (⟨Nat.succ (Nat.succ (Nat.zero)), (let h : Nat.lt 2 4 := (by change 2 < 4; omega); h)⟩ : Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))

def digitArena := homogeneousPointwiseNeArena (Arena.ofFintype (Fin 4)) (Fin 4)
theorem digit_slotSensitive : FiniteSlotSensitivity digitArena :=
  homogeneousPointwiseNe_sensitivity _ (0 : Fin 4) (0 : Fin 4) 1 (by decide)

def recurrentReadout (d : Fin 4) : Fin 4 :=
  Bool.rec d digitZero
    (@decide (d = digitTwo) (instDecidableEqFin 4 d digitTwo))
def recurrentRealization := @homogeneousPointwiseNeRealization (Fin 4) (Fin 4)
  (instDecidableEqFin 4) (fun d => recurrentReadout d) (fun _ => digitTwo)
theorem recurrent_bridge : LegacyPrimitiveRealization digitArena
    (∀ d : Fin 4, recurrentRetract d ≠ 2) recurrentRealization := by
  constructor
  change (∀ d : Fin 4, recurrentRetract d ≠ 2) ↔ (∀ d : Fin 4, recurrentReadout d ≠ 2)
  have tableEq (d : Fin 4) : recurrentReadout d = recurrentRetract d := by
    fin_cases d <;> decide
  simp only [tableEq]
theorem recurrent_lawSensitive : digitArena.Law recurrentRealization ∧
    ¬ digitArena.Law (homogeneousPointwiseNeRealization (fun _ => (2 : Fin 4)) (fun _ => 2)) :=
  ⟨recurrent_bridge.equivalence.mp recurrentRetract_ne_two, fun h => h (0 : Fin 4) rfl⟩

private def recurrentChain : LayerChain digitArena.toArena where
  length := 0
  kernel := fun _ => cutKernel (fun d : Fin 4 => (recurrentReadout d, digitTwo))
  refines := fun r => Fin.elim0 r

section
private local instance : DecidableEq digitArena.State := instDecidableEqFin 4

def recurrentResidual : EscapeResidualWitness recurrentChain :=
  ⟨(0 : Fin 4), (2 : Fin 4), by decide +kernel⟩
end



#print axioms recurrent_bridge
#print axioms recurrent_lawSensitive


def transientReadout (d : Fin 4) : Fin 4 :=
  Bool.rec d digitOne
    (@decide (d = digitZero) (instDecidableEqFin 4 d digitZero))
def transientRealization := @homogeneousPointwiseNeRealization (Fin 4) (Fin 4)
  (instDecidableEqFin 4) (fun d => transientReadout d) (fun _ => digitZero)
theorem transient_bridge : LegacyPrimitiveRealization digitArena
    (∀ d : Fin 4, transientRetract d ≠ 0) transientRealization := by
  constructor
  change (∀ d : Fin 4, transientRetract d ≠ 0) ↔ (∀ d : Fin 4, transientReadout d ≠ 0)
  have tableEq (d : Fin 4) : transientReadout d = transientRetract d := by
    fin_cases d <;> decide
  simp only [tableEq]
theorem transient_lawSensitive : digitArena.Law transientRealization ∧
    ¬ digitArena.Law (homogeneousPointwiseNeRealization (fun _ => (0 : Fin 4)) (fun _ => 0)) :=
  ⟨transient_bridge.equivalence.mp transientRetract_ne_zero, fun h => h (0 : Fin 4) rfl⟩

private def transientChain : LayerChain digitArena.toArena where
  length := 0
  kernel := fun _ => cutKernel (fun d : Fin 4 => (transientReadout d, digitZero))
  refines := fun r => Fin.elim0 r

section
private local instance : DecidableEq digitArena.State := instDecidableEqFin 4

def transientResidual : EscapeResidualWitness transientChain :=
  ⟨(0 : Fin 4), (1 : Fin 4), by decide +kernel⟩
end



#print axioms transient_bridge
#print axioms transient_lawSensitive


#print axioms digit_slotSensitive




end D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
