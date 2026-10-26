import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.SectorPropagation

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.SectorPropagation

abbrev sourceScope_sector_ground_right_word :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.sector_ground_right_word)

theorem source_actual_sector_ground_right_word : sourceScope_sector_ground_right_word :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.sector_ground_right_word

abbrev sourceScope_physicalSlice_sectorProject :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.physicalSlice_sectorProject)

theorem source_actual_physicalSlice_sectorProject : sourceScope_physicalSlice_sectorProject :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.physicalSlice_sectorProject

abbrev sourceScope_mu_sectorProject :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.mu_sectorProject)

theorem source_actual_mu_sectorProject : sourceScope_mu_sectorProject :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.mu_sectorProject

abbrev sourceScope_projectedGround_arbitrary_second :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_arbitrary_second)

theorem source_actual_projectedGround_arbitrary_second : sourceScope_projectedGround_arbitrary_second :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_arbitrary_second

/- These exact full-source reconstructions preserve every original fiber.
   A four-slot Contract.Registration additionally requires a lawful enrolled
   dependent readout, exact sourceSelection and complete-family variation,
   sensitivity and observational-dependence evidence. Those obligations are
   unresolved here; these reconstructions assert no declared_validated state. -/


noncomputable section
open scoped BigOperators VertexOperator
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeInvolution
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeHalfFockGroundRightCurrentTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace RestrictedWordAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ D : LatticeData, List (Index D) × Bool) (fun p => Charge p.1) (fun p => Carrier p.1)
def actual : Realization signature := realize signature
  (fun _ p alpha => rightCurrentWord p.1 p.2.1 (projectedGround p.1 alpha p.2.2)) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (_groundPair : SectorGroundPair D hu) (word : List (Index D))
    (alpha beta : Charge D) (epsilon eta : Bool) (gamma delta : ℤ),
    sectorSign epsilon = (-1 : ℂ)^gamma →
    sectorSign (wordParity word eta) = (-1 : ℂ)^delta →
    OriginalCompatible D hu (projectedGround D alpha epsilon)
      (observation.readout () ⟨D, word, eta⟩ beta) gamma delta
theorem source_bridge : (type_of% (@sector_ground_right_word)) ↔ arena.Law actual := Iff.rfl
end RestrictedWordAttempt

namespace PhysicalProjectionAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ data : {D : LatticeData // IsUnit D.G.det}, Bool × ℤ)
    (fun p => Carrier p.1.val)
    (fun p => VertexOperator ℂ (ActualTensor p.1.val p.1.property))
def actual : Realization signature := realize signature
  (fun _ p b => physicalSlice p.1.val p.1.property
    (correctedField p.1.val p.1.property (sectorProject p.1.val p.2.1 b)) p.2.2)
  (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (b : Carrier D) (eta : Bool) (delta : ℤ),
    sectorSign eta = (-1 : ℂ)^delta →
    observation.readout () ⟨⟨D, hu⟩, eta, delta⟩ b =
      physicalSlice D hu (correctedField D hu b) delta
theorem source_bridge : (type_of% (@physicalSlice_sectorProject)) ↔ arena.Law actual := Iff.rfl
end PhysicalProjectionAttempt

namespace MuProjectionAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (LatticeData × Bool) (fun p => Carrier p.1) (fun p => Carrier p.1)
def actual : Realization signature := realize signature
  (fun _ p b => sectorProject p.1 p.2 b) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (a b : Carrier D)
    (r gamma delta : ℤ) (epsilon eta zeta : Bool),
    theta D a = sectorSign epsilon • a →
    sectorSign epsilon = (-1 : ℂ)^gamma →
    sectorSign eta = (-1 : ℂ)^delta →
    sectorSign zeta = (-1 : ℂ)^(gamma + delta) →
    sectorProject D zeta (LatticeAllStateReconstruction.mu D a r b) =
      LatticeAllStateReconstruction.mu D a r (observation.readout () (D, eta) b)
theorem source_bridge : (type_of% (@mu_sectorProject)) ↔ arena.Law actual := Iff.rfl
end MuProjectionAttempt

namespace ArbitrarySecondAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ data : {D : LatticeData // IsUnit D.G.det}, Charge data.val × Bool × ℤ × ℤ)
    (fun p => Carrier p.1.val)
    (fun p => VertexOperator ℂ (ActualTensor p.1.val p.1.property) ×
      (ℤ → VertexOperator ℂ (ActualTensor p.1.val p.1.property)))
def actual : Realization signature := realize signature
  (fun _ p b =>
    (physicalSlice p.1.val p.1.property (correctedField p.1.val p.1.property b) p.2.2.2.2,
      fun r => physicalSlice p.1.val p.1.property (correctedField p.1.val p.1.property
        (LatticeAllStateReconstruction.mu p.1.val
          (projectedGround p.1.val p.2.1 p.2.2.1) r b))
        (p.2.2.2.1 + p.2.2.2.2))) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (_groundPair : SectorGroundPair D hu) (alpha : Charge D) (epsilon : Bool)
    (gamma delta : ℤ) (b : Carrier D),
    sectorSign epsilon = (-1 : ℂ)^gamma →
    Calculus.fullLaw
      (physicalSlice D hu (correctedField D hu (projectedGround D alpha epsilon)) gamma)
      (observation.readout () ⟨⟨D, hu⟩, alpha, epsilon, gamma, delta⟩ b).1
      (observation.readout () ⟨⟨D, hu⟩, alpha, epsilon, gamma, delta⟩ b).2 gamma
theorem source_bridge : (type_of% (@projectedGround_arbitrary_second)) ↔ arena.Law actual := Iff.rfl
end ArbitrarySecondAttempt

/- The natural dependent readouts and exact bridges above retain all source
   fibers, including zero rank and zero or vanishing sectors. Completing a
   Contract.Registration still requires whole-family variation, sensitivity,
   observational dependence and structural sourceSelection evidence. No
   registered status or evidence for those missing slots is asserted. -/
end

end Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.SectorPropagation
