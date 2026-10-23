import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.ChargedResidue.Locality

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.ChargedResidue.Locality
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedResidue
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev sourceScope := type_of% (@chargedPhysicalResidueRow_tail)
theorem source_actual : sourceScope := @chargedPhysicalResidueRow_tail

abbrev Parameters := Σ data : {D : LatticeData // IsUnit D.G.det},
  Charge data.val × Charge data.val × Bool × Bool × ℤ × ℤ × ℤ × ℤ × ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun p => ActualTensor p.1.val p.1.property)
  (fun p => ActualTensor p.1.val p.1.property)

def actual : Realization signature := realize signature (fun _ p x =>
  chargedPhysicalResidueRow p.1.val p.1.property p.2.1 p.2.2.1 p.2.2.2.1
    p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1
    p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2 x) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ)
    (K : ℕ), (bilinear D sigma tau).natAbs ≤ K →
    ∀ (l : ℕ), ((K : ℤ)-r).toNat ≤ l → ∀ (x : ActualTensor D hu),
    observation.readout () ⟨⟨D, hu⟩, sigma, tau, epsilon, eta, gamma, delta, r, n, l⟩ x = 0

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl
theorem actual_positive : arena.Law actual := source_bridge.mp source_actual

/- The original source family and its reconstruction retain every lattice,
   every sector, all signed lifts and every actual input. A Registration
   additionally requires whole-family variation, sensitivity, observational
   dependence and structural sourceSelection. These are not asserted by the
   exact source bridge. -/
end Reg.D5.S3.VertexAlgebra.ChargedResidue.Locality
