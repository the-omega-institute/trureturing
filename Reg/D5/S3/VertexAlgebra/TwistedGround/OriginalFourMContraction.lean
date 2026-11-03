import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeAllStateField LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockGradedTrace
open HalfFock.LatticeHalfFockParityField TwistedGround.ActualChargedAdjoint
open TwistedGround.MixedIntertwiner SourceBPZ.OriginalSourceCoevaluation
open private sourceGradePairingEquiv from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
open private kernel from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  h24 : D.rank = 24
  H : ℕ
  K : ℕ
  k : ℤ
  t : ℤ
  u : paritySpace D hu (-1)
  v : paritySpace D hu (-1)
  huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val
  hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun p => ActualTensor p.D p.hu × ActualTensor p.D p.hu) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p wd =>
    let h : ℤ := (p.H : ℤ)+(p.K : ℤ)-p.k-1
    let f := normalizedCoefficient p.D p.hu p.k p.u p.v h
    let x := (sourceGradePairingEquiv p.D p.hu p.hD h).symm f
    actualForm p.D p.hu wd.2 ((correctedField p.D p.hu x.val).coeff (-2*p.t-2) wd.1))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (k t : ℤ) (u v : paritySpace D hu (-1))
    (w d : ActualTensor D hu)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val),
    let h : ℤ := (H : ℤ)+(K : ℤ)-k-1
    let f := normalizedCoefficient D hu k u v h
    let E := sourceGradePairingEquiv D hu hD h
    let x := E.symm f
    let F := kernel D hu H K k u.val v.val
    r.readout () ⟨D, hu, hD, h24, H, K, k, t, u, v, huH, hvK⟩ (w, d) =
        (2 : ℂ)⁻¹ * ∑ᶠ a : EnergyFiber D h,
          (F (carrierBasis D a.val) + F (theta D (carrierBasis D a.val))) *
            actualForm D hu d
              ((correctedField D hu (dualCarrierBasis D a.val)).coeff (-2*t-2) w) ∧
    r.readout () ⟨D, hu, hD, h24, H, K, k, t, u, v, huH, hvK⟩ (w, d) =
      if hh : h < 0 then 0 else if hz : h = 0 then
        f (hz.symm ▸ gradeVacuum D) *
          actualForm D hu d ((correctedField D hu (vacuum D)).coeff (-2*t-2) w)
      else ∑ᶠ a : EnergyFiber D h, f (fixedFrame D h a) *
        actualForm D hu d
          ((correctedField D hu (fixedDualFrame D h a).val).coeff (-2*t-2) w)

theorem sourceBridge : (type_of% (@fourM_contraction)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@fourM_contraction)

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
