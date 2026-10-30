import Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace
open LatticeAllStateField LatticePositiveEnergy LatticeInvolution
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open HalfFock.LatticeHalfFockParityField
open _root_.D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private T originalL1 from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

namespace mixed_jacobi
abbrev signature : Signature where
  Params := LatticeData
  State D := FixedRestrictedDual D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ D := FixedRestrictedDual D → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actualEqual : Realization signature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejectedEqual : Realization signature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observed := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)),
    observed.readout () D
      (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
        normalizedCoefficient D hu (m+n-(j : ℤ))
          (((fixedParitySlice D hu (-1) a)[[r+(j : ℤ)]]) u) v)
      (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
        (oppositeAction D hu hD (m+r-(j : ℤ)) a
          (normalizedCoefficient D hu (n+(j : ℤ)) u v) -
         (-1 : ℂ)^r • normalizedCoefficient D hu (n+r-(j : ℤ)) u
           (((fixedParitySlice D hu (-1) a)[[m+(j : ℤ)]]) v)))

theorem sourceBridge :
    (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_jacobi)) ↔
      arena.Law actualEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law rejectedEqual := by
  intro law
  obtain ⟨D, e, h24, hu, hpos, hpair⟩ :=
    _root_.D5.S3.Arith.Lattices.Golay.RealLeech.exists_positive_even_unimodular_gram
  exact law D hu hpos h24 0 0 0 0 0 0
private theorem actualDependence : ObservationalDependence signature actualEqual := by
  intro i
  obtain ⟨D, e, hu, h24, hpos, hpair, a, u, v, ha, huH, hvK, hvac, hne⟩ :=
    _root_.D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.actual_leech_vacuum_channel
  let z : FixedRestrictedDual D := normalizedCoefficient D hu 3 u v
  refine ⟨D, 0, z, ?_⟩
  intro he
  have hz : z = 0 := Eq.mp (congrFun he 0) rfl
  apply hne
  have evaluated := congrArg (fun q : FixedRestrictedDual D => q 0 a) hz
  simpa [z] using evaluated

private theorem actualSensitivity : Sensitivity arena actualEqual := by
  constructor
  · intro i
    refine ⟨rejectedEqual, ?_, ?_, rejectedLaw⟩
    · intro j h
      exact (h (Subsingleton.elim (α := Unit) _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena
    (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_jacobi)) where
  actual := actualEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_jacobi,
    rejectedEqual, rejectedLaw⟩
  sensitivity := actualSensitivity
  dependence := actualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_jacobi)
    (type_of% (realize signature actualEqual.readout actualEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_jacobi "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite.mixed_jacobi.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualEqual.readout actualEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end mixed_jacobi

end Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
