import D5.S3.VertexAlgebra.TwistedGround.OriginalSourceSkew
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The complete original skew telescope, with source-bound coefficient observations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceSkew

attribute [local instance] Classical.propDecidable

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeInvolution LatticeAllStateField
open HalfFock.LatticeHalfFockParityField
open TwistedGround.MixedIntertwiner
open SourceBPZ.OriginalSourcePairing

structure Parameters where
  D : LatticeData
  hu : IsUnit D.G.det
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  h24 : D.rank = 24
  m : ℤ
  v : paritySpace D hu (-1)

abbrev signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun p => paritySpace p.D p.hu (-1)) (fun p => FixedCarrier p.D)

def actual : Realization signature := realize signature
  (fun _ p u => originalCoefficient p.D p.hu p.hD p.m u p.v)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p _ => fixedVacuum p.D) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (m : ℤ) (u v : paritySpace D hu (-1)),
    Function.HasFiniteSupport (fun j : ℕ =>
      (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) •
        (fixedTranslation D ^ j) (originalCoefficient D hu hD (m+(j : ℤ)) v u)) ∧
    R.readout () ⟨D,hu,hD,h24,m,v⟩ u = ∑ᶠ j : ℕ,
      (((-1 : ℂ)^(m+(j : ℤ)+1))/(j.factorial : ℂ)) •
        (fixedTranslation D ^ j) (originalCoefficient D hu hD (m+(j : ℤ)) v u)

private theorem sourceBridge : (type_of% (@originalCoefficient_skew)) ↔ arena.Law actual :=
  Iff.rfl

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨D,e,hu,h24,hD,rest⟩ := actual_leech_vacuum_channel
  have equality := (h D hu hD h24 0 0 0).2
  have zero : (∑ᶠ j : ℕ,
      (((-1 : ℂ)^(0+(j : ℤ)+1))/(j.factorial : ℂ)) •
        (fixedTranslation D ^ j) (originalCoefficient D hu hD (0+(j : ℤ)) 0 0)) = 0 := by
    simp [originalCoefficient]
  rw [zero] at equality
  exact LatticePositiveEnergy.vacuum_nonzero D
    (congrArg (fun x : FixedCarrier D => x.val) equality)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨D,e,hu,h24,hD,_,a,u,v,_,_,_,_,nonzero⟩ := actual_leech_vacuum_channel
  refine ⟨⟨D,hu,hD,h24,3,v⟩, u, 0, ?_⟩
  change originalCoefficient D hu hD 3 u v ≠ originalCoefficient D hu hD 3 0 v
  have zero : originalCoefficient D hu hD 3 0 v = 0 := by simp [originalCoefficient]
  rw [zero]
  intro hz
  have mapped := congrArg (sourcePairingDualEquiv D hu hD) hz
  change (sourcePairingDualEquiv D hu hD)
    ((sourcePairingDualEquiv D hu hD).symm (normalizedCoefficient D hu 3 u v)) =
      (sourcePairingDualEquiv D hu hD) 0 at mapped
  rw [LinearEquiv.apply_symm_apply, map_zero] at mapped
  exact nonzero (congrArg (fun f : FixedRestrictedDual D => f 0 a) mapped)

def family : Registration arena (type_of% (@originalCoefficient_skew)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp originalCoefficient_skew, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@originalCoefficient_skew)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.originalCoefficient_skew
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceSkew.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalSourceSkew
    definition := none
    coordinates := #[0,4,6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","arg","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceSkew
