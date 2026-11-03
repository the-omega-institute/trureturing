import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantThetaS

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open LeanInformationAudit Matrix
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open _root_.D5.S3.Fourier.MatrixGaussian
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.VertexAlgebra.LatticeDiscriminantThetaS

/-! The full-telescope source-bound registration for the native all-sector S law.
The outer four-slot consumer remains an independent audit obligation; this file
retains only the kernel-checked source family and does not claim `declared_validated`.
-/

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp

private theorem zeroPositive : (gramReal zeroLattice).PosDef := by
  constructor
  · ext i
    exact Fin.elim0 i
  · intro x hx
    apply False.elim
    apply hx
    ext i
    exact Fin.elim0 i

abbrev equalitySignature : Signature where
  Params := Type
  State α := α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := α → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equalityActual : Realization equalitySignature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)

def equalityRejected : Realization equalitySignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem equalityDependence : ObservationalDependence equalitySignature equalityActual := by
  intro i
  refine ⟨ℕ, 0, 1, ?_⟩
  intro h
  have he : (1 : ℕ) = 0 := Eq.mp (congrFun h 0) rfl
  omega

abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : (gramReal D).PosDef)
    (x : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im),
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    a.readout () ℂ (sectorTheta D x (-1 / τ))
      ((-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
        (Real.sqrt (gramReal D).det : ℂ) *
        ∑ c : Discriminant D,
          pairingCharacter D hD x (-c) * sectorTheta D c τ)

private theorem sourceBridge :
    (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.sector_S)) ↔
      arena.Law equalityActual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact h zeroLattice zeroPositive 0 Complex.I (by simp)

def family : Registration arena
    (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.sector_S)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.LatticeDiscriminantTheta.sector_S,
    equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.sector_S)
      (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantThetaS.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantThetaS.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  familyRecord := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantThetaS
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  options := #[]
end Reg.D5.S3.VertexAlgebra.LatticeDiscriminantThetaS
