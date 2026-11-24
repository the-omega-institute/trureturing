import Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMWickLowering

/-! A dependent equality readout for the lowering word partition. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality (LatticeData Index)
open _root_.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial (word creator)
open _root_.D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick (wick)
open _root_.D5.S3.VertexAlgebra.TwistedGround.AffineWickConvolution (partitions)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMWickLowering
  (eval_word_partition pairWeight)
open _root_.Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
  (signature oscillatorEqual oscillatorFalse)

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMWickLowering

open private emptyLattice from Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
open private oscillatorEqualDependence from Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial

namespace LoweringWord

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [Finite X] (D : LatticeData) (_hu : IsUnit D.G.det)
      (θ : ℂ) (mode : X → Index D) (l : List X),
    R.readout () D ((word D (l.map mode)).eval (MvPolynomial.C θ))
      (((partitions l).map fun p =>
        MvPolynomial.C (wick (Matrix.of fun i j => pairWeight D θ (mode i) (mode j)) 0 p.1) *
          (p.2.map fun a => (creator D (mode a)).eval (MvPolynomial.C θ)).prod).sum)

private theorem rejectedLaw : ¬ arena.{u}.Law oscillatorFalse := by
  intro h
  have hu : IsUnit emptyLattice.G.det := by
    change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
    simp
  exact @h (ULift.{u} (Fin 0)) inferInstance emptyLattice hu 0
    (fun a => Fin.elim0 a.down) []

def family : Registration arena.{u} (type_of% (@eval_word_partition.{u})) where
  actual := oscillatorEqual
  bridge := Iff.rfl
  variation := ⟨@eval_word_partition.{u}, oscillatorFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law oscillatorEqual oscillatorFalse rejectedLaw
  dependence := oscillatorEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eval_word_partition.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMWickLowering.LoweringWord.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMWickLowering.LoweringWord.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature oscillatorEqual.readout oscillatorEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMWickLowering
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LoweringWord

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMWickLowering
