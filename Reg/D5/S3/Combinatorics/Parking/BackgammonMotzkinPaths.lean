import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Parking.BackgammonMotzkinPaths

open LeanInformationAudit
open BackgammonIncreasingPrefix BackgammonMotzkinPaths
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace Reg.D5.S3.Combinatorics.Parking.BackgammonMotzkinPaths

noncomputable section

private abbrev signature (P A : Type) : DependentFamily.Signature where
  Params := P
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => A
  Anchor := Empty
  finiteAnchor := inferInstance

private def shapeActual : DependentFamily.Realization (signature Unit (List Int)) :=
  DependentFamily.realize (signature Unit (List Int)) (fun _ _ k => signedCoefficients k) (fun e => nomatch e)

private abbrev shapeArena : DependentFamily.Arena where
  signature := signature Unit (List Int)
  Law R := ∀ k : Nat,
    (R.readout () () k).length = 2 * k + 1 ∧
    (R.readout () () k).getLast? = some 1 ∧
    (0 < k → (R.readout () () k).head? = some 0)

private def shapeRejected : DependentFamily.Realization (signature Unit (List Int)) :=
  DependentFamily.realize (signature Unit (List Int)) (fun _ _ _ => []) (fun e => nomatch e)

private theorem shapeRejectedLaw : ¬ shapeArena.Law shapeRejected := by
  intro bad
  have h := (bad 0).1
  change ([] : List Int).length = 1 at h
  simp at h

def shapeFamily : DependentFamily.Registration shapeArena
    (∀ k : Nat,
    (signedCoefficients k).length = 2 * k + 1 ∧
    (signedCoefficients k).getLast? = some 1 ∧
    (0 < k → (signedCoefficients k).head? = some 0)) where
  actual := shapeActual
  bridge := Iff.rfl
  variation := ⟨signedCoefficients_shape, shapeRejected, shapeRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨shapeRejected, ?_, rfl, shapeRejectedLaw⟩
      intro j different
      exact (different (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change signedCoefficients 0 ≠ signedCoefficients 1
    decide +kernel

def shapeRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@signedCoefficients_shape) (DependentFamily.Realization (signature Unit (List Int))) Type Unit where
  unitName := .str ``signedCoefficients_shape "__information_unit"
  realizationName := ``shapeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨shapeArena⟩
  objectArena := .source ⟨shapeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shapeArena ⟨shapeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence
    ⟨(show Nonempty (DependentFamily.Realization (signature Unit (List Int))) from
      ⟨shapeActual⟩)⟩ trivial
  readout := some (DependentFamily.realize (signature Unit (List Int))
    (fun _ _ k => signedCoefficients k) (fun e => nomatch e))
  variation := .evidence ⟨shapeFamily.variation⟩ trivial
  sensitivity := .evidence ⟨shapeFamily.sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.Parking.BackgammonMotzkinPaths
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Parking.BackgammonMotzkinPaths
