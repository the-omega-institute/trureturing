import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Hypercube.BinaryQuadraticMoments
import Reg.Support.SingleDependentReadout

/-! The pair-moment matrix as a dependent readout of a cube word. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryQuadraticMoments

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
open _root_.D5.S3.Combinatorics.Graph.Hypercube.BinaryQuadraticMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev Word (n : ℕ) := Finset (Fin n) → ZMod 2

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ Word (fun n => Fin n → Fin n → ZMod 2)

def actual : Realization signature :=
  realize signature (fun _ _ f => pairMoment f) (fun e => nomatch e)

def constantOne : Realization signature :=
  realize signature (fun _ _ _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (_ : Odd n) {f : Word n} (_ : adjacency f = f),
    ∃ t : Fin n → ZMod 2, ∀ i j, r.readout () n f i j = t i + t j

private theorem constantOne_fails : ¬ arena.Law constantOne := by
  intro h
  have hfixed : adjacency (0 : Word 1) = 0 := by
    funext x
    simp [adjacency]
  obtain ⟨t, ht⟩ := @h 1 (by decide) 0 hfixed
  have hdiag : (1 : ZMod 2) = t 0 + t 0 := ht 0 0
  simpa only [ZModModule.add_self, one_ne_zero] using hdiag

private theorem actual_depends_on_word : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 0, (fun _ => 1), ?_⟩
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  have hne : pairMoment (0 : Word 2) 0 1 ≠ pairMoment (fun _ => 1 : Word 2) 0 1 := by decide
  exact hne h01

def momentFamily : Registration arena (type_of% (@exists_pairMoment_eq_add)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_pairMoment_eq_add, constantOne, constantOne_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual constantOne
    constantOne_fails
  dependence := actual_depends_on_word

def momentAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@exists_pairMoment_eq_add) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Hypercube.BinaryQuadraticMoments.exists_pairMoment_eq_add.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryQuadraticMoments.momentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨momentFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => pairMoment f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.BinaryQuadraticMoments
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryQuadraticMoments
