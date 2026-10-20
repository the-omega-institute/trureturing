import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Orthogonality.NonradicalLineRetraction
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Orthogonality.NonradicalLineRetraction

open Module
open _root_.D5.S3.Combinatorics.Orthogonality.NikandishClique
open _root_.D5.S3.Combinatorics.Orthogonality.NonradicalLineRetraction
open _root_.D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Parameter := Σ n : ℕ, Fin n → ZMod 2

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun p => Fin p.1 → ZMod 2) (fun _ => ZMod 2)

def actual : Realization signature := realize signature
  (fun (_ : Unit) (p : Parameter) v => standardCoordinatePairing (ZMod 2) (Fin p.1) v p.2)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun (_ : Unit) (_ : Parameter) _ => 0) (fun e => nomatch e)

/-- Replace only the final nonradical pairing readout in the complete source statement. -/
def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, ∃ r : orthogonalityGraph n →g retainedGraph n,
    (∀ U : {U : Vertex n // Retained n U}, r U.1 = U) ∧
    (∀ U : Vertex n, (r U).1.1 ≤ U.1) ∧
    (∀ U : Vertex n, (r U).1 ≠ U →
      finrank (ZMod 2) (r U).1.1 = 1 ∧
      ¬(r U).1.1 ≤ (standardCoordinatePairing (ZMod 2) (Fin n)).orthogonal U.1 ∧
      ∃ v : Fin n → ZMod 2, v ∈ U.1 ∧ v ≠ 0 ∧ (r U).1.1 = (ZMod 2) ∙ v ∧
        ∃ w : Fin n → ZMod 2, w ∈ U.1 ∧ R.readout () ⟨n, w⟩ v ≠ 0)

def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Orthogonality.NonradicalLineRetraction.result)) := by
  have hbad : ¬arena.Law rejected := by
    intro h
    let T : Vertex 2 := ⟨⊤, top_ne_bot⟩
    have notRetained : ¬Retained 2 T := by
      rintro (hd | hi)
      · have ht : finrank (ZMod 2) T.1 = 2 := by simp [T]
        omega
      · have hz := hi (Pi.single 0 1) (by trivial) (Pi.single 0 1) (by trivial)
        change dotProduct (Pi.single (0 : Fin 2) (1 : ZMod 2)) (Pi.single 0 1) = 0 at hz
        simp at hz
    obtain ⟨r, _, _, hm⟩ := h 2
    have moved : (r T).1 ≠ T := by
      intro he
      exact notRetained (he ▸ (r T).2)
    obtain ⟨v, _, _, _, w, _, hn⟩ := (hm T moved).2.2
    exact hn rfl
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨_root_.D5.S3.Combinatorics.Orthogonality.NonradicalLineRetraction.result,
      rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := ?_ }
  intro i
  refine ⟨⟨1, fun _ => 1⟩, (0 : Fin 1 → ZMod 2), (fun _ => 1), ?_⟩
  change standardCoordinatePairing (ZMod 2) (Fin 1) 0 (fun _ => 1) ≠
    standardCoordinatePairing (ZMod 2) (Fin 1) (fun _ => 1) (fun _ => 1)
  change dotProduct (0 : Fin 1 → ZMod 2) (fun _ : Fin 1 => (1 : ZMod 2)) ≠
    dotProduct (fun _ : Fin 1 => (1 : ZMod 2)) (fun _ => 1)
  simp [dotProduct]

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Orthogonality.NonradicalLineRetraction.result)
      (type_of% (realize signature
        (fun (_ : Unit) (p : Parameter) v => standardCoordinatePairing (ZMod 2) (Fin p.1) v p.2)
        (fun e => nomatch e))) (ℕ → Type) Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Orthogonality.NonradicalLineRetraction.informationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Orthogonality.NonradicalLineRetraction.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (p : Parameter) v => standardCoordinatePairing (ZMod 2) (Fin p.1) v p.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Vertex
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Orthogonality.NonradicalLineRetraction
    definition := none
    coordinates := #[0, 5]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "arg", "body", "body", "arg", "arg",
        "arg", "body", "arg", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

#print axioms registration

end Reg.D5.S3.Combinatorics.Orthogonality.NonradicalLineRetraction
