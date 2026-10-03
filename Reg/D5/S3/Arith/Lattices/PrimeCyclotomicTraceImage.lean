import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage

noncomputable section

abbrev Role := Bool

abbrev signature : Signature where
  Params := ℕ
  State := fun n => ℤ × (Fin n → ℤ)
  Role := Role
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ n => ℤ × (Fin n → ℤ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i n => match i with
    | false => traceGram n
    | true => reconstruct n) (fun e => nomatch e)

/-- Each intervention changes one role and leaves the other at its actual value. -/
def rejected (i : Role) : Realization signature := realize signature
  (fun j n x => if j = i then (1, fun _ => 0) else actual.readout j n x)
  (fun e => nomatch e)

/-- All source occurrences remain except the first outer trace and the final reconstruction. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (y : ℤ × (Fin n → ℤ)),
    (∀ i, (2 * (n : ℤ) + 3) ∣ y.2 i - 2 * y.1) ↔
      R.readout false n (reconstruct n y) = y ∧
        ∀ x, traceGram n x = y → x = R.readout true n y

theorem rejected_law (i : Role) : ¬ arena.Law (rejected i) := by
  intro h
  have hh := (h 0 (0, fun _ => 0)).mp (by intro j; exact Fin.elim0 j)
  cases i
  · have he := congrArg Prod.fst hh.1
    norm_num [rejected, realize] at he
  · have he := congrArg Prod.fst (hh.2 (0, fun _ => 0) (by simp [traceGram]))
    norm_num [rejected, realize] at he

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize] using integral_image,
    rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j h
      funext n x
      simp [rejected, realize, h]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨0, (0, fun _ => 0), (1, fun _ => 0), ?_⟩
    intro he
    have hfirst := congrArg Prod.fst he
    cases i <;> norm_num [actual, realize, traceGram, reconstruct] at hfirst

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.integral_image) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun i n => match i with
    | false => traceGram n
    | true => reconstruct n) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Lattices") "PrimeCyclotomicTraceImage") "integral_image") "Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage/Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun i n => match i with
    | false => traceGram n
    | true => reconstruct n) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "arg", "arg", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }, { path := #["body", "body", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end
end Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage
