import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree
open _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option maxHeartbeats 1000000
noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := minCompatDegree = 2 / R.readout () () 13

theorem positive : arena.Law actual := result

theorem negative : ¬ arena.Law rejected := by
  intro h
  have hh : minCompatDegree = 2 := by simpa [arena, rejected, realize] using h
  have hr : minCompatDegree = endpoint := result
  have he := endpoint_mem_Icc.2
  rw [← hr, hh] at he
  norm_num at he

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree.result)
    (type_of% (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree.result
    "Reg.D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree/Reg.D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree, definition := some { owner := `D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree, name := `D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree.claim, path := #[] },
    coordinates := #[], readouts := #[{
      path := #["arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end Reg.D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree
