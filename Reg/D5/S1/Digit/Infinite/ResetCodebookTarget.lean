import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.ResetCodebookTarget
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S1.Digit.Infinite.ResetCodebookTarget.OriginalRoot

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => OriginalSpectralRoot p.1 p.2.1 p.2.2 z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (K n : ℕ) (d : ℝ), 2 ≤ K → K ≤ n →
  ∃! z : ℝ, OriginalSpectralRoot K n d z

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K n : ℕ) (d : ℝ), 2 ≤ K → K ≤ n →
    ∃! z : ℝ, R.readout () ⟨K,n,d⟩ z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z,hz,_⟩ := h 2 2 0 (by omega) (by omega)
  exact hz

def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Spectral.original_root_exists_unique,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    obtain ⟨z,hz,_⟩ := Spectral.original_root_exists_unique 2 2 0 (by omega) (by omega)
    refine ⟨⟨2,2,0⟩,z,(0 : ℝ),?_⟩
    intro he
    have hzero : OriginalSpectralRoot 2 2 0 0 := Eq.mp he hz
    exact (lt_irrefl (0 : ℝ)) hzero.1

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.original_root_exists_unique)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ p z => OriginalSpectralRoot p.1 p.2.1 p.2.2 z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Spectral.original_root_exists_unique.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookTarget.OriginalRoot.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ p z => OriginalSpectralRoot p.1 p.2.1 p.2.2 z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookTarget,
    definition := none, coordinates := #[0,1,2],
    readouts := #[{
      path := #["body","body","body","body","body","arg","body"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S1.Digit.Infinite.ResetCodebookTarget.OriginalRoot
