import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
import Reg.Support.DependentFamily
import Mathlib.Tactic.Linarith

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
open _root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => expectedRange n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 / 2 : ℚ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 1 ≤ n →
    ∃ m : ℤ, r.readout () () n * 2 ^ (3 * n - 3) = m

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m, hm⟩ := h 1 (by norm_num)
  change (1 / 2 : ℚ) * 2 ^ (3 * 1 - 3) = m at hm
  have hi : (m : ℚ) > 0 ∧ (m : ℚ) < 1 := by norm_num at hm; constructor <;> linarith
  have : (0 : ℤ) < m ∧ m < 1 := by exact_mod_cast hi
  omega

theorem dependence_proof : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change expectedRange 0 ≠ expectedRange 1
  decide +kernel

def registration : Registration arena (_root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.claim) where
  actual := actual
  bridge := by rfl
  variation := ⟨_root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => expectedRange n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "StatisticalMechanics") "RandomWalks") "KnightWalkRangeIntegrality") "result") "Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality/Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => expectedRange n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, definition := some { owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, name := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.claim, path := #[] }, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
