import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage
open _root_.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage

abbrev signature : Signature where
  Params := List ℕ
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ e d => winCount d e) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ d e : List ℕ, r.readout () e d = indexWinCount d e

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h [2] [1]
  norm_num [rejected, realize, indexWinCount] at hbad

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨[1], [2], [], ?_⟩
  norm_num [actual, realize, winCount]

noncomputable def bridge_registration : Registration arena
    (∀ d e : List ℕ, winCount d e = indexWinCount d e) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨winCount_eq_indexWinCount, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.winCount_eq_indexWinCount)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ e d => winCount d e) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.bridge_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.bridge_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨bridge_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ e d => winCount d e) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage,
    definition := none,
    coordinates := #[],
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage
