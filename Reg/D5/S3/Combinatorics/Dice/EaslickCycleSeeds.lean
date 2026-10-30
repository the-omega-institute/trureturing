import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Dice.EaslickCycleSeeds
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Dice.EaslickCycleSeeds
open _root_.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage
open _root_.D5.S3.Combinatorics.Dice.EaslickCycleSeeds

abbrev signature : Signature where
  Params := ℕ
  State _ := List (List ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ n c => checkCycle n c) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n, 3 ≤ n → ∀ c : List (List ℕ),
    r.readout () n c = true → HasCycle n c.length

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c,hlen,_,hne,_⟩ := h 6 (by decide) [] rfl
  exact hne (List.eq_nil_of_length_eq_zero hlen)

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨6, sourceSeed 6, [], ?_⟩
  change checkCycle 6 (sourceSeed 6) ≠ checkCycle 6 []
  rw [sourceSeed_check 6 (by decide)]
  decide

noncomputable def soundness_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Dice.EaslickCycleSeeds.checkCycle_sound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨checkCycle_sound, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Combinatorics.Dice.EaslickCycleSeeds.checkCycle_sound)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ n c => checkCycle n c) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Dice.EaslickCycleSeeds.soundness_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Dice.EaslickCycleSeeds.soundness_registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨soundness_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ n c => checkCycle n c) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Dice.EaslickCycleSeeds,
    definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "domain", "fn", "arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

namespace SeedInput
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => checkCycle n (sourceSeed n)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n, n ∈ [6,7,8,9,10,11] → r.readout () () n = true
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have := h 6 (by decide)
  contradiction
theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 6, 5, ?_⟩
  change checkCycle 6 (sourceSeed 6) ≠ checkCycle 5 (sourceSeed 5)
  rw [sourceSeed_check 6 (by decide)]
  decide
noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Dice.EaslickCycleSeeds.sourceSeed_check)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sourceSeed_check, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof
end SeedInput

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Dice.EaslickCycleSeeds.sourceSeed_check)
    (type_of% (realize.{0,0,0,0,0} SeedInput.signature (fun _ _ n => checkCycle n (sourceSeed n)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Dice.EaslickCycleSeeds.seed_input_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Dice.EaslickCycleSeeds.SeedInput.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨SeedInput.arena⟩, objectArena := .source ⟨SeedInput.arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source SeedInput.arena ⟨SeedInput.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} SeedInput.signature (fun _ _ n => checkCycle n (sourceSeed n)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Dice.EaslickCycleSeeds,
    definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Dice.EaslickCycleSeeds
