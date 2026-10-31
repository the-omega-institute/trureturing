import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

/-! Source-bound counting and threshold readouts for dice probabilities. -/

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
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

namespace Threshold
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => threshold n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 3, 4, ?_⟩
  norm_num [actual, realize, threshold]
end Threshold

namespace AboveHalf
abbrev arena : Arena where
  signature := Threshold.signature
  Law r := ∀ n : ℕ, 0 < n → ∀ d e : List ℕ, IsDie n d → IsDie n e →
    (1/2 < winProbability d e ↔ r.readout () () n ≤ winCount d e)
theorem rejected_law : ¬ arena.Law Threshold.rejected := by
  intro h
  have hd : IsDie 3 [1,1,1] := by unfold IsDie; decide
  have hp : winProbability [1,1,1] [1,1,1] = 0 := by
    norm_num [winProbability, ← winCount_eq_indexWinCount, winCount]
  have hw : winCount [1,1,1] [1,1,1] = 0 := by decide
  have hh := h 3 (by decide) [1,1,1] [1,1,1] hd hd
  norm_num [Threshold.rejected, realize, hp, hw] at hh
end AboveHalf

namespace Minimum
abbrev arena : Arena where
  signature := Threshold.signature
  Law r := ∀ n : ℕ, 3 ≤ n → IsMinimum n ((r.readout () () n : ℚ)/(n*n : ℕ))
theorem rejected_law : ¬ arena.Law Threshold.rejected := by
  intro h
  have hh := (h 3 (by decide)).2.1
  norm_num [Threshold.rejected, realize] at hh
end Minimum

namespace EdgeScore
abbrev arena : Arena where
  signature := Threshold.signature
  Law r := ∀ n : ℕ, 3 ≤ n → ∀ d e : List ℕ, IsDie n d → IsDie n e →
    (Edge n d e ↔ winCount d e = r.readout () () n)
theorem rejected_law : ¬ arena.Law Threshold.rejected := by
  intro h
  have hd : IsDie 3 [1,1,1] := by unfold IsDie; decide
  have hp : winProbability [1,1,1] [1,1,1] = 0 := by
    norm_num [winProbability, ← winCount_eq_indexWinCount, winCount]
  have hw : winCount [1,1,1] [1,1,1] = 0 := by decide
  have hh := (h 3 (by decide) [1,1,1] [1,1,1] hd hd).mpr
    (by simpa [Threshold.rejected, realize] using hw)
  have hpos := hh.2.2.2.1
  rw [hp] at hpos
  norm_num at hpos
end EdgeScore

namespace AboveHalf
noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.above_half_iff)) where
  actual := Threshold.actual
  bridge := Iff.rfl
  variation := ⟨above_half_iff, Threshold.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨Threshold.rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := Threshold.dependence_proof
end AboveHalf

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.above_half_iff)
    (type_of% (realize.{0,0,0,0,0} Threshold.signature (fun _ _ n => threshold n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.above_half_iff_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.AboveHalf.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨AboveHalf.arena⟩,
  objectArena := .source ⟨AboveHalf.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source AboveHalf.arena ⟨AboveHalf.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} Threshold.signature (fun _ _ n => threshold n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage,
    definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

namespace Minimum
noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.minimum_probability)) where
  actual := Threshold.actual
  bridge := Iff.rfl
  variation := ⟨minimum_probability, Threshold.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨Threshold.rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := Threshold.dependence_proof
end Minimum

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.minimum_probability)
    (type_of% (realize.{0,0,0,0,0} Threshold.signature (fun _ _ n => threshold n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.minimum_probability_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.Minimum.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Minimum.arena⟩,
  objectArena := .source ⟨Minimum.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Minimum.arena ⟨Minimum.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} Threshold.signature (fun _ _ n => threshold n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage,
    definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

namespace EdgeScore
noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.edge_iff)) where
  actual := Threshold.actual
  bridge := Iff.rfl
  variation := ⟨edge_iff, Threshold.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨Threshold.rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := Threshold.dependence_proof
end EdgeScore

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.edge_iff)
    (type_of% (realize.{0,0,0,0,0} Threshold.signature (fun _ _ n => threshold n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.edge_iff_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage.EdgeScore.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨EdgeScore.arena⟩,
  objectArena := .source ⟨EdgeScore.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source EdgeScore.arena ⟨EdgeScore.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} Threshold.signature (fun _ _ n => threshold n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage,
    definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage
