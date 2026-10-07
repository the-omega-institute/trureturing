import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.PrimeNumberTheorem.Smooth1
import Reg.Support.DependentFamily
import Reg.Support.PntAuditFacts

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1

open Set Function Filter Complex Real MeasureTheory
open scoped ContDiff Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PntAuditFacts
open LeanInformationAudit

noncomputable section

namespace Below

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c ε => 1 - c * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 5) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1),
    ∃ c : ℝ, 0 < c ∧ c = Real.log 2 ∧
      ∀ (ε x : ℝ) (_ : 0 < ε), 0 < x → x ≤ r.readout () c ε →
        _root_.Smooth1 ν ε x = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ν, _hd, _hn, hs, hm⟩ := normalized_smooth_kernel
  obtain ⟨c, _hc, _hceq, below⟩ := h hs hm
  have h1 := below (1 / 2) 5 (by norm_num) (by norm_num) (by norm_num [rejected, realize])
  obtain ⟨d, _hd, hdeq, above⟩ := Smooth1Properties_above hs
  have hd : d ≤ 2 := by rw [hdeq]; linarith [log_two_le_one]
  have h0 := above (1 / 2) 5 (by constructor <;> norm_num) (by linarith)
  rw [h0] at h1
  norm_num at h1

def registration : Registration arena
    (∀ {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
      (mass_one : ∫ x in Ioi 0, ν x / x = 1),
      ∃ c : ℝ, 0 < c ∧ c = Real.log 2 ∧
        ∀ (ε x : ℝ) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε →
          _root_.Smooth1 ν ε x = 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.Smooth1Properties_below, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
    change (1 : ℝ) - 1 * 0 ≠ 1 - 1 * 1
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.Smooth1Properties_below) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ c ε => 1 - c * ε) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Smooth1Properties_below") "Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1/Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ c ε => 1 - c * ε) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, definition := none, coordinates := #[3], readouts := #[{ path := #["body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "body", "body", "domain", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1Properties_below, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.canonicalArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.sourceBridgeFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.observationFact0, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.anchorEnumeration }


end Below

namespace Above

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c ε => 1 + c * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2),
    ∃ c : ℝ, 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x : ℝ) (_ : ε ∈ Ioo 0 1), r.readout () c ε ≤ x →
        _root_.Smooth1 ν ε x = 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ν, _hd, _hn, hs, hm⟩ := normalized_smooth_kernel
  obtain ⟨c, _hc, _hceq, above⟩ := h hs
  have h0 := above (1 / 4) (1 / 4) (by constructor <;> norm_num)
    (by norm_num [rejected, realize])
  obtain ⟨d, _hd, hdeq, below⟩ := Smooth1Properties_below hs hm
  have hd : d ≤ 1 := by rw [hdeq]; exact log_two_le_one
  have h1 := below (1 / 4) (1 / 4) (by norm_num) (by norm_num) (by linarith)
  rw [h0] at h1
  norm_num at h1

def registration : Registration arena
    (∀ {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2),
      ∃ c : ℝ, 0 < c ∧ c = 2 * Real.log 2 ∧
        ∀ (ε x : ℝ) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x →
          _root_.Smooth1 ν ε x = 0) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.Smooth1Properties_above, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
    change (1 : ℝ) + 1 * 0 ≠ 1 + 1 * 1
    norm_num

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.Smooth1Properties_above) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ c ε => 1 + c * ε) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Smooth1Properties_above") "Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1/Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ c ε => 1 + c * ε) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "arg", "body", "arg", "arg", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1Properties_above, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.canonicalArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.sourceBridgeFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.observationFact0, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.anchorEnumeration }


end Above

namespace Transform

abbrev signature : Signature where
  Params := Σ _ : (ℝ → ℝ), ℝ
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => s⁻¹ * mellin (fun x => (p.1 x : ℂ)) (p.2 * s))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re),
    mellin (fun x => (_root_.Smooth1 ν ε x : ℂ)) s = r.readout () ⟨ν, ε⟩ s

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (ν := fun _ => 0) contDiff_const (by simp)
    (ε := 1) (by norm_num) (s := 1) (by norm_num)
  simpa [rejected, realize, smooth1_zero, mellin] using hh

def registration : Registration arena
    (∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
      (suppν : ν.support ⊆ Icc (1 / 2) 2)
      {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re),
      mellin (fun x => (_root_.Smooth1 ν ε x : ℂ)) s =
        s⁻¹ * mellin (fun x => (ν x : ℂ)) (ε * s)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.MellinOfSmooth1a, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let ν : ℝ → ℝ := (Set.Ioc (0 : ℝ) 1).indicator fun _ => 1
    refine ⟨⟨ν, (1 : ℝ)⟩, (1 : ℂ), (2 : ℂ), ?_⟩
    change (1 : ℂ)⁻¹ * mellin (fun x => (ν x : ℂ)) (1 * 1) ≠
      (2 : ℂ)⁻¹ * mellin (fun x => (ν x : ℂ)) (1 * 2)
    have hcast : (fun x => (ν x : ℂ)) =
        (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1 <;>
        simp [ν, Set.indicator_apply, hx]
    rw [hcast]
    simp only [one_mul]
    have h1 := (hasMellin_one_Ioc (s := (1 : ℂ)) (by norm_num)).2
    have h2 := (hasMellin_one_Ioc (s := (2 : ℂ)) (by norm_num)).2
    rw [h1, h2]
    norm_num

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.MellinOfSmooth1a) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p s => s⁻¹ * mellin.{0} (fun x => (p.1 x : ℂ)) (p.2 * s))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "MellinOfSmooth1a") "Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1/Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p s => s⁻¹ * mellin.{0} (fun x => (p.1 x : ℂ)) (p.2 * s))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `MellinOfSmooth1a, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.canonicalArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.sourceBridgeFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.observationFact0, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.anchorEnumeration }


end Transform

namespace Continuity

abbrev signature : Signature where
  Params := Σ _ : (ℝ → ℝ), ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => _root_.Smooth1 p.1 p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => if x = 1 then 1 else 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y),
    ContinuousAt (fun x => r.readout () ⟨ν, ε⟩ x) y

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := h (ν := fun _ => 0) contDiff_const (by simp) (by simp)
    (ε := 1) (by norm_num) (y := 1) (by norm_num)
  change ContinuousAt (fun x : ℝ => if x = 1 then (1 : ℝ) else 0) 1 at hc
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hc (1 / 2) (by norm_num)
  have hx : (1 + δ / 2 : ℝ) ≠ 1 := by linarith
  have hd : dist (1 + δ / 2 : ℝ) 1 < δ := by
    rw [Real.dist_eq, show (1 + δ / 2 : ℝ) - 1 = δ / 2 by ring,
      abs_of_pos (by positivity : 0 < δ / 2)]
    linarith
  have hh := hball hd
  norm_num [hx, Real.dist_eq] at hh

def registration : Registration arena
    (∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
      (νpos : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
      {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y),
      ContinuousAt (fun x => _root_.Smooth1 ν ε x) y) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.Smooth1ContinuousAt, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    obtain ⟨ν, h1, h0⟩ := smooth1_distinct_values
    refine ⟨⟨ν, (1 / 4 : ℝ)⟩, (1 / 4 : ℝ), (5 : ℝ), ?_⟩
    change _root_.Smooth1 ν (1 / 4) (1 / 4) ≠ _root_.Smooth1 ν (1 / 4) 5
    rw [h1, h0]
    norm_num

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.Smooth1ContinuousAt) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p x => _root_.Smooth1 p.1 p.2 x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Smooth1ContinuousAt") "Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1/Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p x => _root_.Smooth1 p.1 p.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, definition := none, coordinates := #[0, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1ContinuousAt, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.canonicalArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.canonicalObjectArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.sourceBridgeFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.observationFact0, `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.anchorEnumeration }


end Continuity
end
end Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1


noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Below\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Below\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Below\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Below\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Above\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Above\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Above\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Above\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Transform\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Transform\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Transform\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Transform\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Continuity\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Continuity\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Continuity\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Continuity\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.arena
    (∀ {ν : Real → Real}
      (suppν :
        @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
          (@Set.Icc.{0} Real Real.instPreorder
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      (mass_one :
        @Eq.{1} Real
          (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
            (@MeasureTheory.Measure.restrict.{0} Real
              (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
              (@Set.Ioi.{0} Real Real.instPreorder
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
            fun (x : Real) =>
            @HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (ν x) x)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
      @Exists.{1} Real fun (c : Real) =>
        And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
          (And
            (@Eq.{1} Real c
              (Real.log
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
            (∀ (ε x : Real),
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  ε →
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    x →
                  @LE.le.{0} Real Real.instLE x
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c ε)) →
                    @Eq.{1} Real (Smooth1 ν ε x)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"Smooth1Properties_below\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Below\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1Properties_below, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.arena
  (∀ {ν : Real → Real}
    (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (mass_one :
      @Eq.{1} Real
        (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@MeasureTheory.Measure.restrict.{0} Real
            (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
            (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
            (@Set.Ioi.{0} Real Real.instPreorder
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
          fun (x : Real) =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (ν x) x)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
    @Exists.{1} Real fun (c : Real) =>
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
        (And
          (@Eq.{1} Real c
            (Real.log
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
          (∀ (ε x : Real),
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  x →
                @LE.le.{0} Real Real.instLE x
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c ε)) →
                  @Eq.{1} Real (Smooth1 ν ε x)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.observation0 : {ν : Real → Real} →
  (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
    (mass_one :
        @Eq.{1} Real
          (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
            (@MeasureTheory.Measure.restrict.{0} Real
              (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
              (@Set.Ioi.{0} Real Real.instPreorder
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
            fun (x : Real) =>
            @HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (ν x) x)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
      (c ε x : Real) →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) x →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.signature PUnit.unit.{1} c :=
  fun {ν : Real → Real}
    (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (mass_one :
      @Eq.{1} Real
        (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@MeasureTheory.Measure.restrict.{0} Real
            (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
            (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
            (@Set.Ioi.{0} Real Real.instPreorder
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
          fun (x : Real) =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (ν x) x)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (c ε x : Real)
    (x_1 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    (a : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) x) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.signature Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.actual
    PUnit.unit.{1} c ε

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Smooth1Properties_below\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Below\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1Properties_below, part := .type, path := [.body, .body, .body, .argument, .body, .argument, .argument, .body, .body, .body, .body, .domain, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Below\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Below\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Smooth1Properties_below\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1Properties_below, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration).actual (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration).variation.2.choose (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration).variation.1 (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Below\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Below\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Below.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.arena
    (∀ {ν : Real → Real}
      (suppν :
        @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
          (@Set.Icc.{0} Real Real.instPreorder
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))),
      @Exists.{1} Real fun (c : Real) =>
        And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
          (And
            (@Eq.{1} Real c
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (Real.log
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
            (∀ (ε x : Real),
              @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                  (@Set.Ioo.{0} Real Real.instPreorder
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                  ε →
                @LE.le.{0} Real Real.instLE
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c ε))
                    x →
                  @Eq.{1} Real (Smooth1 ν ε x)
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"Smooth1Properties_above\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Above\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1Properties_above, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.arena
  (∀ {ν : Real → Real}
    (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))),
    @Exists.{1} Real fun (c : Real) =>
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
        (And
          (@Eq.{1} Real c
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (Real.log
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
          (∀ (ε x : Real),
            @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                (@Set.Ioo.{0} Real Real.instPreorder
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                ε →
              @LE.le.{0} Real Real.instLE
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c ε))
                  x →
                @Eq.{1} Real (Smooth1 ν ε x)
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.observation0 : {ν : Real → Real} →
  (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
    (c ε x : Real) →
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
          (@Set.Ioo.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          ε →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.signature PUnit.unit.{1} c :=
  fun {ν : Real → Real}
    (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (c ε x : Real)
    (x_1 :
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
        (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        ε) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.signature Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.actual
    PUnit.unit.{1} c ε

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Smooth1Properties_above\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"body\",\"body\",\"domain\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Above\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1Properties_above, part := .type, path := [.body, .body, .argument, .body, .argument, .argument, .body, .body, .body, .domain, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Above\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Above\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Smooth1Properties_above\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1Properties_above, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration).actual (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration).variation.2.choose (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration).variation.1 (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Above\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Above\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Above.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.arena
    (∀ {ν : Real → Real}
      (diffν :
        @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
          Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
            (@One.toOfNat1.{0} (WithTop.{0} ENat)
              (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
          ν)
      (suppν :
        @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
          (@Set.Icc.{0} Real Real.instPreorder
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      {ε : Real}
      (εpos : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
      {s : Complex}
      (hs :
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (Complex.re s)),
      @Eq.{1} Complex
        (@mellin.{0} Complex Complex.instNormedAddCommGroup
          (@NonUnitalCStarAlgebra.toNormedSpace.{0} Complex
            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex)))
          (fun (x : Real) => Complex.ofReal (Smooth1 ν ε x)) s)
        (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
          (@Inv.inv.{0} Complex Complex.instInv s)
          (@mellin.{0} Complex Complex.instNormedAddCommGroup
            (@NonUnitalCStarAlgebra.toNormedSpace.{0} Complex
              (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex)))
            (fun (x : Real) => Complex.ofReal (ν x))
            (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (Complex.ofReal ε)
              s))))
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"MellinOfSmooth1a\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Transform\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `MellinOfSmooth1a, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.arena
  (∀ {ν : Real → Real}
    (diffν :
      @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
          (@One.toOfNat1.{0} (WithTop.{0} ENat)
            (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
        ν)
    (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    {ε : Real}
    (εpos : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    {s : Complex}
    (hs :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (Complex.re s)),
    @Eq.{1} Complex
      (@mellin.{0} Complex Complex.instNormedAddCommGroup
        (@NonUnitalCStarAlgebra.toNormedSpace.{0} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex)))
        (fun (x : Real) => Complex.ofReal (Smooth1 ν ε x)) s)
      (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
        (@Inv.inv.{0} Complex Complex.instInv s)
        (@mellin.{0} Complex Complex.instNormedAddCommGroup
          (@NonUnitalCStarAlgebra.toNormedSpace.{0} Complex
            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex)))
          (fun (x : Real) => Complex.ofReal (ν x))
          (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (Complex.ofReal ε) s))))
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.observation0 : {ν : Real → Real} →
  (diffν :
      @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
          (@One.toOfNat1.{0} (WithTop.{0} ENat)
            (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
        ν) →
    (suppν :
        @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
          (@Set.Icc.{0} Real Real.instPreorder
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
      {ε : Real} →
        (εpos :
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε) →
          {s : Complex} →
            (hs :
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (Complex.re s)) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.signature PUnit.unit.{1}
                (@Sigma.mk.{0, 0} (Real → Real) (fun (x : Real → Real) => Real) ν ε) :=
  fun {ν : Real → Real}
    (diffν :
      @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
          (@One.toOfNat1.{0} (WithTop.{0} ENat)
            (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
        ν)
    (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    {ε : Real}
    (εpos : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    {s : Complex}
    (hs :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (Complex.re s)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.signature
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} (Real → Real) (fun (x : Real → Real) => Real) ν ε) s

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"MellinOfSmooth1a\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Transform\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `MellinOfSmooth1a, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Transform\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Transform\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"MellinOfSmooth1a\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `MellinOfSmooth1a, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration).actual (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration).variation.2.choose (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration).variation.1 (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Transform\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Transform\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Transform.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.arena
    (∀ {ν : Real → Real}
      (diffν :
        @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
          Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
            (@One.toOfNat1.{0} (WithTop.{0} ENat)
              (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
          ν)
      (νpos :
        ∀ (x : Real),
          @GT.gt.{0} Real Real.instLT x (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (ν x))
      (suppν :
        @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
          (@Set.Icc.{0} Real Real.instPreorder
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      {ε : Real}
      (εpos : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
      {y : Real}
      (ypos :
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) y),
      @ContinuousAt.{0, 0} Real Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (fun (x : Real) => Smooth1 ν ε x) y)
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"Smooth1ContinuousAt\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Continuity\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1ContinuousAt, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.arena
  (∀ {ν : Real → Real}
    (diffν :
      @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
          (@One.toOfNat1.{0} (WithTop.{0} ENat)
            (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
        ν)
    (νpos :
      ∀ (x : Real),
        @GT.gt.{0} Real Real.instLT x (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (ν x))
    (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    {ε : Real}
    (εpos : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    {y : Real}
    (ypos : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) y),
    @ContinuousAt.{0, 0} Real Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (fun (x : Real) => Smooth1 ν ε x) y)
  Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.observation0 : {SmoothingF : Real → Real} →
  (diffSmoothingF :
      @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
          (@One.toOfNat1.{0} (WithTop.{0} ENat)
            (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
        SmoothingF) →
    (SmoothingFpos :
        ∀ (x : Real),
          @GT.gt.{0} Real Real.instLT x (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (SmoothingF x)) →
      (suppSmoothingF :
          @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero SmoothingF)
            (@Set.Icc.{0} Real Real.instPreorder
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
        {ε : Real} →
          (εpos :
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                ε) →
            {y : Real} →
              (ypos :
                  @LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) y) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
                    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.signature
                    (@Sigma.mk.{0, 0} (Real → Real) (fun (x : Real → Real) => Real) SmoothingF ε) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.signature PUnit.unit.{1}
                    (@Sigma.mk.{0, 0} (Real → Real) (fun (x : Real → Real) => Real) SmoothingF ε) :=
  fun {SmoothingF : Real → Real}
    (diffSmoothingF :
      @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
          (@One.toOfNat1.{0} (WithTop.{0} ENat)
            (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
        SmoothingF)
    (SmoothingFpos :
      ∀ (x : Real),
        @GT.gt.{0} Real Real.instLT x (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (SmoothingF x))
    (suppSmoothingF :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero SmoothingF)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    {ε : Real}
    (εpos : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    {y : Real}
    (ypos :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) y) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.signature
    Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} (Real → Real) (fun (x : Real → Real) => Real) SmoothingF ε)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Smooth1ContinuousAt\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Continuity\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1ContinuousAt, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Continuity\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Continuity\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Smooth1ContinuousAt\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Smooth1ContinuousAt, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration).actual (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration).variation.2.choose (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration).variation.1 (Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Continuity\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"Smooth1\",\"Continuity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1.Continuity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
