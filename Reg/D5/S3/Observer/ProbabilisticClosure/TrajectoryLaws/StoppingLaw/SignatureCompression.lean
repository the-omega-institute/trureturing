import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := Bool
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j T => compressedTree j T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .leaf none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j : Bool) (T : ReadTree) (k : ℕ), T.height ≤ k →
    SameSignature j T (R.readout () j T) ∧ (compressedTree j T).height = T.height ∧
      ∀ t ∈ (compressedTree j T).addresses,
        j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤ t ∧
          t ≤ j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1

private theorem actual_law : arena.Law actual := bounded_signature_relabeling

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h false (.read 0 (.leaf none) (.leaf none)) 1 (by decide)).1.1
  simp [rejected, realize, ReadTree.paritySkeleton] at hb

def evidence : Registration arena (type_of% (@bounded_signature_relabeling)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨false, .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    intro he
    have hx := congrArg ReadTree.height he
    change (compressedTree false (.leaf none)).height =
      (compressedTree false (.read 0 (.leaf none) (.leaf none))).height at hx
    rw [(bounded_signature_relabeling false (.leaf none) 0 (by decide)).2.1,
      (bounded_signature_relabeling false (.read 0 (.leaf none) (.leaf none)) 1 (by decide)).2.1] at hx
    norm_num [ReadTree.height] at hx

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_signature_relabeling)
    (type_of% (realize signature (fun _ j T => compressedTree j T) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ j T => compressedTree j T) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

namespace CompletedCompression

open MeasureTheory
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => 2 ^ (k + 1) - 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν] (β : Bias) (j : Bool) (k : ℕ),
    (∀ Q : CompletedRule U, Q.Lawful ((sourceLaw β).prod ν) → Q.TotalCap k →
      ∃ R : RawRule U, R.Lawful ∧ R.TotalCap k ∧ R.fullLaw β j ν = Q.fullLaw β j ν ∧
      R.WithinActualRadius j (2 ^ (k + 1) - 1) ∧
      (k = 0 → R.WithinActualRadius j 0) ∧
      ∀ u : U, (R.normalize k u).height ≤ k ∧
        ∀ t ∈ (R.normalize k u).addresses,
          j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤ t ∧
            t ≤ j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1) ∧
    rhoLaw β j ν 0 = 0 ∧ rhoLaw β j ν 1 = 3 ∧
    (1 ≤ k → 2 * k + 1 ≤ rhoLaw β j ν k) ∧
    rhoLaw β j ν k ≤ R.readout () () k

private theorem actual_law : arena.{u}.Law actual := @completed_rule_uniform_compression.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hb := h ν β false 1
  have hx := hb.2.2.1
  have hz := hb.2.2.2.2
  change rhoLaw β false ν 1 ≤ 0 at hz
  rw [hx] at hz
  omega

def evidence : Registration arena.{u} (type_of% (@completed_rule_uniform_compression.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completed_rule_uniform_compression.{u})
    (type_of% (realize signature (fun _ _ k => 2 ^ (k + 1) - 1) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression.CompletedCompression.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression.CompletedCompression.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ k => 2 ^ (k + 1) - 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg"],
      stateBinder := 6, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end CompletedCompression

namespace ActualRadius

universe u

abbrev signature : Signature where
  Params := Bool
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j t => |t - j.toInt|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ {U : Type u} [MeasurableSpace U] (R : RawRule U) (k : ℕ)
    (hc : R.TotalCap k) (j : Bool) (ρ : ℕ),
    (∀ u : U, ∀ t ∈ (R.normalize k u).addresses, A.readout () j t ≤ (ρ : ℤ)) →
      R.WithinActualRadius j ρ

private theorem actual_law : arena.{u}.Law actual := @normalized_actual_radius.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .read 1 (.leaf none) (.leaf none)
  let Q := RawRule.realize T
  have hc : Q.TotalCap 1 := RawRule.realize_cap T 1 (fun _ => by decide)
  have hrad := h Q 1 hc false 0 (fun _ _ _ => by norm_num [rejected, realize])
  have hp : Q.readPrefix (ULift.up ()) (visible false (fun _ => false)) 1 = some [(1, false)] := by
    simp [Q, T, RawRule.readPrefix, RawRule.realize, ReadTree.eventAfter, ReadTree.follow, constant_visible]
  have hb := hrad false (fun _ => false) (ULift.up ()) 1 [(1, false)] hp (1, false) (by simp)
  norm_num at hb

def evidence : Registration arena.{u} (type_of% (@normalized_actual_radius.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    exact ⟨false, 0, 1, by norm_num [actual, realize]⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_actual_radius.{u})
    (type_of% (realize signature (fun _ j t => |t - j.toInt|) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression.ActualRadius.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression.ActualRadius.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ j t => |t - j.toInt|) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression,
    definition := none,
    coordinates := #[5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "body", "fn", "arg"],
      stateBinder := 8, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end ActualRadius

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression
