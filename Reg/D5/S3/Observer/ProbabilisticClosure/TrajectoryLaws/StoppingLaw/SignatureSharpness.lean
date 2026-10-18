import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureSharpness
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureSharpness
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace ExactSignature

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
  Law R := ∀ (j : Bool) (k : ℕ) (hk : 1 ≤ k),
    signatureRadius j k = R.readout () () k ∧
    let W := completePathTree (!j) k (j.toInt + 1)
    W.height = k ∧ W.potentialReadCount = 2 ^ k - 1 ∧
    (∀ T' : ReadTree, SameSignature j W T' →
      ∃ t ∈ T'.addresses, ((2 ^ (k + 1) - 1 : ℕ) : ℤ) ≤ |t - j.toInt|) ∧
    (repeatTargetTree j k).height = k ∧
    (∀ t ∈ (repeatTargetTree j k).addresses, t = j.toInt) ∧
    (∀ (U : Type u) [MeasurableSpace U] (ν : Measure U) (β : Bias),
      let R := RawRule.realize (fun _ : U => repeatTargetTree j k)
      R.Lawful ∧ R.TotalCap k ∧ R.WithinActualRadius j 0 ∧
        R.fullLaw β j ν =
          (RawRule.realize (fun _ : U => W)).fullLaw β j ν)

private theorem actual_law : arena.{u}.Law actual := @exact_signature_radius_with_law_zero_witness.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := (h false 1 (by decide)).1
  have hx := (exact_signature_radius_with_law_zero_witness.{u} false 1 (by decide)).1
  change signatureRadius false 1 = 0 at hb
  norm_num at hx
  omega

def evidence : Registration arena.{u} (type_of% (@exact_signature_radius_with_law_zero_witness.{u})) where
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
    (@exact_signature_radius_with_law_zero_witness.{u})
    (type_of% (realize signature (fun _ _ k => 2 ^ (k + 1) - 1) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureSharpness.ExactSignature.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureSharpness.ExactSignature.evidence,
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
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureSharpness,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"],
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

end ExactSignature

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureSharpness
