import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight
import Reg.Support.DependentFamily

open D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight
open D5.S3.Quantum.Measurement.AntidistinguishabilityGram
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => IsTight n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 10 ≤ n → ¬ R.readout () () n

private theorem zeroTight : IsTight 0 := by
  intro e he
  refine ⟨1, Fin.elim0, ?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · rintro ⟨M, hp, hs, hz⟩
    have hh := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => A 0 0) hs
    norm_num at hh

theorem positive : arena.Law actual := result
theorem negative : ¬ arena.Law rejected := by
  intro h
  exact h 10 (by decide) trivial

def evidence : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 10, ?_⟩
    change IsTight 0 ≠ IsTight 10
    intro h
    exact result 10 (by decide) (h ▸ zeroTight)

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result)
    (type_of% (realize signature (fun _ _ n => IsTight n) (fun e => nomatch e)))
    Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight.result.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => IsTight n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some ℕ,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight,
    definition := some {
      owner := `D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight,
      name := `D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight.claim, path := #[] },
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "arg"],
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
end Reg.D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight
