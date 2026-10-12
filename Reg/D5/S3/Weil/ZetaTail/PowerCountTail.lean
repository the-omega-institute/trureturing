import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaTail.PowerCountTail
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.ZetaTail.PowerCountTail

open _root_.D5.S3.Weil.ZetaTail.PowerCountTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
universe u

@[reducible] def signature : Signature where
  Params := Type u
  State ι := ι → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ ι := ι → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def emptyAnchor (e : Empty) (ι : Type u) : ι → ℝ := nomatch e

def actual : Realization signature :=
  realize signature (fun _ _ m => m) emptyAnchor

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) emptyAnchor

/-- Keep the complete original telescope and raw hypotheses. The observation is
the mass operand in the total bound; convergence retains the original masses. -/
@[reducible] def arena : Arena where
  signature := signature.{u}
  Law O := ∀ {ι : Type u} (g m : ι → ℝ) {Y C p a : ℝ},
    0 < Y → 0 ≤ C → 0 < p → a < p → (∀ i, 0 ≤ m i) →
    (∀ v : ℝ, Y ≤ v → ∀ s : Finset ι,
      (∀ i ∈ s, g i < v) → ∑ i ∈ s, m i ≤ C * v ^ a) →
    Summable (fun i => if Y ≤ g i then m i * (g i) ^ (-p) else 0) ∧
    (∑' i, if Y ≤ g i then
      (O.readout () ι m) i * (g i) ^ (-p) else 0) ≤
      (p * C / (p - a)) * Y ^ (a - p)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => 0)
    (Y := 1) (C := 0) (p := 1) (a := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp) (by simp)
  have hbad := hb.2
  norm_num [rejected, realize, signature, tsum_fintype] at hbad

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrFun h (ULift.up ())
  norm_num [actual, realize, signature] at he

def sourceRegistration :
    Registration arena.{u} (type_of% (@inverse_power_tail_of_raw_count.{u})) where
  actual := realize signature (fun _ _ m => m) emptyAnchor
  bridge := Iff.rfl
  variation := ⟨inverse_power_tail_of_raw_count, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,0,1,0,0,0,u+1,u,0,u,0,0}
    (@inverse_power_tail_of_raw_count.{u})
    (type_of% (realize signature.{u} (fun _ _ m => m) emptyAnchor)) Unit Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaTail.PowerCountTail.inverse_power_tail_of_raw_count,
  realizationName := `Reg.D5.S3.Weil.ZetaTail.PowerCountTail.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ m => m) emptyAnchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaTail.PowerCountTail,
    definition := none,
    coordinates := #[0],
    readouts := #[
      { path := #[
          "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "body", "body", "body",
          "arg", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg", "fn"],
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#check Reg.Support.DependentFamily.enrollment_1
#print axioms sourceRegistration
#print axioms registration_1

end
end Reg.D5.S3.Weil.ZetaTail.PowerCountTail
