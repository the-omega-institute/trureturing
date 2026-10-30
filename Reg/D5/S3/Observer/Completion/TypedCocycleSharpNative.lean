import D5.S3.Observer.Completion.TypedCocycleSharpNative
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Observer.Completion.TypedCocycleSource
open D5.S3.Observer.Completion.TypedCocycleSharpNative
namespace Reg.D5.S3.Observer.Completion.TypedCocycleSharpNative

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ h ε => quantum h ε) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law f := ∀ (h ε : ℝ), 0 < h → 0 < ε → ∀ C E : Vector,
    LeastCost (StaticCost h ε C E) ((f.readout () h ε) ^ 2) ∧
    LeastCost (OnlineCost h ε C E) ((f.readout () h ε) ^ 2) ∧
    (Feasible h ε C E (fun _ : History => ()) ↔ 2 * ε < h) ∧
    (∀ k : ℕ, (k : ℝ) * h ≤ 2 * ε → 2 * ε < (k + 1 : ℕ) * h →
      f.readout () h ε = k + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hn := (law 1 (1/4) (by norm_num) (by norm_num) (0,0) (0,0)).2.2.2 0
    (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hn

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1/4, 1, ?_⟩
  norm_num [actual, realize, quantum]
  rw [show ⌊(1 / 2 : ℝ)⌋₊ = 0 from Nat.floor_eq_zero.mpr (by norm_num)]
  norm_num

def family : Registration arena (type_of% (@whole_sharp_native_law)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_sharp_native_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@whole_sharp_native_law) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.Completion.TypedCocycleSharpNative.whole_sharp_native_law.__information_unit
  realizationName := `Reg.D5.S3.Observer.Completion.TypedCocycleSharpNative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ h ε => quantum h ε) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Completion.TypedCocycleSharpNative
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Reg.D5.S3.Observer.Completion.TypedCocycleSharpNative
