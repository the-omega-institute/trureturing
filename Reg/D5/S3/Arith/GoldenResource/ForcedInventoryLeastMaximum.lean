import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.ForcedInventoryLeastMaximum
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection

namespace Reg.D5.S3.Arith.GoldenResource.ForcedInventoryLeastMaximum

open _root_.D5.S3.Arith.GoldenResource.ForcedInventoryLeastMaximum
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m C => Nat.lcm m C) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

-- The divisibility conclusion observes the forced LCM. The entire maximum
-- conjunct, every original premise and every universal domain remain literal.
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lambda : ℝ}, 0 < lambda → ∀ {m C : ℕ}, 1 ≤ m → 1 ≤ C →
    (∀ q : ℕ, C.factorization q = optimalLayerCount lambda q) →
    (∀ n : ℕ, m ∣ n → 1 ≤ n →
      goldenResourceObjective lambda n ≤
        goldenResourceObjective lambda (Nat.lcm m C)) ∧
    (∀ n : ℕ, m ∣ n → 1 ≤ n →
      (∀ k : ℕ, m ∣ k → 1 ≤ k →
        goldenResourceObjective lambda k ≤ goldenResourceObjective lambda n) →
      R.readout () m C ∣ n)

theorem bridge : (type_of% @forced_inventory_least_maximum) ↔ arena.Law actual :=
  Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C, hC, hcounts, _⟩ := optimal_layer_count_spec (by norm_num : (0 : ℝ) < 1)
  have hmax := (forced_inventory_least_maximum (by norm_num : (0 : ℝ) < 1)
    (m := 1) (by norm_num) hC hcounts).1
  simp only [Nat.lcm_one_left] at hmax
  have hbad := (h (lambda := 1) (by norm_num) (m := 1) (C := C)
    (by norm_num) hC hcounts).2 C (one_dvd C) hC hmax
  change 0 ∣ C at hbad
  have hzero := (zero_dvd_iff.mp hbad)
  omega

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  change Nat.lcm 1 1 ≠ Nat.lcm 1 2
  norm_num

def familyRegistration : Registration arena (type_of% @forced_inventory_least_maximum) where
  actual := actual
  bridge := bridge
  variation := ⟨forced_inventory_least_maximum, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := actual_dependence

-- The source selection addresses the literal Nat.lcm in the divisibility
-- conclusion, with m as a parameter and C as the observed state.
def audit : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@forced_inventory_least_maximum) (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Arith.GoldenResource.ForcedInventoryLeastMaximum.forced_inventory_least_maximum "audit"
  realizationName := `Reg.D5.S3.Arith.GoldenResource.ForcedInventoryLeastMaximum.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.GoldenResource.ForcedInventoryLeastMaximum
    definition := none
    coordinates := #[2]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body",
          "arg", "body", "body", "body", "body", "fn", "arg"],
        stateBinder := 3, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms bridge
#print axioms rejected_law
#print axioms familyRegistration

end
end Reg.D5.S3.Arith.GoldenResource.ForcedInventoryLeastMaximum
