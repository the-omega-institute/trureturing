import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification
import Reg.Support.DependentFamily
set_option autoImplicit false
namespace Reg.D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification
open _root_.CubicCirculant
open _root_.WellCoveredPowerCliqueProduct (WellCovered)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation (graphPower)
open scoped Classical
noncomputable section
namespace FirstPower
abbrev signature : Signature.{0,0,0,0,0} where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ n a => decide (WellCovered (cubic n a))) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ (n a : ℕ) (hn : 4 ≤ n) (hne : Even n) (ha : 1 ≤ a) (halt : a < n/2),
    R.readout () n a = true ↔ n / Nat.gcd n a ∈ ({3,4,5,6,8} : Set ℕ)

private lemma source_law : arena.Law actual := by
  intro n a hn hne ha halt
  change decide (WellCovered (cubic n a)) = true ↔ _
  rw [decide_eq_true_eq]
  exact first_wellCovered_iff n a hn hne ha halt
private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := (h 4 1 (by omega) (by decide) (by omega) (by omega)).mpr (by norm_num)
  exact Bool.false_ne_true hh

def registration : Registration arena (type_of% (@_root_.CubicCirculant.first_wellCovered_iff)) where
  actual := actual
  bridge := by simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨source_law,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨12,1,2,?_⟩
    have hn : ¬ WellCovered (cubic 12 1) := by
      rw [first_wellCovered_iff 12 1 (by omega) (by decide) (by omega) (by omega)]
      norm_num
    have hy : WellCovered (cubic 12 2) := by
      rw [first_wellCovered_iff 12 2 (by omega) (by decide) (by omega) (by omega)]
      norm_num
    change decide (WellCovered (cubic 12 1)) ≠ decide (WellCovered (cubic 12 2))
    rw [decide_eq_false hn,decide_eq_true hy]
    decide

def contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.CubicCirculant.first_wellCovered_iff)
    (type_of% (realize signature (fun _ n a => decide (WellCovered (cubic n a))) (fun e => nomatch e)))
    Type Unit := {
  unitName := Lean.Name.str (Lean.Name.str `CubicCirculant.first_wellCovered_iff
    "Reg.D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification/Reg.D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification.FirstPower.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification.FirstPower.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => decide (WellCovered (cubic n a))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg","arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit,value := .bool false }] }
#print axioms registration
#print axioms contract
end FirstPower
namespace AllPowers
abbrev signature : Signature.{0,0,0,0,0} where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ n a => decide (WellCovered (cubic n a))) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ (n a : ℕ) (hn : 4 ≤ n) (hne : Even n) (ha : 1 ≤ a) (halt : a < n/2),
    ((∀ d : ℕ, 1 ≤ d → WellCovered (graphPower (cubic n a) d)) ↔ R.readout () n a = true) ∧
      (WellCovered (cubic n a) ↔ n / Nat.gcd n a ∈ ({3,4,5,6,8} : Set ℕ))

private lemma source_law : arena.Law actual := by
  intro n a hn hne ha halt
  change ((∀ d : ℕ, 1 ≤ d → WellCovered (graphPower (cubic n a) d)) ↔ decide (WellCovered (cubic n a)) = true) ∧ _
  rw [decide_eq_true_eq]
  exact all_powers_iff n a hn hne ha halt
private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hy : WellCovered (cubic 4 1) :=
    (first_wellCovered_iff 4 1 (by omega) (by decide) (by omega) (by omega)).mpr (by norm_num)
  have hp := (all_powers_iff 4 1 (by omega) (by decide) (by omega) (by omega)).1.mpr hy
  have hh := (h 4 1 (by omega) (by decide) (by omega) (by omega)).1.mp hp
  exact Bool.false_ne_true hh

def registration : Registration arena (type_of% (@_root_.CubicCirculant.all_powers_iff)) where
  actual := actual
  bridge := by simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨source_law,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨12,1,2,?_⟩
    have hn : ¬ WellCovered (cubic 12 1) := by
      rw [first_wellCovered_iff 12 1 (by omega) (by decide) (by omega) (by omega)]
      norm_num
    have hy : WellCovered (cubic 12 2) := by
      rw [first_wellCovered_iff 12 2 (by omega) (by decide) (by omega) (by omega)]
      norm_num
    change decide (WellCovered (cubic 12 1)) ≠ decide (WellCovered (cubic 12 2))
    rw [decide_eq_false hn,decide_eq_true hy]
    decide

def contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.CubicCirculant.all_powers_iff)
    (type_of% (realize signature (fun _ n a => decide (WellCovered (cubic n a))) (fun e => nomatch e)))
    Type Unit := {
  unitName := Lean.Name.str (Lean.Name.str `CubicCirculant.all_powers_iff
    "Reg.D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification/Reg.D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification.AllPowers.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification.AllPowers.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => decide (WellCovered (cubic n a))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg","arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit,value := .bool false }] }
#print axioms registration
#print axioms contract
end AllPowers
end
end Reg.D5.S3.Combinatorics.Graph.Walks.CubicPowerClassification
