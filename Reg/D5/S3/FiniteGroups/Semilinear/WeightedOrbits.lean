import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Semilinear.WeightedOrbits
import Reg.Support.DependentFamily

set_option autoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open WeightedSemilinear
open scoped Classical
namespace Reg.D5.S3.FiniteGroups.Semilinear.WeightedOrbits
noncomputable section
universe u
namespace orbit_cardinality
structure Scope where
  p : ℕ
  n : ℕ
  [prime : Fact p.Prime]
  L : Type
  [fieldL : Field L]
  [finiteL : Fintype L]
  [algebraL : Algebra (ZMod p) L]
  J : Type u
  [finiteJ : Fintype J]
  hL : Fintype.card L = p ^ n
attribute [instance] Scope.prime Scope.fieldL Scope.finiteL Scope.algebraL Scope.finiteJ

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.J → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p x => (Nat.card (Orbits (F := ZMod p.p) (K := p.L) x) : ℚ)) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun i p x => actual.readout i p x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (p n : ℕ) [fp : Fact p.Prime] {L : Type} [fl : Field L]
    [nl : Fintype L] [al : Algebra (ZMod p) L] {J : Type u} [fj : Fintype J]
    (weights : J → ℕ) (hL : Fintype.card L = p ^ n),
    r.readout () ⟨p,n,L,J,hL⟩ weights =
      (1 / (n : ℚ)) *
        ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) / (p ^ d - 1 : ℕ) *
          ∑ m ∈ (p ^ d - 1).divisors, (Nat.totient m : ℚ) *
            (p : ℚ) ^ (d * (Finset.univ.filter (fun i => m ∣ weights i)).card)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hb := h 2 1 (L := ZMod 2) (J := PUnit.{u+1}) (fun _ => 0) (by norm_num)
  have hp := WeightedSemilinear.orbit_cardinality 2 1 (L := ZMod 2) (J := PUnit.{u+1}) (fun _ => 0) (by norm_num)
  simp only [rejected, realize, actual] at hb
  linarith
def family : Registration arena.{u} (type_of% (@WeightedSemilinear.orbit_cardinality.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WeightedSemilinear.orbit_cardinality, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hL : Fintype.card (ZMod 3) = 3 ^ 1 := by norm_num
    refine ⟨⟨3,1,ZMod 3,PUnit.{u+1},hL⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hzero := WeightedSemilinear.orbit_cardinality 3 1 (L := ZMod 3) (J := PUnit.{u+1}) (fun _ => 0) hL
    have hone := WeightedSemilinear.orbit_cardinality 3 1 (L := ZMod 3) (J := PUnit.{u+1}) (fun _ => 1) hL
    have hd : Nat.divisors 2 = {1,2} := by decide
    norm_num [hd] at hzero hone
    dsimp only [actual, realize]
    linarith

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WeightedSemilinear.orbit_cardinality.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `WeightedSemilinear.orbit_cardinality.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Semilinear.WeightedOrbits.orbit_cardinality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Semilinear.WeightedOrbits
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,10]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end orbit_cardinality
end
end Reg.D5.S3.FiniteGroups.Semilinear.WeightedOrbits
