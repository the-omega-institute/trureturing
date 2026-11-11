import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.FiniteJetAudit

/-! Source-faithful dependent-family audit evidence for finite original jets. -/

set_option autoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra
open FiniteJetCoefficients FiniteJetClassification FiniteJetOrbits OddPrimeJetDeformation
open Reg.Support.FiniteJetAudit
open scoped BigOperators
noncomputable section
universe u
namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits
namespace original_class_cardinality
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun _ => CountData.{u}) (fun _ => ℚ)
def actual : Realization signature.{u} := realize signature
  (fun _ _ s => (Nat.card (OriginalClasses (p := s.p) (K := s.K)) : ℚ))
  (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature
  (fun i s x => actual.readout i s x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type u} [fk : Field K] [ft : Fintype K] [ak : Algebra (ZMod p) K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n),
    f.readout () () ⟨⟨⟨p,K,n⟩,hn,hK⟩⟩ =
      (1 / (n : ℚ)) *
        ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) / (p ^ d - 1 : ℕ) *
          ∑ m ∈ (p ^ d - 1).divisors, (Nat.totient m : ℚ) *
            (p : ℚ) ^ (d * (Finset.univ.filter (fun i : Fin (n - 1) => m ∣ weight p n i)).card)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h (p := 3) (K := ULift.{u} (ZMod 3)) (n := 1) (by decide) (by simp)
  have ha := FiniteJetOrbits.original_class_cardinality
    (p := 3) (K := ULift.{u} (ZMod 3)) (n := 1) (by decide) (by simp)
  dsimp only [rejected, actual, realize] at hb
  linarith
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(),threeCount,nineCount,?_⟩
  have h1 := FiniteJetOrbits.original_class_cardinality
    (p := 3) (K := ULift.{u} (ZMod 3)) (n := 1) (by decide) (by simp)
  have h2 := FiniteJetOrbits.original_class_cardinality
    (p := 3) (K := Nine.{u}) (n := 2) (by decide) nine_card
  have d2 : Nat.divisors 2 = {1,2} := by decide
  have d8 : Nat.divisors 8 = {1,2,4,8} := by decide
  have t4 : Nat.totient 4 = 2 := by decide
  have t8 : Nat.totient 8 = 4 := by decide
  norm_num [d2, d8, t4, t8, weight, Finset.filter_true_of_mem] at h1 h2
  dsimp only [actual, realize, threeCount, nineCount, nineSized, nine]
  rw [h1,h2]
  norm_num

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits.original_class_cardinality.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits.original_class_cardinality.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits.original_class_cardinality.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits.original_class_cardinality.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits.original_class_cardinality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_class_cardinality
end Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits
