import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.TruncatedPolynomialCyclicCriterion
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! The complete cyclic projectivity criterion with a variable coefficient readout. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra.TruncatedPolynomialCyclicCriterion
open Polynomial
open scoped MonoidAlgebra

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.TruncatedPolynomialCyclicCriterion

universe uR uA
noncomputable section

/-- Ring and algebra dictionaries are coordinates; the polynomial is the state. -/
abbrev signature : Signature where
  Params := Σ R : Type uR, Σ A : Type uA, Σ _ : CommRing R,
    Σ _ : CommRing A, Algebra R A
  State p := letI := p.2.2.2.1; Polynomial p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uR,uA} :=
  realize signature (fun _ p h => letI := p.2.2.2.1; h.coeff 1)
    (fun e => nomatch e)

def rejected : Realization signature.{uR,uA} :=
  realize signature (fun _ p _ => letI := p.2.2.2.1; (0 : p.2.1))
    (fun e => nomatch e)

/-- The complete original telescope and actual cyclic action remain fixed. -/
abbrev arena : Arena where
  signature := signature.{uR,uA}
  Law r := ∀ {R : Type uR} [rr : CommRing R] {A : Type uA} [aa : CommRing A]
    [alg : Algebra R A] {p : ℕ} [Fact p.Prime]
    (hpA : (p : A) = 0) (h : A[X]) (h0 : h.coeff 0 = 0),
    Module.Projective R[Multiplicative (ZMod p)]
        (cyclicAction (R := R) hpA h h0).asModule ↔
      Module.Projective R A ∧ IsUnit (r.readout () ⟨R, A, rr, aa, alg⟩ h)

private abbrev testR := ULift.{uR} (ZMod 2)
private abbrev testA := ULift.{uA} (ZMod 2)
private def testEquiv : testR.{uR} ≃+* testA.{uA} :=
  ULift.ringEquiv.trans ULift.ringEquiv.symm
private instance testAlgebra : Algebra testR.{uR} testA.{uA} :=
  testEquiv.toRingHom.toAlgebra

private theorem rejected_law : ¬ arena.{uR,uA}.Law rejected := by
  intro hbad
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpA : (2 : testA.{uA}) = 0 := by
    apply ULift.ext
    change (2 : ZMod 2) = 0
    decide
  have h0 : (X : testA.{uA}[X]).coeff 0 = 0 := by simp
  have hproj : Module.Projective testR.{uR}[Multiplicative (ZMod 2)]
      (cyclicAction (R := testR.{uR}) hpA X h0).asModule :=
    (projective_iff_projective_coeff_and_isUnit_coeff_one hpA X h0).mpr
      ⟨inferInstance, by simp⟩
  have hunit := (hbad hpA X h0).mp hproj |>.2
  simp [rejected, realize] at hunit

def family : Registration arena.{uR,uA}
    (type_of% (@projective_iff_projective_coeff_and_isUnit_coeff_one.{uR,uA})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@projective_iff_projective_coeff_and_isUnit_coeff_one.{uR,uA},
    rejected, rejected_law⟩
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
    refine ⟨⟨testR.{uR}, testA.{uA}, inferInstance, inferInstance, testAlgebra⟩,
      (0 : testA.{uA}[X]), X, ?_⟩
    simp [actual, realize]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@projective_iff_projective_coeff_and_isUnit_coeff_one.{uR,uA})
    (Realization signature.{uR,uA}) Unit Unit where
  unitName :=
    `D5.S3.FiniteGroups.GroupAlgebra.TruncatedPolynomialCyclicCriterion.projective_iff_projective_coeff_and_isUnit_coeff_one.__information_unit
  realizationName :=
    `Reg.D5.S3.FiniteGroups.GroupAlgebra.TruncatedPolynomialCyclicCriterion.family
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
    owner := `D5.S3.FiniteGroups.GroupAlgebra.TruncatedPolynomialCyclicCriterion
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.TruncatedPolynomialCyclicCriterion
