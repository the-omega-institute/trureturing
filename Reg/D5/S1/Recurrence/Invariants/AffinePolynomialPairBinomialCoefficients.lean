import D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
namespace Reg.D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
open _root_.D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℤ)

abbrev actual : Realization signature :=
  realize signature (fun _ n k => ((pair (n - 1)).2).coeff k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ,
    R.readout () n k =
      (Nat.choose (n - 1) (2*k+1) : ℤ) + (Nat.choose n (2*k+1) : ℤ)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) 0
  norm_num [rejected, realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize, pair, Polynomial.coeff_one]

def family : Registration arena (type_of% (@werner_a208509)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨werner_a208509, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@werner_a208509) (Realization signature) (Type) Unit where
  unitName := `D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients.werner_a208509.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n k => ((pair (n - 1)).2).coeff k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
