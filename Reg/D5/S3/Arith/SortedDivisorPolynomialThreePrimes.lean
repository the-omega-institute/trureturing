import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.SortedDivisorPolynomialThreePrimes
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.SortedDivisorPolynomialThreePrimes

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev predicate (n : ℕ) : Prop :=
  0 < n ∧ n.primeFactors.card = 3 ∧
    ∃ f : Polynomial ℤ, ∀ (j : ℕ) (hj : j < n.divisors.card),
      f.eval (j : ℤ) =
        ((n.divisors.sort (· ≤ ·)).get
          ⟨j, by simpa only [Finset.length_sort] using hj⟩ : ℤ)

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => predicate n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ n : ℕ, R.readout () () n

theorem actual_law : arena.Law actual :=
  _root_.D5.S3.Arith.SortedDivisorPolynomialThreePrimes.result

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨_, h⟩
  exact h

theorem dependence : ObservationalDependence signature actual := by
  intro _
  obtain ⟨n, hn⟩ := actual_law
  refine ⟨(), n, 0, ?_⟩
  change predicate n ≠ predicate 0
  intro h
  have hz : predicate 0 := h ▸ hn
  exact (Nat.lt_irrefl 0) hz.1

def registration : Registration arena
    (type_of% _root_.D5.S3.Arith.SortedDivisorPolynomialThreePrimes.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.SortedDivisorPolynomialThreePrimes.result)
    (type_of% (realize signature (fun _ _ n => predicate n) (fun e => nomatch e)))
    Type Unit := {
  unitName := `Reg.D5.S3.Arith.SortedDivisorPolynomialThreePrimes.result.__information_unit,
  realizationName := `Reg.D5.S3.Arith.SortedDivisorPolynomialThreePrimes.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => predicate n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.SortedDivisorPolynomialThreePrimes,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Arith.SortedDivisorPolynomialThreePrimes
