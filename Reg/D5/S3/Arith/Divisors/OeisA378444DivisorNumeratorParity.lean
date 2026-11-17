import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity

open _root_.D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => A378444 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n → R.readout () () n = ⌈(A174273 n : ℚ) / 2⌉₊

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide)
  change 0 = ⌈(A174273 1 : ℚ) / 2⌉₊ at hh
  norm_num [A174273, A035263, Finset.filter_singleton, Nat.factorization_one] at hh
  have hc := Nat.le_ceil ((1 : ℚ) / 2)
  rw [← hh] at hc
  norm_num at hc

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 9, ?_⟩
  change A378444 1 ≠ A378444 9
  have hp : Nat.Prime 3 := by decide
  have hf9 : (9 : ℕ).factorization = Finsupp.single 3 2 := by
    simpa using (hp.factorization_pow (k := 2))
  have hd9 : (9 : ℕ).divisors = {1, 3, 9} := by
    rw [show (9 : ℕ) = 3 ^ 2 from rfl, Nat.divisors_prime_pow hp]
    norm_num [Finset.range_add_one]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have h13 : ((1 : ℚ) / 3).num = 1 := by
    exact Rat.num_div_eq_of_coprime (a := 1) (b := 3) (by decide) (by decide)
  have h23 : ((2 : ℚ) / 3).num = 2 := by
    exact Rat.num_div_eq_of_coprime (a := 2) (b := 3) (by decide) (by decide)
  norm_num [A378444, A083345, r, hd9, hf9, hp.factorization,
    Finset.filter_insert, Finset.filter_singleton, h13, h23]

def sourceRegistration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity.result)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity.unit
  realizationName := `Reg.D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => A378444 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity
    definition := some {
      owner := `D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity
      name := `D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity
