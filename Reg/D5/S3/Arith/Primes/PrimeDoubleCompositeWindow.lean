import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.PrimeDoubleCompositeWindow
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Primes.PrimeDoubleCompositeWindow

open _root_.D5.S3.Arith.Primes.PrimeDoubleCompositeWindow
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 2 * n) (fun e => nomatch e)

/-- Only the numerical center in the lower window endpoint is observed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ H B : ℕ, ∃ p : ℕ, B < p ∧ H < p ∧ p.Prime ∧
    ∀ t : ℕ, R.readout () () p - H ≤ t → t ≤ 2 * p + H → ¬t.Prime

def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem erased_fails : ¬arena.Law erased := by
  intro h
  obtain ⟨p, hBp, hHp, hp, hwin⟩ := h 0 0
  have hpp : 2 ≤ p := hp.two_le
  have hupper : 2 ≤ 2 * p + 0 := by omega
  have hbad := hwin 2 (by change (0 : ℕ) ≤ 2; omega) hupper
  exact hbad Nat.prime_two

def family : Registration arena (type_of% (@exists_prime_double_composite_window)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_prime_double_composite_window, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hji
      change Unit at i j
      cases i
      cases j
      exact (hji rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change (2 * 0 : ℕ) ≠ 2 * 1
    norm_num

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_prime_double_composite_window) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Primes.PrimeDoubleCompositeWindow.exists_prime_double_composite_window.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.PrimeDoubleCompositeWindow.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => 2 * n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.PrimeDoubleCompositeWindow
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "arg", "body", "arg", "arg", "arg", "body", "domain", "fn", "arg", "fn", "arg"]
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Primes.PrimeDoubleCompositeWindow
