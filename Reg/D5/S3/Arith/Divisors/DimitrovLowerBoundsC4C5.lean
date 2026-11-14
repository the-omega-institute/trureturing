import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5
import Reg.Support.DependentFamily

/-! Source bindings for the original arithmetic and mixed-power bounds. -/

namespace Reg.D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

open _root_.D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5
open _root_.D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes (psi)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev psiSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev psiArena : Arena where
  signature := psiSignature
  Law R := ∀ {n : ℕ}, 2 ≤ n → n + 1 ≤ R.readout () () n

def psiActual : Realization psiSignature :=
  realize psiSignature (fun _ _ n => psi n) (fun e => nomatch e)

def psiRejected : Realization psiSignature :=
  realize psiSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem psiRejected_law : ¬ psiArena.Law psiRejected := by
  intro h
  have hbad := h (n := 2) (by norm_num)
  norm_num [psiRejected, realize, psi, Nat.primeFactors] at hbad

def psiRegistration : Registration psiArena (∀ {n : ℕ}, 2 ≤ n → n + 1 ≤ psi n) where
  actual := psiActual
  bridge := Iff.rfl
  variation := ⟨psi_ge, psiRejected, psiRejected_law⟩
  sensitivity := ⟨fun i => ⟨psiRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), psiRejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [psiActual, realize, psi, Nat.primeFactors_zero, Nat.primeFactors_one]

def psiAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@psi_ge) (type_of% (realize.{0,0,0,0,0} psiSignature (fun _ _ n => psi n) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5.psi_ge.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5.psiRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨psiArena⟩
  objectArena := .source ⟨psiArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source psiArena ⟨psiRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} psiSignature (fun _ _ n => psi n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev sigmaSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev sigmaArena : Arena where
  signature := sigmaSignature
  Law R := ∀ {n : ℕ}, 2 ≤ n → psi n ≤ R.readout () () n

def sigmaActual : Realization sigmaSignature :=
  realize sigmaSignature (fun _ _ n => ArithmeticFunction.sigma 1 n) (fun e => nomatch e)

def sigmaRejected : Realization sigmaSignature :=
  realize sigmaSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem sigmaRejected_law : ¬ sigmaArena.Law sigmaRejected := by
  intro h
  have hbad := h (n := 2) (by norm_num)
  norm_num [sigmaRejected, realize, psi, Nat.primeFactors] at hbad

def sigmaRegistration : Registration sigmaArena (∀ {n : ℕ}, 2 ≤ n → psi n ≤ ArithmeticFunction.sigma 1 n) where
  actual := sigmaActual
  bridge := Iff.rfl
  variation := ⟨sigma_ge_psi, sigmaRejected, sigmaRejected_law⟩
  sensitivity := ⟨fun i => ⟨sigmaRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), sigmaRejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [sigmaActual, realize]

def sigmaAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sigma_ge_psi) (type_of% (realize.{0,0,0,0,0} sigmaSignature (fun _ _ n => ArithmeticFunction.sigma 1 n) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5.sigma_ge_psi.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5.sigmaRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sigmaArena⟩
  objectArena := .source ⟨sigmaArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sigmaArena ⟨sigmaRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sigmaSignature (fun _ _ n => ArithmeticFunction.sigma 1 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev mixedSignature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev mixedArena : Arena where
  signature := mixedSignature
  Law R := ∀ {a b c q : ℝ} {m : ℕ},
    0 < a → a ≤ b → b ≤ c → 1 ≤ m → 1 ≤ q → q ≤ b / a →
    let A := a ^ m * (b + c)
    let B := R.readout () m b * (a + c)
    let C := c ^ m * (a + b)
    A ≤ B ∧ B ≤ C ∧ q ^ (m - 1) * (1 + q) / 2 ≤ B / A

def mixedActual : Realization mixedSignature :=
  realize mixedSignature (fun _ m b => b ^ m) (fun e => nomatch e)

def mixedRejected : Realization mixedSignature :=
  realize mixedSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem mixedRejected_law : ¬ mixedArena.Law mixedRejected := by
  intro h
  have hbad := h (a := 1) (b := 1) (c := 1) (q := 1) (m := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [mixedRejected, realize] at hbad

def mixedRegistration : Registration mixedArena
    (∀ {a b c q : ℝ} {m : ℕ},
      0 < a → a ≤ b → b ≤ c → 1 ≤ m → 1 ≤ q → q ≤ b / a →
      let A := a ^ m * (b + c)
      let B := b ^ m * (a + c)
      let C := c ^ m * (a + b)
      A ≤ B ∧ B ≤ C ∧ q ^ (m - 1) * (1 + q) / 2 ≤ B / A) where
  actual := mixedActual
  bridge := Iff.rfl
  variation := ⟨mixed_bound, mixedRejected, mixedRejected_law⟩
  sensitivity := ⟨fun i => ⟨mixedRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), mixedRejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    norm_num [mixedActual, realize]

def mixedAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixed_bound)
    (type_of% (realize.{0,0,0,0,0} mixedSignature (fun _ m b => b ^ m)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5.mixed_bound.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5.mixedRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨mixedArena⟩
  objectArena := .source ⟨mixedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source mixedArena ⟨mixedRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} mixedSignature (fun _ m b => b ^ m)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5
    definition := none
    coordinates := #[4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5
