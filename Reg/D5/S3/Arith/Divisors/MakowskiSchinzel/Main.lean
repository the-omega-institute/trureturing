import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.MakowskiSchinzel.Main
import Reg.Support.DependentFamily

/-! Source-bound audits of the sigma-totient inequalities with non-Fermat budget forty-two. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.Main

open _root_.D5.S3.Arith.MakowskiSchinzel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => ArithmeticFunction.sigma 1 n.totient) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), eta n ≤ 42 →
    n ≤ 2 * R.readout () () n ∧ (Odd n → n ≤ ArithmeticFunction.sigma 1 n.totient)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 (by simp [eta, nonFermatFactors])).1
  norm_num [rejected, realize] at hbad

def evidence : Registration arena (type_of% @makowski_schinzel_eta_le_42) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨makowski_schinzel_eta_le_42, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@makowski_schinzel_eta_le_42) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.makowski_schinzel_eta_le_42.__information_unit
  realizationName := `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.Main.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => ArithmeticFunction.sigma 1 n.totient) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.Main
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev oddSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def oddActual : Realization oddSignature :=
  realize oddSignature (fun _ _ n => alpha n) (fun e => nomatch e)

def oddRejected : Realization oddSignature :=
  realize oddSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev oddArena : Arena where
  signature := oddSignature
  Law R := ∀ (n : ℕ), Odd n → eta n ≤ 42 → 1 ≤ R.readout () () n

private theorem odd_rejected_law : ¬ oddArena.Law oddRejected := by
  intro h
  have hbad := h 1 (by decide) (by simp [eta, nonFermatFactors])
  norm_num [oddRejected, realize] at hbad

def oddEvidence : Registration oddArena (type_of% @odd_alpha_eta_le_42) where
  actual := oddActual
  bridge := Iff.rfl
  variation := ⟨odd_alpha_eta_le_42, oddRejected, odd_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨oddRejected, ?_, rfl, odd_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [oddActual, realize, alpha]

def oddAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@odd_alpha_eta_le_42) (Realization oddSignature) Type Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.odd_alpha_eta_le_42.__information_unit
  realizationName := `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.Main.oddEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨oddArena⟩
  objectArena := .source ⟨oddArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source oddArena ⟨oddEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize oddSignature (fun _ _ n => alpha n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.Main
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def etaActual : Realization signature :=
  realize signature (fun _ _ n => eta n) (fun e => nomatch e)

def etaRejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev etaArena : Arena where
  signature := signature
  Law R := ∀ {a b : ℕ}, b ≠ 0 → a ∣ b → R.readout () () a ≤ eta b

private theorem eta_rejected_law : ¬ etaArena.Law etaRejected := by
  intro h
  have hbad := h (a := 1) (b := 1) (by decide) (dvd_refl 1)
  norm_num [etaRejected, realize, eta, nonFermatFactors] at hbad

def etaEvidence : Registration etaArena (type_of% @eta_le_of_dvd) where
  actual := etaActual
  bridge := Iff.rfl
  variation := ⟨@eta_le_of_dvd, etaRejected, eta_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨etaRejected, ?_, rfl, eta_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 7, ?_⟩
    have hnotpow : ¬ ∃ k : ℕ, 7 - 1 = 2 ^ k := by
      rintro ⟨k, hk⟩
      have hklt : k < 3 := by
        by_contra h
        have hle := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ k by omega)
        norm_num at hle hk
        omega
      interval_cases k <;> norm_num at hk
    have hp7 : Nat.Prime 7 := by norm_num
    simp [etaActual, realize, eta, nonFermatFactors, hp7.primeFactors,
      Finset.filter_singleton, hnotpow]

def etaAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eta_le_of_dvd) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.eta_le_of_dvd.__information_unit
  realizationName := `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.Main.etaEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨etaArena⟩
  objectArena := .source ⟨etaArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source etaArena ⟨etaEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => eta n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.Main
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms etaEvidence
#print axioms etaAudit
#print axioms evidence
#print axioms audit
#print axioms oddEvidence
#print axioms oddAudit

end
end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.Main
