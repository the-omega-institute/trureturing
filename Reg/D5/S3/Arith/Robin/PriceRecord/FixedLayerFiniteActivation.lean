import D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts for the capped Euler term and supported tail allowance. -/

noncomputable section

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation

open Real
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope (eulerTerm)
open _root_.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport (primeSupport)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Capped

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ K => K) (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p K : ℕ} {q : ℝ}, p.Prime → 1 ≤ K →
    IsLeast (localCost p q '' Set.Icc (1 : ℕ) K)
      (eulerTerm p (R.readout () () K) + clippedLayers p q K)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hprime : Nat.Prime 2 := Nat.prime_two
  have hcorrect := capped_minimum_isLeast (p := 2) (q := 0) (K := 1) hprime le_rfl
  have hwrong := h (p := 2) (q := 0) (K := 1) hprime le_rfl
  change IsLeast (localCost 2 0 '' Set.Icc (1 : ℕ) 1)
    (eulerTerm 2 2 + clippedLayers 2 0 1) at hwrong
  have heq := hcorrect.unique hwrong
  have hlog : log (3 / 4 : ℝ) < log (7 / 8 : ℝ) :=
    log_lt_log (by norm_num) (by norm_num)
  norm_num [eulerTerm] at heq
  linarith only [hlog, heq]

def family : Registration arena (type_of% (@capped_minimum_isLeast)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@capped_minimum_isLeast, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℕ) ≠ 2
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@capped_minimum_isLeast) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation.capped_minimum_isLeast.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation.Capped.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K => K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Capped

namespace Supported

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ lam => lam) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => (-1 - eulerTerm 2 3) / log 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {S : Finset ℕ} {lam : ℝ} {m : ℕ},
    primeSupport S → 0 < lam → 2 ≤ m → ∀ (K : ℕ → ℕ), (∀ p ∈ S, m ≤ K p) →
    0 ≤ fixedPriceMinimum S lam - (∑ p ∈ S, clippedLayers p (lam * log (p : ℝ)) m) ∧
      fixedPriceMinimum S lam - (∑ p ∈ S, clippedLayers p (lam * log (p : ℝ)) m) ≤
        ∑ p ∈ S, (((K p - m : ℕ) : ℝ) * (R.readout () () lam * log (p : ℝ)) +
          eulerTerm p (K p))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hS : primeSupport {2} := by simp [primeSupport, Nat.prime_two]
  have hcap : ∀ p ∈ ({2} : Finset ℕ), 2 ≤ (fun _ : ℕ => (3 : ℕ)) p := by
    intro _ _
    exact (by decide : (2 : ℕ) ≤ 3)
  obtain ⟨hlow, hupp⟩ := h (S := {2}) (lam := 1) (m := 2)
    hS (by norm_num) le_rfl (fun _ => 3) hcap
  change _ ≤ ∑ p ∈ ({2} : Finset ℕ),
    (((3 - 2 : ℕ) : ℝ) * (((-1 - eulerTerm 2 3) / log 2) * log (p : ℝ)) +
      eulerTerm p 3) at hupp
  norm_num at hlow hupp
  linarith only [hlow, hupp]

def family : Registration arena (type_of% (@fixed_price_omitted_layers)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_price_omitted_layers, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℝ) ≠ 2
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixed_price_omitted_layers) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation.fixed_price_omitted_layers.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation.Supported.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ lam => lam) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Supported

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation
