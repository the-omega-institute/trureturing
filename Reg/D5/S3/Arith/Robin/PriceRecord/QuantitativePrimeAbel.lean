import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open Real Filter
open scoped Topology
open LeanInformationAudit
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => primeCount x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ, Tendsto (fun x : ℝ =>
    (R.readout () () x - ∑ j ∈ Finset.range r, (j.factorial : ℝ) * (x / log x ^ (j + 1))) /
      (x / log x ^ (r + 1))) atTop (𝓝 (r.factorial : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 1) := by
    simpa [rejected, realize] using h 0
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hzero)

def family : Registration arena (type_of% prime_counting_factorial_residual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_counting_factorial_residual, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : ℝ), (2 : ℝ), ?_⟩
    have h0 : primeCount 0 = 0 := by simp [primeCount]
    have h2 : primeCount 2 = 1 := by
      rw [primeCount, Nat.floor_ofNat]
      have h : Nat.primeCounting 2 = 1 := by decide
      simp [h]
    change primeCount 0 ≠ primeCount 2
    rw [h0, h2]
    exact zero_ne_one

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    prime_counting_factorial_residual (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.prime_counting_factorial_residual.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => primeCount x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
