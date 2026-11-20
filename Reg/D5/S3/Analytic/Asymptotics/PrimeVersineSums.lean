import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Analytic.Asymptotics.PrimeVersineSums

/-! Source-bound audit of the phases of the prime versine sums. The readout is the partial sum
over the primes `p ≤ x` of a summand, read in the third conjunct at the summand
`p ↦ p ^ (-2σ) / 2` that is subtracted from the versine sum. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Asymptotics.PrimeVersineSums
open Real Filter Finset Topology

set_option linter.style.longLine false
noncomputable section
namespace Reg.D5.S3.Analytic.Asymptotics.PrimeVersineSums

namespace PartialSum

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x f => Finset.sum (Finset.filter (fun p => Nat.Prime p)
    (Finset.Ioc 0 ⌊x⌋₊)) f) (fun e => nomatch e)

/-- The reading that returns `0` for every summand. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete statement of `prime_versine_phases`; only the partial sum of
`p ^ (-2σ) / 2` over the primes `p ≤ x` in the third conjunct is read out. -/
abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ σ : ℝ, 0 ≤ σ →
      (Summable (fun p : Nat.Primes => 1 - Real.cos ((p : ℝ) ^ (-σ))) ↔ 1 / 2 < σ)) ∧
    (∀ σ : ℝ, 0 ≤ σ →
      (Summable (fun p : Nat.Primes => 1 - Real.cos ((p : ℝ) ^ (-σ)) - (p : ℝ) ^ (-(2 * σ)) / 2) ↔
        1 / 4 < σ)) ∧
    (∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 / 4 →
      Tendsto (fun x : ℝ => primeVersineSum σ x -
        r.readout () x (fun p : ℕ => (p : ℝ) ^ (-(2 * σ)) / 2)) atTop atBot) ∧
    ∀ x : ℝ,
      (∑' p : Nat.Primes, (1 / (2 * (p : ℝ)) - (1 - Real.cos ((p : ℝ) ^ (-(1 / 2 : ℝ)))))) -
          5 / (48 * ((⌊x⌋₊ : ℝ) + 1)) ≤
        (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, 1 / (2 * (p : ℝ))) - primeVersineSum (1 / 2) x ∧
      (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, 1 / (2 * (p : ℝ))) - primeVersineSum (1 / 2) x ≤
        ∑' p : Nat.Primes, (1 / (2 * (p : ℝ)) - (1 - Real.cos ((p : ℝ) ^ (-(1 / 2 : ℝ)))))

/-- The versine sum is nonnegative. -/
theorem primeVersineSum_nonneg (σ x : ℝ) : 0 ≤ primeVersineSum σ x :=
  Finset.sum_nonneg fun p _ => by linarith [Real.cos_le_one ((p : ℝ) ^ (-σ))]

/-- At `σ = 0`, a nonnegative function cannot tend to `-∞`. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h3 := h.2.2.1 0 le_rfl (by norm_num)
  simp only [rejected, realize, sub_zero] at h3
  obtain ⟨x, hx⟩ := ((Filter.tendsto_atBot.mp h3 (-1)).and
    (Filter.Eventually.of_forall fun x => primeVersineSum_nonneg 0 x)).exists
  linarith [hx.1, hx.2]

/-- At `x = 2` the only prime is `2`, so the summands `0` and `1` give `0` and `1`. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, fun _ => 0, fun _ => 1, ?_⟩
  change Finset.sum (Finset.filter (fun p => Nat.Prime p) (Finset.Ioc 0 ⌊(2 : ℝ)⌋₊))
      (fun _ => (0 : ℝ)) ≠
    Finset.sum (Finset.filter (fun p => Nat.Prime p) (Finset.Ioc 0 ⌊(2 : ℝ)⌋₊)) (fun _ => 1)
  have hf : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hf, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : (Finset.filter (fun p => Nat.Prime p) (Finset.Ioc 0 2)).card = 1 := by decide
  rw [hc]
  norm_num

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @prime_versine_phases

def source : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_versine_phases, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_versine_phases) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Asymptotics.PrimeVersineSums.PartialSum.unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.PrimeVersineSums.PartialSum.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x f => Finset.sum (Finset.filter
    (fun p => Nat.Prime p) (Finset.Ioc 0 ⌊x⌋₊)) f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.PrimeVersineSums
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "body", "body", "fn", "fn", "arg", "body",
        "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end PartialSum

end Reg.D5.S3.Analytic.Asymptotics.PrimeVersineSums
