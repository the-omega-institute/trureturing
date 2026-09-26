import Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice
import Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder
import Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram

open Lean Meta LeanInformationAudit MeasureTheory
open _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)
open scoped BigOperators

namespace LeanInformationAuditRegTests.CosineSourceContract

def pointwiseLattice : Prop := ∀ z : ℝ, 0 < z → ∃ C : ℝ, 0 < C ∧
  Summable (fun n : ℕ => cosineIntegral (z * (n + 1)) ^ 2) ∧
    z * (∑' n : ℕ, cosineIntegral (z * (n + 1)) ^ 2) ≤ C

def missingSummability : Prop := ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
  z * (∑' n : ℕ, cosineIntegral (z * (n + 1)) ^ 2) ≤ C

def pointwiseRemainder : Prop := ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ N : ℕ, 1 ≤ N →
  ∃ C : ℝ, 0 < C ∧
    |(∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) / (k : ℝ)) -
      (-Real.log θ + cosineIntegral ((N : ℝ) * θ))| ≤
      C * (1 / (N : ℝ) + θ * (1 + max 0 (Real.log ((N : ℝ) * θ))))

def missingIntegrability : Prop := ∀ a b : ℝ, 0 < a → 0 < b →
  (∫ z : ℝ, cosineIntegral (a * |z|) * cosineIntegral (b * |z|)) = Real.pi / max a b

-- The rejected family passes every separate scale. This distinguishes the
-- forbidden pointwise weakening from the original uniform law.
example (z : ℝ) : ∃ C : ℝ, 0 < C ∧
    Summable (fun n : ℕ =>
      Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.rejected.readout () z n) ∧
    z * (∑' n : ℕ,
      Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.rejected.readout () z n) ≤ C := by
  refine ⟨z ^ 2 + 1, by positivity,
    Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.rejected_summable z, ?_⟩
  simp only [Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.rejected,
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize,
    tsum_ite_eq]
  nlinarith

run_meta do
  let names := #[
    `D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result,
    `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result,
    `D5.S3.Fourier.Asymptotics.CosineIntegralGram.result]
  for name in names do
    let env ← getEnv
    let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == name)
      | throwError "original source occurrence missing: {name}"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "original source claim missing: {name}"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredValidated certificate := record.result
      | throwError "[FAIL] original source: {(← TemplateBinding.recordJson record).compress}"
    unless certificate.sourceBinding.isSome && record.escape.fromObject.isSome &&
        record.escape.bridgeKind == "source-equivalence" &&
        record.escape.continuation.any (·.kind == "open") do
      throwError "[FAIL] missing four-slot evidence: {name}"
    logInfo m!"[PASS] {name} evidence_ref={certificate.evidenceRef}"
  for (target, mutation) in #[
      (names[0]!, ``pointwiseLattice), (names[0]!, ``missingSummability),
      (names[1]!, ``pointwiseRemainder), (names[2]!, ``missingIntegrability)] do
    let original := (← getConstInfo target).type
    let changed := (← getConstInfo mutation).value!
    let rejected ← try
      discard <| (SourceScope.reconstruct original changed).run 524288
      pure false
    catch _ => pure true
    unless rejected do throwError "[FAIL] accepted {mutation}"
    logInfo m!"[PASS] source_rejects_{mutation}"

end LeanInformationAuditRegTests.CosineSourceContract
