import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage
import D5.S3.Weil.ZetaSeam.StatementSeamClosed
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import Reg.Support.SingleDependentReadout

/-! Retain the original actual zeta seam, complete strip envelope and
pointwise convergence telescope. The complete signed complex sample in
the first summability clause is observed by the identity readout; all
other clauses retain their original signed products. The rejected
constant-one readout fails actual summability,
using the already established infinitude of the actual zeta-zero carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage
open _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open LeanInformationAudit Zeta23 Filter
open scoped Topology ComplexConjugate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (hs : ZetaSeam) {U : ℂ → ℂ} {V : ℕ → ℂ → ℂ} {D : ℝ},
    0 ≤ D →
    (∀ n z, |z.im| ≤ 1 / 2 → ‖V n z‖ ≤ D / (1 + z.re ^ (2 : ℕ))) →
    (∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Tendsto (fun n => V n z) atTop (𝓝 (U z))) →
    (∀ n, Summable (fun ρ : (zetaZeros hs).carrier =>
      R.readout () () ((zeroMult ρ : ℂ) * V n (gammaOf ρ) *
        conj (V n (conj (gammaOf ρ)))))) ∧
    Summable (fun ρ : (zetaZeros hs).carrier =>
      (zeroMult ρ : ℂ) * U (gammaOf ρ) * conj (U (conj (gammaOf ρ)))) ∧
    Tendsto (fun n => ∑' ρ : (zetaZeros hs).carrier,
      (zeroMult ρ : ℂ) * V n (gammaOf ρ) * conj (V n (conj (gammaOf ρ))))
      atTop (𝓝 (∑' ρ : (zetaZeros hs).carrier,
        (zeroMult ρ : ℂ) * U (gammaOf ρ) * conj (U (conj (gammaOf ρ)))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Infinite ((zetaZeros zetaSeam).carrier) := Set.infinite_coe_iff.mpr (by
    simpa only [zetaZeros_carrier] using zetaZeroData_closed_chain.1)
  have hall := h zetaSeam (U := fun _ => 0) (V := fun _ _ => 0) (D := 0)
    (by norm_num) (by intro n z hz; simp) (fun _ _ => tendsto_const_nhds)
  have hi : Summable (fun _ : (zetaZeros zetaSeam).carrier => (1 : ℂ)) := hall.1 0
  have hz : (1 : ℂ) = 0 := (summable_const_iff (1 : ℂ)).mp hi
  norm_num at hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ) ≠ 1
  norm_num

def evidence : Registration arena (type_of% actual_zeta_signed_zero_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_zeta_signed_zero_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    actual_zeta_signed_zero_tendsto (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage
