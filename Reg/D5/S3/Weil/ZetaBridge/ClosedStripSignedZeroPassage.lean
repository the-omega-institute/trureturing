import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage
import D5.S3.Weil.ZetaSeam.StatementSeamClosed
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import Reg.Support.SingleDependentReadout

/-! Retain the full strip telescope and all signed products. Intervene only
on the first sampled function V_n in the approximant summability clause.
The rejected quadratic readout turns a lawful inverse-square input into
the nonsummable actual multiplicity series. -/

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
    (ℕ → ℂ → ℂ) (fun _ => ℕ) (fun _ => ℂ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ V n => V n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ z => (((1 + z.re ^ (2 : ℕ)) : ℝ) : ℂ))
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (hs : ZetaSeam) {U : ℂ → ℂ} {V : ℕ → ℂ → ℂ} {D : ℝ},
    0 ≤ D →
    (∀ n z, |z.im| ≤ 1 / 2 → ‖V n z‖ ≤ D / (1 + z.re ^ (2 : ℕ))) →
    (∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Tendsto (fun n => V n z) atTop (𝓝 (U z))) →
    (∀ n, Summable (fun ρ : (zetaZeros hs).carrier =>
      (zeroMult ρ : ℂ) * (R.readout () V n) (gammaOf ρ) *
        conj (V n (conj (gammaOf ρ))))) ∧
    Summable (fun ρ : (zetaZeros hs).carrier =>
      (zeroMult ρ : ℂ) * U (gammaOf ρ) * conj (U (conj (gammaOf ρ)))) ∧
    Tendsto (fun n => ∑' ρ : (zetaZeros hs).carrier,
      (zeroMult ρ : ℂ) * V n (gammaOf ρ) * conj (V n (conj (gammaOf ρ))))
      atTop (𝓝 (∑' ρ : (zetaZeros hs).carrier,
        (zeroMult ρ : ℂ) * U (gammaOf ρ) * conj (U (conj (gammaOf ρ)))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Infinite ((zetaZeros zetaSeam).carrier) := Set.infinite_coe_iff.mpr (by
    simpa only [zetaZeros_carrier, _root_.D5.S3.Weil.ZeroSum.IsNontrivialZero,
      _root_.D5.S3.Weil.Convention.classicalZeta, Zeta23.IsNontrivialZero] using
      zetaZeroData_closed_chain.1)
  let W : ℂ → ℂ := fun z => ((1 / (1 + z.re ^ (2 : ℕ)) : ℝ) : ℂ)
  have hall := h zetaSeam (U := W) (V := fun _ => W) (D := 1)
    (by norm_num) (by
      intro n z hz
      change ‖((1 / (1 + z.re ^ (2 : ℕ)) : ℝ) : ℂ)‖ ≤
        1 / (1 + z.re ^ (2 : ℕ))
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)])
    (fun _ _ => tendsto_const_nhds)
  have hterm (ρ : (zetaZeros zetaSeam).carrier) :
      (zeroMult ρ : ℂ) * (((1 + (gammaOf ρ).re ^ (2 : ℕ)) : ℝ) : ℂ) *
        conj (W (conj (gammaOf ρ))) = (zeroMult ρ : ℂ) := by
    dsimp only [W]
    rw [Complex.conj_re, Complex.conj_ofReal, mul_assoc, ← Complex.ofReal_mul]
    have hq : 1 + (gammaOf ρ).re ^ (2 : ℕ) ≠ 0 := by positivity
    simp [hq]
  have hmult : Summable (fun ρ : (zetaZeros zetaSeam).carrier =>
      (zeroMult ρ : ℂ)) := (hall.1 0).congr hterm
  have hi : Summable (fun _ : (zetaZeros zetaSeam).carrier => (1 : ℂ)) :=
    hmult.norm.of_norm_bounded (fun ρ => by
      rw [norm_one, Complex.norm_natCast]
      exact_mod_cast zetaSeam.one_le_mult (ρ : ℂ) ρ.property)
  have hz : (1 : ℂ) = 0 := (summable_const_iff (1 : ℂ)).mp hi
  norm_num at hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(fun n _ => (n : ℂ)), 0, 1, ?_⟩
  intro h
  have hzero := congrFun h (0 : ℂ)
  norm_num [actual, realize] at hzero

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
  readout := some (realize signature (fun _ V n => V n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaBridge.ClosedStripSignedZeroPassage
