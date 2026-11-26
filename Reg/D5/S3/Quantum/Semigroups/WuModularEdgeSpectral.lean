import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuModularEdgeSpectral

/-! Source-bound registration for the spectral edge sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.SpectralPower (mpow)
open _root_.D5.S3.Quantum.Semigroups.WuModularEdgeSpectral

namespace Reg.D5.S3.Quantum.Semigroups.WuModularEdgeSpectral

namespace Expansion

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

private abbrev arena.{u, v} : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {ι : Type v} [Fintype ι]
      {D ρ : Matrix n n ℂ} (hD : D.PosDef) (hρ : ρ.PosSemidef)
      (a b : ι → ℝ) (J : ι → Matrix n n ℂ) {s : ℝ} (hs : 1 < s)
      (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
      (hJ : ∀ k, D * J k * D⁻¹ = (a k / b k) • J k),
    let G := mpow D (1 / (2 * s))
    let H := mpow D (-(1 / (2 * s)))
    let M := mpow ρ (1 / s)
    let X := H * M * H
    R.readout () ()
      ((1 / 4 : ℝ) * (mpow M (s - 1) *
        (G * (∑ k, pairedGenerator (a k) (b k) (J k) X) * G)).trace.re)
      (∑ k, ∑ i, ∑ j, edgeWeight hρ.isHermitian (J k) i j *
        coshEdgeKernel (1 / s) (b k * hρ.isHermitian.eigenvalues i)
          (a k * hρ.isHermitian.eigenvalues j))

universe u v

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let ι := ULift.{v} (Fin 1)
  let D : Matrix n n ℂ := 1
  let ρ : Matrix n n ℂ := 0
  let a : ι → ℝ := fun _ => 1
  let J : ι → Matrix n n ℂ := fun _ => 0
  have hD : D.PosDef := Matrix.PosDef.one
  have hρ : ρ.PosSemidef := Matrix.PosSemidef.zero
  have hs : (1 : ℝ) < 2 := by norm_num
  have ha : ∀ k, 0 < a k := fun _ => zero_lt_one
  have hJ : ∀ k, D * J k * D⁻¹ = (a k / a k) • J k := by simp [J]
  exact h hD hρ a a J hs ha ha hJ (generatorTrace_eq_cosh hD hρ a a J hs ha ha hJ)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (one_ne_zero : (1 : ℝ) ≠ 0) (Eq.mp (congrFun h 0) rfl)

def family : Registration arena.{u, v} (type_of% @generatorTrace_eq_cosh.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@generatorTrace_eq_cosh.{u, v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u, v}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@generatorTrace_eq_cosh.{u, v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuModularEdgeSpectral.generatorTrace_eq_cosh.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuModularEdgeSpectral.Expansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuModularEdgeSpectral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Expansion

end Reg.D5.S3.Quantum.Semigroups.WuModularEdgeSpectral
