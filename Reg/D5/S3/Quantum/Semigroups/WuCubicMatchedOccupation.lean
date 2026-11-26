import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation

/-! Source-bound registrations for the Hellinger comparison and cubic generator excess. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.SpectralPower (mpow)
open _root_.D5.S3.Quantum.Semigroups.WuModularEdgeSpectral (edgeWeight pairedGenerator)
open _root_.D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation

universe u v

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => ¬ x ≤ y) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (not_le_of_gt zero_lt_one) (Eq.mp (congrFun h 0) (le_rfl : (0 : ℝ) ≤ 0))

namespace Probability

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι]
      (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i)
      (hPsum : (∑ i, P i) = 1) (hQsum : (∑ i, Q i) = 1)
      {u v : ℝ} (hu : 0 < u) (hv : 0 < v),
    R.readout () ()
      (hellingerCoefficient u v * (1 - ∑ i, Real.sqrt (P i * Q i)))
      (u * (1 - ∑ i, P i ^ (1 / 3 : ℝ) * Q i ^ (2 / 3 : ℝ)) +
        v * (1 - ∑ i, P i ^ (2 / 3 : ℝ) * Q i ^ (1 / 3 : ℝ)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  let P : ULift.{u} (Fin 1) → ℝ := fun _ => 1
  have hP : ∀ i, 0 ≤ P i := fun _ => zero_le_one
  have hsum : (∑ i, P i) = 1 := by simp [P]
  exact law P P hP hP hsum hsum zero_lt_one zero_lt_one
    (finite_probability_comparison P P hP hP hsum hsum zero_lt_one zero_lt_one)

def family : Registration arena.{u} (type_of% @finite_probability_comparison.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_probability_comparison.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_probability_comparison.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation.finite_probability_comparison.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation.Probability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Probability

namespace Generator

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} {ι : Type v} [Fintype n] [DecidableEq n] [Fintype ι]
      {D ρ : Matrix n n ℂ} (hD : D.PosDef) (hρ : ρ.PosSemidef)
      (a b : ι → ℝ) (J : ι → Matrix n n ℂ)
      (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
      (hJ : ∀ k, D * J k * D⁻¹ = (a k / b k) • J k)
      (hA : ∀ k, 0 < (ρ * (J k * (J k)ᴴ)).trace.re)
      (hB : ∀ k, 0 < (ρ * ((J k)ᴴ * J k)).trace.re),
    let lam := hρ.isHermitian.eigenvalues
    let w (k : ι) := edgeWeight hρ.isHermitian (J k)
    let A (k : ι) := (ρ * (J k * (J k)ᴴ)).trace.re
    let B (k : ι) := (ρ * ((J k)ᴴ * J k)).trace.re
    let P (k : ι) (i j : n) := w k i j * lam i / A k
    let Q (k : ι) (i j : n) := w k i j * lam j / B k
    let u (k : ι) := (b k * A k) ^ (1 / 3 : ℝ) * (a k * B k) ^ (2 / 3 : ℝ)
    let v (k : ι) := (b k * A k) ^ (2 / 3 : ℝ) * (a k * B k) ^ (1 / 3 : ℝ)
    let G := mpow D (1 / (2 * 3))
    let H := mpow D (-(1 / (2 * 3)))
    let M := mpow ρ (1 / 3)
    let X := H * M * H
    R.readout () ()
      (∑ k, (9 / 4 : ℝ) * hellingerCoefficient (u k) (v k) *
        (1 - ∑ i, ∑ j, Real.sqrt (P k i j * Q k i j)))
      ((9 / 8 : ℝ) * (mpow M 2 *
        (G * (∑ k, pairedGenerator (a k) (b k) (J k) X) * G)).trace.re -
        (9 / 4 : ℝ) * (∑ k, cubicKernel (b k * A k) (a k * B k)))

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro law
  let n := ULift.{u} (Fin 1)
  let ι := ULift.{v} (Fin 1)
  let I : Matrix n n ℂ := 1
  let a : ι → ℝ := fun _ => 1
  let J : ι → Matrix n n ℂ := fun _ => I
  have hD : I.PosDef := Matrix.PosDef.one
  have hρ : I.PosSemidef := hD.posSemidef
  have ha : ∀ k, 0 < a k := fun _ => zero_lt_one
  have hJ : ∀ k, I * J k * I⁻¹ = (a k / a k) • J k := by
    intro k
    simp [I, a, J]
  have hA : ∀ k, 0 < (I * (J k * (J k)ᴴ)).trace.re := by
    intro k
    norm_num [I, J, n, Matrix.trace_one]
  have hB : ∀ k, 0 < (I * ((J k)ᴴ * J k)).trace.re := by
    intro k
    norm_num [I, J, n, Matrix.trace_one]
  exact law hD hρ a a J ha ha hJ hA hB
    (generator_energy_sub_matched_occupation_ge hD hρ a a J ha ha hJ hA hB)

def family : Registration arena.{u, v} (type_of% @generator_energy_sub_matched_occupation_ge.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@generator_energy_sub_matched_occupation_ge.{u, v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u, v}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@generator_energy_sub_matched_occupation_ge.{u, v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation.generator_energy_sub_matched_occupation_ge.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation.Generator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation
    definition := none
    coordinates := #[]
    readouts := #[{
      -- The generator comparison follows the quantified hypotheses and twelve let bindings.
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Generator

end Reg.D5.S3.Quantum.Semigroups.WuCubicMatchedOccupation
