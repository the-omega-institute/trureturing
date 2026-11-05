import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Tower.DBonacci.PerronRoot
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection
import Reg.Support.DependentFamily

/-! Faithful registration for all natural q>=3, including even q.
Params is Unit and State is the original subtype of q>=3. The two native
readouts are the Perron root at q^2 and its logarithm. The Law retains all
six original coefficient conclusions at every q. Whole-role zero
interventions refute the Law; q=3 and q=4 supply genuine state dependence.
Source-occurrence binding remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/25856 .
sourceSelection and familyRecord remain none; continuation is unknown. -/

set_option autoImplicit false

namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection

open _root_.D5.S0.Tower.DBonacci.PerronRoot
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev coefficientSignature : Signature where
  Params := Unit
  State _ := {q : ℕ // 3 ≤ q}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature
    (fun i _ s => if i = 0 then dbonacciPerronRoot (s.1^2)
      else Real.log (dbonacciPerronRoot (s.1^2)))
    (fun e => nomatch e)

noncomputable def coefficientRejected (i : Fin 2) :
    Realization coefficientSignature :=
  realize coefficientSignature
    (fun j p s => if j = i then 0 else coefficientActual.readout j p s)
    (fun e => nomatch e)

abbrev coefficientArena : Arena where
  signature := coefficientSignature
  Law R := ∀ (q : ℕ) (hq : 3 ≤ q),
    let s : coefficientSignature.State () := ⟨q, hq⟩
    let Q : ℝ := (q : ℝ)
    let nu : ℕ := q^2
    let beta : ℝ := R.readout 0 () s
    let sigma : ℝ := R.readout 1 () s
    let c : ℝ := (Q^2 - 1) / (4 * Q)
    let alpha : ℝ := c / sigma
    let g : ℝ := Real.exp sigma - Q^2 * Real.exp (-Q^2 * sigma)
    let C : ℝ := 2 * (Q^2 + 1) / (3 * (Q^2 - 1)^2)
    let H : ℝ := C * sigma^3 *
      (Real.exp sigma - Q^4 * Real.exp (-Q^2 * sigma))
    let d : ℝ := ((Q^2 + 1) * sigma / (6 * Q * (Q^2 - 1))) *
      (((Q^4 + 1) * beta - 2 * Q^4) /
        ((Q^2 + 1) * beta - 2 * Q^2))
    let b : ℝ := d - 1 / (2 * Q)
    0 < g ∧ 0 < d ∧ d < 5 * Real.log 2 / (24 * Q) ∧
      -1 / (2 * Q) < b ∧ b < 0 ∧ g * (sigma * d / alpha) = H

private theorem coefficient_actual_bridge :
    (type_of% square_displacement_correction) ↔ coefficientArena.Law coefficientActual := by
  simp [coefficientArena, coefficientActual, realize]

private theorem coefficient_actual_law : coefficientArena.Law coefficientActual := by
  intro q hq
  simpa [coefficientActual, realize] using
    (square_displacement_correction q hq)

private theorem coefficient_rejected_law (i : Fin 2) :
    ¬ coefficientArena.Law (coefficientRejected i) := by
  intro h
  have hh := h 3 (by norm_num)
  fin_cases i
  · have hb := hh.2.2.2.2.1
    have hs : (2 / 3 : ℝ) < Real.log (dbonacciPerronRoot 9) := by
      simpa [s_star] using two_thirds_lt_s_star
    simp [coefficientRejected, coefficientActual, realize] at hb
    nlinarith only [hs, hb]
  · have hg := hh.1
    norm_num [coefficientRejected, coefficientActual, realize] at hg

/- The original q=3 and q=4 states distinguish each native readout. -/
private theorem native_parameter_variation :
    coefficientActual.readout 0 () ⟨3, by decide⟩ <
        coefficientActual.readout 0 () ⟨4, by decide⟩ ∧
      coefficientActual.readout 1 () ⟨3, by decide⟩ <
        coefficientActual.readout 1 () ⟨4, by decide⟩ := by
  have hβ : dbonacciPerronRoot 9 < dbonacciPerronRoot 16 := by
    exact dbonacciPerronRoot_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
  have hσ : Real.log (dbonacciPerronRoot 9) <
      Real.log (dbonacciPerronRoot 16) :=
    Real.strictMonoOn_log
      (lt_trans zero_lt_one (one_lt_dbonacciPerronRoot 9 (by norm_num)))
      (lt_trans zero_lt_one (one_lt_dbonacciPerronRoot 16 (by norm_num))) hβ
  simpa [coefficientActual, realize] using And.intro hβ hσ

private theorem coefficient_actual_dependence :
    ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  refine ⟨(), ⟨3, by decide⟩, ⟨4, by decide⟩, ?_⟩
  have hv := native_parameter_variation
  fin_cases i
  · exact ne_of_lt hv.1
  · exact ne_of_lt hv.2

noncomputable def coefficientSource : Registration coefficientArena
    (type_of% square_displacement_correction) where
  actual := coefficientActual
  bridge := coefficient_actual_bridge
  variation := ⟨coefficient_actual_law,
    coefficientRejected 0, coefficient_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coefficientRejected i, ?_, rfl, coefficient_rejected_law i⟩
      intro j hj
      funext p s
      simp [coefficientRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := coefficient_actual_dependence

noncomputable def coefficientRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@square_displacement_correction)
      (Realization coefficientSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection.square_displacement_correction.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection.coefficientSource
  realizationSource := none
  generated := false
  arena := .source ⟨coefficientArena⟩
  objectArena := .source ⟨coefficientArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coefficientArena ⟨coefficientSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some coefficientActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection
