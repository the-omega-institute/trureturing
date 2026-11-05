/- Full natural family; no current binding evidence.
Source-occurrence selection/reconstruction and escapeFrom remain unfinished:
https://github.com/the-omega-institute/trureturing/issues/25856 .
No registration here is claimed declared_validated. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthCoefficient
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthCoefficient

open Filter
open _root_.D5.S0.Tower.DBonacci.PerronRoot
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthCoefficient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev fourthSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The readout is the actual analytic coefficient, with its complete defining telescope. -/
noncomputable def fourthValue (q : ℕ) : ℝ :=
  let Q : ℕ → ℝ := fun q => (q : ℝ)
  let nu : ℕ → ℝ := fun q => (Q q)^2
  let beta : ℕ → ℝ := fun q => dbonacciPerronRoot (q^2)
  let sigma : ℕ → ℝ := fun q => Real.log (beta q)
  let w : ℕ → ℝ := fun q => Real.exp (-nu q * sigma q)
  let alpha : ℕ → ℝ := fun q => (nu q - 1) / (4 * Q q * sigma q)
  let g : ℕ → ℝ := fun q => beta q - nu q * w q
  let C : ℕ → ℝ := fun q => 2 * (nu q + 1) / (3 * (nu q - 1)^2)
  let E : ℕ → ℝ := fun q => 4 / (3 * (nu q - 1)^2)
  let B : ℕ → ℝ := fun q =>
    16 * ((nu q)^2 + nu q + 1) / (15 * (nu q - 1)^4)
  let H : ℕ → ℝ → ℝ := fun q s =>
    C q * s^3 * (Real.exp s - (nu q)^2 * Real.exp (-nu q * s))
  let K : ℕ → ℝ → ℝ := fun q s =>
    -E q * s^3 * (Real.exp s - nu q * Real.exp (-nu q * s)) +
      B q * s^5 * (Real.exp s - (nu q)^3 * Real.exp (-nu q * s)) +
      ((C q)^2 / 2) * s^6 * (Real.exp s + (nu q)^4 * Real.exp (-nu q * s))
  let d : ℕ → ℝ := fun q =>
    (nu q + 1) * sigma q / (6 * Q q * (nu q - 1)) *
      ((((nu q)^2 + 1) * beta q - 2 * (nu q)^2) /
        ((nu q + 1) * beta q - 2 * nu q))
  let u : ℕ → ℝ := fun q => -sigma q * d q / alpha q
  let G2 : ℕ → ℝ := fun q => beta q + (nu q)^2 * w q
  let Hp : ℕ → ℝ := fun q =>
    C q * (3 * (sigma q)^2 * (beta q - (nu q)^2 * w q) +
      (sigma q)^3 * (beta q + (nu q)^3 * w q))
  let e : ℕ → ℝ := fun q =>
    (d q)^2 / alpha q + alpha q / (sigma q * g q) *
      (G2 q * (u q)^2 / 2 + Hp q * u q + K q (sigma q))
  let r : ℕ → ℝ := fun q => nu q * (nu q - 1) * w q / g q
  let A : ℕ → ℝ := fun q =>
    (2 * ((nu q)^2 - 4 * nu q + 1) -
      4 * (nu q + 1) * (3 * (nu q)^2 - 2 * nu q - 2) * r q -
      10 * (nu q + 1)^2 * (r q)^2) / (45 * (nu q - 1)^3)
  let J : ℕ → ℝ := fun q =>
    beta q * (nu q)^2 * w q * (nu q + 1)^2 / (9 * (nu q - 1) * (g q)^3)
  e q

noncomputable def fourthActual : Realization fourthSignature :=
  realize fourthSignature (fun _ _ q => fourthValue q) (fun a => nomatch a)

noncomputable def fourthRejected : Realization fourthSignature :=
  realize fourthSignature (fun _ _ _ => 0) (fun a => nomatch a)

/-- Only the whole coefficient role is replaced; every other formula and all four clauses remain. -/
def fourthLaw (R : Realization fourthSignature) : Prop :=
  let Q : ℕ → ℝ := fun q => (q : ℝ)
  let nu : ℕ → ℝ := fun q => (Q q)^2
  let beta : ℕ → ℝ := fun q => dbonacciPerronRoot (q^2)
  let sigma : ℕ → ℝ := fun q => Real.log (beta q)
  let w : ℕ → ℝ := fun q => Real.exp (-nu q * sigma q)
  let alpha : ℕ → ℝ := fun q => (nu q - 1) / (4 * Q q * sigma q)
  let g : ℕ → ℝ := fun q => beta q - nu q * w q
  let C : ℕ → ℝ := fun q => 2 * (nu q + 1) / (3 * (nu q - 1)^2)
  let E : ℕ → ℝ := fun q => 4 / (3 * (nu q - 1)^2)
  let B : ℕ → ℝ := fun q =>
    16 * ((nu q)^2 + nu q + 1) / (15 * (nu q - 1)^4)
  let H : ℕ → ℝ → ℝ := fun q s =>
    C q * s^3 * (Real.exp s - (nu q)^2 * Real.exp (-nu q * s))
  let K : ℕ → ℝ → ℝ := fun q s =>
    -E q * s^3 * (Real.exp s - nu q * Real.exp (-nu q * s)) +
      B q * s^5 * (Real.exp s - (nu q)^3 * Real.exp (-nu q * s)) +
      ((C q)^2 / 2) * s^6 * (Real.exp s + (nu q)^4 * Real.exp (-nu q * s))
  let d : ℕ → ℝ := fun q =>
    (nu q + 1) * sigma q / (6 * Q q * (nu q - 1)) *
      ((((nu q)^2 + 1) * beta q - 2 * (nu q)^2) /
        ((nu q + 1) * beta q - 2 * nu q))
  let u : ℕ → ℝ := fun q => -sigma q * d q / alpha q
  let G2 : ℕ → ℝ := fun q => beta q + (nu q)^2 * w q
  let Hp : ℕ → ℝ := fun q =>
    C q * (3 * (sigma q)^2 * (beta q - (nu q)^2 * w q) +
      (sigma q)^3 * (beta q + (nu q)^3 * w q))
  let e : ℕ → ℝ := fun q => R.readout () () q
  let r : ℕ → ℝ := fun q => nu q * (nu q - 1) * w q / g q
  let A : ℕ → ℝ := fun q =>
    (2 * ((nu q)^2 - 4 * nu q + 1) -
      4 * (nu q + 1) * (3 * (nu q)^2 - 2 * nu q - 2) * r q -
      10 * (nu q + 1)^2 * (r q)^2) / (45 * (nu q - 1)^3)
  let J : ℕ → ℝ := fun q =>
    beta q * (nu q)^2 * w q * (nu q + 1)^2 / (9 * (nu q - 1) * (g q)^3)
  (∀ q : ℕ, 3 ≤ q → e q < 0) ∧
  (∀ q : ℕ, 3 ≤ q → u q = -H q (sigma q) / g q ∧
    G2 q * (u q)^2 / 2 + Hp q * u q + K q (sigma q) +
      g q * (sigma q * (d q)^2 / (alpha q)^2 - sigma q * e q / alpha q) = 0) ∧
  (∀ q : ℕ, 3 ≤ q → Q q * e q = -sigma q / (3 * (nu q - 1)) +
    A q * (sigma q)^3 + J q * (sigma q)^4) ∧
  Tendsto (fun q : ℕ => (q : ℝ)^3 * e q) atTop
    (nhds (-Real.log 2 / 3 + 2 * (Real.log 2)^3 / 45))

abbrev fourthArena : Arena where
  signature := fourthSignature
  Law := fourthLaw

private theorem actual_bridge :
    (type_of% square_displacement_fourth_coefficient) ↔ fourthArena.Law fourthActual := by
  rfl

private theorem actual_law : fourthArena.Law fourthActual :=
  actual_bridge.mp square_displacement_fourth_coefficient

/-- Zeroing the actual coefficient already contradicts its native strict sign clause. -/
private theorem rejected_not_law : ¬ fourthArena.Law fourthRejected := by
  intro h
  have hz := h.1 3 (by norm_num)
  change (0 : ℝ) < 0 at hz
  exact (lt_irrefl (0 : ℝ)) hz

/-- Dependence uses the full scaled law; it is not a manually supplied two-point assertion. -/
private theorem value_tendsto_zero : Tendsto fourthValue atTop (nhds 0) := by
  have hs := actual_law.2.2.2
  change Tendsto (fun q : ℕ => (q : ℝ)^3 * fourthValue q) atTop
    (nhds (-Real.log 2 / 3 + 2 * (Real.log 2)^3 / 45)) at hs
  have hi : Tendsto (fun q : ℕ => ((q : ℝ)^3)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α := ℝ)
      (by decide : 3 ≠ 0)).comp tendsto_natCast_atTop_atTop)
  have hp : Tendsto (fun q : ℕ => ((q : ℝ)^3 * fourthValue q) * ((q : ℝ)^3)⁻¹)
      atTop (nhds 0) := by simpa using hs.mul hi
  apply hp.congr'
  filter_upwards [eventually_ge_atTop 3] with q hq
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  field_simp [hq0]

private theorem actual_dependence : ObservationalDependence fourthSignature fourthActual := by
  intro i
  cases i
  by_contra hn
  have hconstant (q : ℕ) : fourthValue q = fourthValue 3 := by
    by_contra hq
    apply hn
    refine ⟨(), 3, q, ?_⟩
    change fourthValue 3 ≠ fourthValue q
    exact Ne.symm hq
  have hc : Tendsto fourthValue atTop (nhds (fourthValue 3)) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => fourthValue 3)
      atTop (nhds (fourthValue 3))) using 1
    funext q
    exact hconstant q
  have hz : fourthValue 3 = 0 := tendsto_nhds_unique hc value_tendsto_zero
  have hs := actual_law.1 3 (by norm_num)
  change fourthValue 3 < 0 at hs
  rw [hz] at hs
  exact (lt_irrefl (0 : ℝ)) hs

noncomputable def fourthSource : Registration fourthArena
    (type_of% square_displacement_fourth_coefficient) where
  actual := fourthActual
  bridge := actual_bridge
  variation := ⟨actual_law, fourthRejected, rejected_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨fourthRejected, ?_, rfl, rejected_not_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro a
      exact nomatch a
  dependence := actual_dependence

noncomputable def fourthRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@square_displacement_fourth_coefficient)
      (Realization fourthSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthCoefficient.square_displacement_fourth_coefficient.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthCoefficient.fourthSource
  realizationSource := none
  generated := false
  arena := .source ⟨fourthArena⟩
  objectArena := .source ⟨fourthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fourthArena ⟨fourthSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some fourthActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthCoefficient
