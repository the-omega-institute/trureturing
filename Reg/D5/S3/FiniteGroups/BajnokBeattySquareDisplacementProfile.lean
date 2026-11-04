import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Tower.DBonacci.PerronRoot
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile
import Reg.Support.DependentFamily

/-! Faithful Reg source attempt. Source-occurrence binding remains unfinished.
The full original five-part statement is the Law. Params is Unit, State is Nat
(including q<3 and the complete limit domain), and the two whole-role readouts
are beta_q and sigma_q. Native states q=3,4 vary at the SAME parameter ().

Both whole-role zero interventions are addressed below. Sigma=0 contradicts
the ray-root clause at the actual order-nine logarithm. Beta=0 leaves the
actual sigma family and makes (q*d_q)/q^2 tend to log(2)/6>0; a finite limit
for q*d_q would instead force that normalized sequence to tend to zero.

Source-occurrence selection/reconstruction and escapeFrom remain unfinished:
https://github.com/the-omega-institute/trureturing/issues/25856 .
sourceSelection and familyRecord are none; continuation is unknown.
This is not declared_validated and supplies no current binding evidence. -/

set_option autoImplicit false

namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile

open Filter
open _root_.D5.S0.Tower.DBonacci.PerronRoot
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev profileSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def profileActual : Realization profileSignature :=
  realize profileSignature
    (fun i _ q => if i = 0 then dbonacciPerronRoot (q^2)
      else Real.log (dbonacciPerronRoot (q^2)))
    (fun e => nomatch e)

noncomputable def profileRejected (i : Fin 2) : Realization profileSignature :=
  realize profileSignature
    (fun j p q => if j = i then 0 else profileActual.readout j p q)
    (fun e => nomatch e)

/-- The telescope matches the source, with only beta and sigma replaced by readouts. -/
def profileLaw (R : Realization profileSignature) : Prop :=
  let beta : ℕ → ℝ := fun q => R.readout 0 () q
  let sigma : ℕ → ℝ := fun q => R.readout 1 () q
  let G : ℕ → ℝ → ℝ := fun q s => Real.exp s + Real.exp (-(q : ℝ)^2 * s)
  let d : ℕ → ℝ := fun q =>
    (((q : ℝ)^2 + 1) * sigma q / (6 * (q : ℝ) * ((q : ℝ)^2 - 1))) *
      ((((q : ℝ)^4 + 1) * beta q - 2 * (q : ℝ)^4) /
        (((q : ℝ)^2 + 1) * beta q - 2 * (q : ℝ)^2))
  let b : ℕ → ℝ := fun q => d q - 1 / (2 * (q : ℝ))
  (∀ (q : ℕ), 3 ≤ q → ∀ (s : ℝ), (2 / 3 : ℝ) ≤ s →
    (161 / 90 : ℝ) < deriv (G q) s) ∧
  (∀ (q : ℕ), 3 ≤ q → ∀ (a b : ℝ), (2 / 3 : ℝ) ≤ a → a ≤ b →
    (161 / 90 : ℝ) * (b - a) ≤ G q b - G q a ∧
      (a < b → (161 / 90 : ℝ) * (b - a) < G q b - G q a)) ∧
  (∀ (q : ℕ), 3 ≤ q → ∀ (s : ℝ), (2 / 3 : ℝ) ≤ s →
    (G q s = 2 ↔ s = sigma q)) ∧
  Tendsto (fun q : ℕ => (q : ℝ) * d q) atTop (nhds (Real.log 2 / 6)) ∧
  Tendsto (fun q : ℕ => (q : ℝ) * b q) atTop (nhds (Real.log 2 / 6 - 1 / 2))

abbrev profileArena : Arena where
  signature := profileSignature
  Law := profileLaw

private theorem profile_actual_bridge :
    (type_of% square_displacement_profile) ↔ profileArena.Law profileActual := by
  simp [profileArena, profileLaw, profileActual, realize]

private theorem profile_actual_law : profileArena.Law profileActual := by
  simpa [profileArena, profileLaw, profileActual, realize] using
    square_displacement_profile

private theorem zero_sigma_not_law : ¬ profileArena.Law (profileRejected 1) := by
  intro h
  let s : ℝ := Real.log (dbonacciPerronRoot 9)
  have hs : (2 / 3 : ℝ) < s := by
    simpa only [s, _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.s_star]
      using _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.two_thirds_lt_s_star
  have hactual : Real.exp s + Real.exp (-(3 : ℝ)^2 * s) = 2 := by
    have hroot := square_displacement_profile.2.2.1 3 (by norm_num) s hs.le
    apply hroot.mpr
    norm_num [s]
  have hbad : (Real.exp s + Real.exp (-(3 : ℝ)^2 * s) = 2 ↔ s = 0) := by
    simpa [profileArena, profileLaw, profileRejected, profileActual, realize]
      using h.2.2.1 3 (by norm_num) s hs.le
  have hz := hbad.mp hactual
  linarith only [hs, hz]

/-- Auxiliary limit evidence on exactly Nat, used by the beta intervention. -/
private theorem native_limit_data :
    Tendsto (fun q : ℕ => ((q : ℝ)^2)⁻¹) atTop (nhds 0) ∧
    Tendsto (fun q : ℕ => Real.log (dbonacciPerronRoot (q^2)))
      atTop (nhds (Real.log 2)) ∧
    Tendsto (fun q : ℕ => ((q : ℝ)^2 + 1) / ((q : ℝ)^2 - 1))
      atTop (nhds 1) := by
  have hv : Tendsto (fun q : ℕ => (q : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by decide : 2 ≠ 0)).comp
      tendsto_natCast_atTop_atTop
  have hσ : Tendsto (fun q : ℕ => Real.log (dbonacciPerronRoot (q^2)))
      atTop (nhds (Real.log 2)) :=
    (dbonacciPerronRoot_tendsto_two.comp
      (tendsto_pow_atTop (α := ℕ) (by decide : 2 ≠ 0))).log (by norm_num)
  refine ⟨tendsto_inv_atTop_zero.comp hv, hσ, ?_⟩
  have hm : Tendsto (fun q : ℕ => (q : ℝ)^2 - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) hv
  have hi := tendsto_inv_atTop_zero.comp hm
  have hr : Tendsto (fun q : ℕ => 1 + 2 * ((q : ℝ)^2 - 1)⁻¹)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (nhds 1)).add ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)).mul hi)
  apply hr.congr'
  filter_upwards [eventually_ge_atTop 3] with q hq
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hm0 : (q : ℝ)^2 - 1 ≠ 0 := by nlinarith only [hqR]
  field_simp [hm0] <;> ring

private theorem zero_beta_not_law : ¬ profileArena.Law (profileRejected 0) := by
  intro h
  let S : ℕ → ℝ := fun q => Real.log (dbonacciPerronRoot (q^2))
  let D : ℕ → ℝ := fun q =>
    (((q : ℝ)^2 + 1) * S q / (6 * (q : ℝ) * ((q : ℝ)^2 - 1))) *
      ((-2 * (q : ℝ)^4) / (-2 * (q : ℝ)^2))
  have hfinite : Tendsto (fun q : ℕ => (q : ℝ) * D q) atTop
      (nhds (Real.log 2 / 6)) := by
    simpa [D, S, profileArena, profileLaw, profileRejected, profileActual, realize]
      using h.2.2.2.1
  have hn := native_limit_data
  have hzero : Tendsto (fun q : ℕ => ((q : ℝ) * D q) * ((q : ℝ)^2)⁻¹)
      atTop (nhds 0) := by
    simpa using hfinite.mul hn.1
  have hprod : Tendsto (fun q : ℕ => (S q / 6) *
      (((q : ℝ)^2 + 1) / ((q : ℝ)^2 - 1)))
      atTop (nhds (Real.log 2 / 6)) := by
    simpa only [S, mul_one] using (hn.2.1.div_const 6).mul hn.2.2
  have hpositive : Tendsto (fun q : ℕ => ((q : ℝ) * D q) * ((q : ℝ)^2)⁻¹)
      atTop (nhds (Real.log 2 / 6)) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 3] with q hq
    have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hq0 : (q : ℝ) ≠ 0 := by linarith only [hqR]
    have hm0 : (q : ℝ)^2 - 1 ≠ 0 := by nlinarith only [hqR]
    dsimp [D]
    field_simp [hq0, hm0] <;> ring
  have heq : (0 : ℝ) = Real.log 2 / 6 := tendsto_nhds_unique hzero hpositive
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  linarith only [heq, hlog]

private theorem profile_rejected_law (i : Fin 2) :
    ¬ profileArena.Law (profileRejected i) := by
  fin_cases i
  · exact zero_beta_not_law
  · exact zero_sigma_not_law

private theorem native_state_variation :
    profileActual.readout 0 () 3 < profileActual.readout 0 () 4 ∧
      profileActual.readout 1 () 3 < profileActual.readout 1 () 4 := by
  have hβ : dbonacciPerronRoot 9 < dbonacciPerronRoot 16 :=
    dbonacciPerronRoot_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
  have hσ : Real.log (dbonacciPerronRoot 9) < Real.log (dbonacciPerronRoot 16) :=
    Real.strictMonoOn_log
      (lt_trans zero_lt_one (one_lt_dbonacciPerronRoot 9 (by norm_num)))
      (lt_trans zero_lt_one (one_lt_dbonacciPerronRoot 16 (by norm_num))) hβ
  simpa [profileActual, realize] using And.intro hβ hσ

private theorem profile_actual_dependence :
    ObservationalDependence profileSignature profileActual := by
  intro i
  refine ⟨(), 3, 4, ?_⟩
  have hv := native_state_variation
  fin_cases i
  · exact ne_of_lt hv.1
  · exact ne_of_lt hv.2

noncomputable def profileSource : Registration profileArena
    (type_of% square_displacement_profile) where
  actual := profileActual
  bridge := profile_actual_bridge
  variation := ⟨profile_actual_law, profileRejected 0, profile_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨profileRejected i, ?_, rfl, profile_rejected_law i⟩
      intro j hj
      funext p q
      simp [profileRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := profile_actual_dependence

noncomputable def profileRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@square_displacement_profile)
      (Realization profileSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile.square_displacement_profile.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile.profileSource
  realizationSource := none
  generated := false
  arena := .source ⟨profileArena⟩
  objectArena := .source ⟨profileArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source profileArena ⟨profileSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some profileActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile
