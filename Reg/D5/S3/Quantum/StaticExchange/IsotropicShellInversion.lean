import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.StaticExchange.IsotropicShellInversion
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.NormNum

/-! Input-dependent readouts for the two shell inversion conclusions. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.StaticExchange.IsotropicShellInversion
open LeanInformationAudit Set MeasureTheory Filter
open scoped Topology
namespace Reg.D5.S3.Quantum.StaticExchange.IsotropicShellInversion
noncomputable section

namespace Mass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)

def actual : Realization signature := realize signature (fun _ _ f => f) (fun e => nomatch e)
def shifted : Realization signature := realize signature (fun _ _ f r => f r + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {f d : ℝ → ℝ}
    (hd : ∀ r, 0 ≤ r → HasDerivAt f (d r) r) (hs : ∀ r, 0 < r → d r ≤ 0)
    (h∞ : Tendsto f atTop (𝓝 0)) (hr∞ : Tendsto (fun r => r * f r) atTop (𝓝 0))
    (hf : IntegrableOn f (Ioi 0)) (hrd : IntegrableOn (fun r => r * d r) (Ioi 0)),
    (∀ r, 0 ≤ r → 0 ≤ shell d r) ∧ (∀ t, 0 ≤ t → projection (shell d) t = R.readout () () f t) ∧
      ∫ r in Ioi (0 : ℝ), shell d r = 2 * ∫ r in Ioi (0 : ℝ), f r

private theorem shifted_fails : ¬arena.Law shifted := by
  intro law
  have h := law (f := fun _ => 0) (d := fun _ => 0)
    (fun r _ => hasDerivAt_const r 0) (by simp) tendsto_const_nhds (by simp)
    (by simp) (by simp)
  have eq := h.2.1 1 (by norm_num)
  change projection (shell (fun _ => 0)) 1 = 0 + 1 at eq
  simp [projection, shell] at eq

def family : Registration arena (type_of% @shell_projection_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨shell_projection_mass, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro i
    exact ⟨(), (fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (1 : ℝ)), fun h =>
      zero_ne_one (congrFun h 0)⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.StaticExchange.IsotropicShellInversion.shell_projection_mass)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.StaticExchange.IsotropicShellInversion.Mass.unit
  realizationName := `Reg.D5.S3.Quantum.StaticExchange.IsotropicShellInversion.Mass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.StaticExchange.IsotropicShellInversion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Mass

namespace Unique

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)

def actual : Realization signature := realize signature (fun _ _ f => f) (fun e => nomatch e)
def shifted : Realization signature := realize signature (fun _ _ f r => f r + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {h f : ℝ → ℝ}
    (hc : ContinuousOn h (Ioi 0))
    (hi : ∀ t, 0 < t → IntegrableOn (fun r => h r / (2 * r)) (Ioi t))
    (same : ∀ t, 0 < t → projection h t = f t),
    ∀ r, 0 < r → R.readout () () h r = shell (deriv f) r

private theorem shifted_fails : ¬arena.Law shifted := by
  intro law
  have h := law (h := fun _ => 0) (f := fun _ => 0) continuousOn_const
    (by simp) (by simp [projection]) 1 (by norm_num)
  change (0 : ℝ) + 1 = shell (deriv (fun _ : ℝ => (0 : ℝ))) 1 at h
  simp [shell] at h

def family : Registration arena (type_of% @shell_density_unique) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨shell_density_unique, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro i
    exact ⟨(), (fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (1 : ℝ)), fun h =>
      zero_ne_one (congrFun h 0)⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.StaticExchange.IsotropicShellInversion.shell_density_unique)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.StaticExchange.IsotropicShellInversion.Unique.unit
  realizationName := `Reg.D5.S3.Quantum.StaticExchange.IsotropicShellInversion.Unique.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.StaticExchange.IsotropicShellInversion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Unique

end
end Reg.D5.S3.Quantum.StaticExchange.IsotropicShellInversion
