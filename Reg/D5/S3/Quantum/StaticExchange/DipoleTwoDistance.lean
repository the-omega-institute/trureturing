import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.StaticExchange.DipoleTwoDistance
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.FinCases

/-! Two coincident distances cannot carry the asserted strict minor. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.StaticExchange.DipoleTwoDistance
open LeanInformationAudit Finset Real
namespace Reg.D5.S3.Quantum.StaticExchange.DipoleTwoDistance
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def shifted : Realization signature := realize signature (fun _ _ x => x + 1) (fun e => nomatch e)

namespace Minor

def arena : Arena where
  signature := signature
  Law R := ∀ {x y a b : ℝ} (hx : 0 < x) (hxy : x < R.readout () () y)
    (ha : 0 < a) (hab : a < b),
    profile (x * a) * profile (y * b) < profile (x * b) * profile (y * a)

private theorem shifted_fails : ¬arena.Law shifted := by
  intro law
  have h := law (x := 1) (y := 1) (a := 1) (b := 2) (by norm_num)
    (by change (1 : ℝ) < 1 + 1; norm_num) (by norm_num) (by norm_num)
  exact (lt_irrefl _) (by simpa only [mul_comm] using h)

def family : Registration arena (type_of% @profile_minor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨profile_minor, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro i
    exact ⟨(), (0 : ℝ), (1 : ℝ), (zero_ne_one : (0 : ℝ) ≠ 1)⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.StaticExchange.DipoleTwoDistance.profile_minor)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.StaticExchange.DipoleTwoDistance.Minor.unit
  realizationName := `Reg.D5.S3.Quantum.StaticExchange.DipoleTwoDistance.Minor.family
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
    owner := `D5.S3.Quantum.StaticExchange.DipoleTwoDistance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Minor

namespace Spectral

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (p g : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hg : ∀ i, 0 < g i) (support : ∃ i j, 0 < p i ∧ 0 < p j ∧ g i < g j)
    {x y : ℝ} (hx : 0 < x) (hxy : x < R.readout () () y),
    moment p g 2 x * moment p g 4 y < moment p g 4 x * moment p g 2 y ∧
    Function.Injective (fun c : ℝ × ℝ =>
      (c.1 * moment p g 2 x + c.2 * moment p g 4 x,
       c.1 * moment p g 2 y + c.2 * moment p g 4 y))

private theorem shifted_fails : ¬arena.Law shifted := by
  intro law
  let g : Fin 2 → ℝ := ![1, 2]
  have hg : ∀ i, 0 < g i := by intro i; fin_cases i <;> norm_num [g]
  have h := (law (fun _ => 1) g (fun _ => by norm_num) hg
    ⟨0, 1, by norm_num, by norm_num, by norm_num [g]⟩ (x := 1) (y := 1)
    (by norm_num) (by change (1 : ℝ) < 1 + 1; norm_num)).1
  exact (lt_irrefl _) (by simpa only [mul_comm] using h)

def family : Registration arena (type_of% @finite_spectral_separation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_spectral_separation, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro i
    exact ⟨(), (0 : ℝ), (1 : ℝ), (zero_ne_one : (0 : ℝ) ≠ 1)⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.StaticExchange.DipoleTwoDistance.finite_spectral_separation)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.StaticExchange.DipoleTwoDistance.Spectral.unit
  realizationName := `Reg.D5.S3.Quantum.StaticExchange.DipoleTwoDistance.Spectral.family
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
    owner := `D5.S3.Quantum.StaticExchange.DipoleTwoDistance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Spectral

end
end Reg.D5.S3.Quantum.StaticExchange.DipoleTwoDistance
