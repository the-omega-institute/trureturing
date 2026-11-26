import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuPhysicalHighHigh

/-! Source-bound equality readout for the weighted physical cost. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuPhysicalHighHigh

namespace Reg.D5.S3.Quantum.Semigroups.WuPhysicalHighHigh

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def shifted : Realization signature :=
  realize signature (fun _ _ x y => x = y + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ (u v : Vec), pairing u u = 1 → pairing v v = 1 → pairing u v = 0 →
    ∀ (dp dm : ℝ), 0 ≤ dp → 0 ≤ dm →
    let A := (dp + dm) / 2
    let rho := (dp - dm) / (dp + dm)
    let product := A * (1 + rho * imbalance u) * (1 - rho * imbalance v)
    let paritySquare := A * ((2 - rho ^ 2) / 4) * Complex.normSq (eta u v)
    let twistSquare := A * Complex.normSq (sigma u v + (rho : ℂ) * tau u v)
    W.readout () () (dp * weight u v + dm * weight v u) (product - paritySquare - twistSquare) ∧
    ∀ marginalPlus marginalMinus : ℝ,
      dp * (marginalPlus - weight u v) + dm * (marginalMinus - weight v u) =
        (dp * marginalPlus + dm * marginalMinus - product) + paritySquare + twistSquare

private theorem shifted_law_fails : ¬ arena.Law shifted := by
  intro hlaw
  let u : Vec := Pi.single (0, 0) 1
  let v : Vec := Pi.single (1, 1) 1
  have hne : ((1, 1) : Occupation) ≠ (0, 0) := by decide
  have hu : pairing u u = 1 := by
    simp [u, pairing, dotProduct_single_one]
  have hv : pairing v v = 1 := by
    simp [v, pairing, dotProduct_single_one]
  have huv : pairing u v = 0 := by
    simp [u, v, pairing, dotProduct_single_one, Pi.single_eq_of_ne hne]
  have heta : eta u v = 0 := by
    simp [eta, pairing, u, v, Matrix.mulVec_single_one, single_one_dotProduct,
      Matrix.col_apply, parity, Matrix.diagonal_apply, Ne.symm hne]
  have hsigma : sigma u v = -1 := by
    norm_num [sigma, theta, pairing, u, v, Matrix.mulVec_single_one, single_one_dotProduct,
      Matrix.col_apply, omega, Matrix.single_apply]
  have hshifted := (hlaw u v hu hv huv 1 1 zero_le_one zero_le_one).1
  have hexact := (weighted_high_high u v hu hv huv 1 1 zero_le_one zero_le_one).1
  -- With equal direction weights, dropping both squares raises the predicted cost by one.
  norm_num [shifted, realize, heta, hsigma] at hshifted hexact
  linarith only [hshifted, hexact]

def family : Registration arena (type_of% @weighted_high_high) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@weighted_high_high, shifted, shifted_law_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ shifted shifted_law_fails
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) (rfl : (0 : ℝ) = 0))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_high_high) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuPhysicalHighHigh.weighted_high_high.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuPhysicalHighHigh.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuPhysicalHighHigh
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Nine arguments, five source lets, then the equality in the first conjunct.
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Semigroups.WuPhysicalHighHigh
