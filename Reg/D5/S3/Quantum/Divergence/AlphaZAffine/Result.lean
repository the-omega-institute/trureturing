import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.AlphaZAffine.Result
import Reg.Support.SingleDependentReadout

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.AlphaZAffine
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Divergence.AlphaZAffine.Result

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ → ℝ) (fun _ => Set ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ f s => MonotoneOn f s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {ρ σ : Matrix d d ℂ}, ρ.PosSemidef → σ.PosSemidef → ρ ≠ 0 →
    (∀ x : d → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0) →
    ∀ {κ z₀ : ℝ}, 0 < κ → 0 ≤ z₀ →
    R.readout () () (fun a => hiaiD ρ σ a (affineZ κ z₀ a)) (Set.Ioi (0 : ℝ))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) Matrix.PosSemidef.one Matrix.PosSemidef.one
    one_ne_zero (fun x hx => hx) (κ := 1) (z₀ := 0) zero_lt_one le_rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun a => -a), ?_⟩
  intro he
  have hz : actual.readout () () (fun _ => 0) (Set.Ioi (0 : ℝ)) :=
    fun _ _ _ _ _ => le_rfl
  have hm : MonotoneOn (fun a : ℝ => -a) (Set.Ioi (0 : ℝ)) :=
    Eq.mp (congrFun he (Set.Ioi (0 : ℝ))) hz
  have hn := hm (a := 1) (b := 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hn
def family : Registration arena.{u} (type_of% (@result.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.AlphaZAffine.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.AlphaZAffine.Result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ f s => MonotoneOn f s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.AlphaZAffine.Result
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Quantum.Divergence.AlphaZAffine.Result
