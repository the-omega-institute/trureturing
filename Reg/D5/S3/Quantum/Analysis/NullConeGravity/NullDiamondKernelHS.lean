import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernelHS
import Reg.Support.DependentFamily
import Mathlib.MeasureTheory.Measure.Dirac.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory
open scoped ENNReal
open _root_.NullConeGravity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernelHS

universe u

abbrev signature : Signature where
  Params := Σ X : Type u, X
  State p := p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p g => g p.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (g : X → ℂ)
    (hg : MemLp g ∞ μ) (f : Lp ℂ 2 μ),
    (mulOp μ g hg f : X → ℂ) =ᵐ[μ] fun x => r.readout () ⟨X, x⟩ g * f x

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hlaw
  let X := ULift.{u} Unit
  let _ : MeasurableSpace X := ⊤
  let _ : MeasurableSingletonClass X := ⟨fun _ => trivial⟩
  let a : X := ⟨()⟩
  let μ : Measure X := Measure.dirac a
  let f : Lp ℂ 2 μ := (memLp_const (μ := μ) 1).toLp (fun _ : X => 1)
  let g : X → ℂ := fun _ => 0
  have hg : MemLp g ∞ μ := memLp_const 0
  have hbad := hlaw μ g hg f
  have ha := mulOp_ae μ g hg f
  have hf : (f : X → ℂ) =ᵐ[μ] fun _ => 1 := MemLp.coeFn_toLp _
  have hc : ∀ᵐ x ∂μ, (0 : ℂ) = 1 := by
    filter_upwards [hbad, ha, hf] with x hbx hax hfx
    change (mulOp μ g hg f) x = 1 * f x at hbx
    calc
      0 = g x * f x := by simp [g]
      _ = (mulOp μ g hg f) x := hax.symm
      _ = 1 * f x := hbx
      _ = 1 := by simp [hfx]
  have hμ : μ ≠ 0 := by simp [μ]
  let _ : NeZero μ := ⟨hμ⟩
  exact zero_ne_one hc.exists.choose_spec

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} Unit, ⟨()⟩⟩, 0, 1, ?_⟩
  exact zero_ne_one

abbrev sourceStatement : Prop := type_of% @mulOp_ae.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := realize signature (fun _ p g => g p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@mulOp_ae.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def mulOp_ae_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@mulOp_ae.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernelHS.mulOp_ae_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernelHS.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p g => g p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernelHS
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernelHS
