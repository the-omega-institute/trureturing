import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.FiveModeRealResponse
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ComplexOrder
namespace Reg.D5.S3.Quantum.Fibers.FiveModeRealResponse
open _root_.D5.S3.Quantum.Fibers.FiveModeRealResponse
open _root_.D5.S3.Quantum.Fibers.FiveModeRealWaitSpan
open _root_.D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
open _root_.D5.S3.Quantum.QuantumChannels.RealPartPositiveObstruction
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 5) (Fin 5) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (P : Protocol (Fin 5)) → Record P → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ X P h => ludersLaw menu P X h) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ X Y : Matrix (Fin 5) (Fin 5) ℂ,
    X.IsHermitian → Y.IsHermitian →
    ((∀ (P : Protocol (Fin 5)) (h : Record P), R.readout () () X P h = R.readout () () Y P h)
      ↔ realEntries X = realEntries Y) ∧ Module.finrank ℝ waitSpan = 15 ∧
    Submodule.span ℝ (Set.range (fun p : (P : Protocol (Fin 5)) × Record P =>
      recordEffect walk p.1 p.2)) = symmetricEffectSpace ∧
    (∃ effects : Finset (Matrix (Fin 5) (Fin 5) ℂ),
      (↑effects : Set _) ⊆ Set.range (fun p : (P : Protocol (Fin 5)) × Record P =>
        recordEffect walk p.1 p.2) ∧
      Submodule.span ℝ (effects : Set _) = symmetricEffectSpace) ∧
    (∀ (Seed : Type) [MeasurableSpace Seed] (μ : MeasureTheory.Measure Seed)
      (strategy : Seed → Protocol (Fin 5)) (event : ∀ c, Finset (Record (strategy c))),
      realEntries X = realEntries Y →
        (∫ c, ∑ h ∈ event c, R.readout () () X (strategy c) h ∂μ) =
        (∫ c, ∑ h ∈ event c, R.readout () () Y (strategy c) h ∂μ)) ∧
    (∀ Z : Matrix (Fin 5) (Fin 5) ℂ, Z.PosSemidef →
      ∀ (P : Protocol (Fin 5)) (h : Record P),
        R.readout () () (symmetrize Z) P h = R.readout () () Z P h) ∧
    ¬ MatrixMap.IsCompletelyPositive (symmetrize (n := Fin 5)) ∧
    finiteOrthogonalReadout (fun Z P h => R.readout () () Z P h)

private theorem bridge : (type_of% (@five_mode_real_response_fiber)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 0 1 Matrix.isHermitian_zero Matrix.isHermitian_one).1.mp (by intros; rfl)
  have hz := congrFun (congrFun he 0) 0
  norm_num [realEntries] at hz

def family : Registration arena (type_of% (@five_mode_real_response_fiber)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp five_mode_real_response_fiber, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrArg (fun f => f .stop PUnit.unit) h
    change (Matrix.trace (0 : Matrix (Fin 5) (Fin 5) ℂ)).re =
      (Matrix.trace (1 : Matrix (Fin 5) (Fin 5) ℂ)).re at he
    norm_num at he

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Fibers.FiveModeRealResponse.five_mode_real_response_fiber)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.FiveModeRealResponse.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.FiveModeRealResponse.family
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
    (fun _ _ X P h => ludersLaw menu P X h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Quantum.Fibers.FiveModeRealResponse
