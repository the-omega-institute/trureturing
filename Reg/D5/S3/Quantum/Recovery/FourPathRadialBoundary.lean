import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathRadialBoundary
import Reg.Support.SingleDependentReadout

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.FourPathRadialBoundary

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FourPathRadialBoundary

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => Point) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ w => m w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private def geometry (q : Point → ℝ) : Prop :=
    W = {w | q w ≤ 1} ∧
    interior W = {w | q w < 1} ∧
    frontier W = {w | q w = 1} ∧
    frontier W = {z | z ∈ W ∧ (maxMod z = 1 ∨ totalMod z - 2 * minMod z = 2)} ∧
    (∀ w ∈ W, w ≠ 0 →
      ∃ t : ℝ, ∃ z : Point, 0 < t ∧ t ≤ 1 ∧ t = q w ∧ q z = 1 ∧ w = t • z ∧
        ∀ s : ℝ, ∀ y : Point, 0 < s → q y = 1 → w = s • y → s = t ∧ y = z)

def arena : Arena where
  signature := signature
  Law R := geometry (R.readout () ())

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hw : (0 : Point) ∈ W := by simp [W, totalMod, minMod]
  have he := congrArg (fun s : Set Point => (0 : Point) ∈ s) h.1
  have : (2 : ℝ) ≤ 1 := Eq.mp he hw
  norm_num at this

def registration : Registration arena (type_of% exact_radial_boundary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_radial_boundary, rejected, rejected_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := by
    intro i
    refine ⟨(), (0 : Point), (fun _ => (1 : ℂ)), ?_⟩
    change m (0 : Point) ≠ m (fun _ => (1 : ℂ))
    norm_num [m, maxMod, minMod, totalMod]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    exact_radial_boundary (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.FourPathRadialBoundary.exact_radial_boundary.audit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathRadialBoundary.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => m w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.FourPathRadialBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.FourPathRadialBoundary
