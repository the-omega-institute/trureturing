import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The comparison readout retains the complete scalar family. -/
set_option autoImplicit false
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Algebra
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1
noncomputable section
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : Nat) (hn : 5 ≤ n) (hn' : n ≤ 18)
    (j r H D q a : ℝ) (hj : 10 ≤ j) (hj' : j ≤ (5*n : Nat)-15)
    (h : Hyp r H D q a),
    R.readout () () (energy (5*n : Nat) j r H D q a)
      (theta (5*n : Nat)*(mass (5*n : Nat) j r H D)^2)

private theorem zero_hyp : Hyp 0 0 0 0 0 := by
  constructor <;> norm_num [charge]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 5 (by decide) (by decide) 10 0 0 0 0 0 (by norm_num) (by norm_num) zero_hyp

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) (le_refl 0)
  norm_num at hf
private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected,?_,?_,rejected_law⟩
    · intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · funext e; exact nomatch e
  · intro e; exact nomatch e

def family : Registration arena (type_of% scalar_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨scalar_bound,rejected,rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1.scalar_bound)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1
