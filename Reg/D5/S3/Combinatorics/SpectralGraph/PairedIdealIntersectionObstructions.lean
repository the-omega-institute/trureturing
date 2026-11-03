import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
open _root_.D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
set_option autoImplicit false
noncomputable section

abbrev matrixSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def lowerLaw (f : ℝ → ℝ → ℝ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) : Prop :=
  ∀ (a b c : ℝ), 0 < a → 0 ≤ b → 0 ≤ c → (f a b c-1).PosDef

def lowerActual : Realization matrixSignature :=
  realize matrixSignature (fun _ p c => symmetricK p.1 p.2 c) (fun e => nomatch e)
def lowerRejected : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev lowerArena : Arena where
  signature := matrixSignature
  Law r := lowerLaw (fun a b c => r.readout () ⟨a,b⟩ c)

private theorem lower_rejected : ¬ lowerArena.Law lowerRejected := by
  intro h
  have hp := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  have hv : (fun _ : Fin 2 × Fin 2 => (1 : ℝ)) ≠ 0 := by
    intro hz
    have hh := congrFun hz (0,0)
    norm_num at hh
  have hh := hp.dotProduct_mulVec_pos hv
  simp [lowerRejected,realize] at hh

private theorem lower_dependence : ObservationalDependence matrixSignature lowerActual := by
  intro i
  refine ⟨⟨1,1⟩,1,2,?_⟩
  intro he
  have hh := congrFun (congrFun he (0,0)) (0,0)
  norm_num [lowerActual,realize,symmetricK,E,H,Matrix.kroneckerMap_apply] at hh

def lowerSource : Registration lowerArena (type_of% @symmetricK_sub_one_posDef) where
  actual := lowerActual
  bridge := Iff.rfl
  variation := ⟨@symmetricK_sub_one_posDef,lowerRejected,lower_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lowerRejected,?_,rfl,lower_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := lower_dependence

def lowerRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@symmetricK_sub_one_posDef) (Realization matrixSignature) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions.lowerUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions.lowerSource
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena⟩
  objectArena := .source ⟨lowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena ⟨lowerSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p c => symmetricK p.1 p.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
