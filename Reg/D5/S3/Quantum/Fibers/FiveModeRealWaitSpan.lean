import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.FiveModeRealWaitSpan
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.Quantum.Fibers.FiveModeRealWaitSpan
open _root_.D5.S3.Quantum.Fibers.FiveModeRealWaitSpan
open _root_.D5.S3.Quantum.Fibers.NonnegativeConjugationSpan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 5
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := NNReal → Matrix (Fin 5) (Fin 5) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ s t => conjugate generator (Matrix.single s s 1) t) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := Submodule.span ℝ (Set.range (fun p : NNReal × Fin 5 => R.readout () () p.2 p.1)) =
    symmetricSpace

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : (⊥ : Submodule ℝ (Matrix (Fin 5) (Fin 5) ℝ)) = symmetricSpace := by
    simpa [arena, rejected, realize] using h
  have hm : Matrix.single (0 : Fin 5) 0 (1 : ℝ) ∈
      (⊥ : Submodule ℝ (Matrix (Fin 5) (Fin 5) ℝ)) := by
    rw [he]
    simp [symmetricSpace, Matrix.transpose_single]
  have hz := (Submodule.mem_bot ℝ).mp hm
  have hh := congrFun (congrFun hz 0) 0
  norm_num at hh

def family : Registration arena (type_of% (@five_mode_nonnegative_wait_span)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨five_mode_nonnegative_wait_span, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrArg (fun f => f 0 0 0) h
    norm_num [actual, realize, conjugate] at he

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Fibers.FiveModeRealWaitSpan.five_mode_nonnegative_wait_span)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.FiveModeRealWaitSpan.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.FiveModeRealWaitSpan.family
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
    (fun _ _ s t => conjugate generator (Matrix.single s s 1) t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Quantum.Fibers.FiveModeRealWaitSpan
