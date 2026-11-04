import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Completion.HistoryKernelConverse
import Reg.Support.DependentFamily

/-! Source-family registration of the complete kernel telescopes. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Completion.HistoryKernelExtension
open _root_.D5.S3.Quantum.Completion.HistoryKernelConverse
open scoped ComplexOrder MatrixOrder

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
namespace Reg.D5.S3.Quantum.Completion.HistoryKernelConverse

abbrev signature : Signature.{u+1,u,0,u,0} where
  Params := Type u
  State X := X → X → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := X → X → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature.{u}
  (fun _ _ K => K) (fun e => nomatch e)
def rejected : Realization signature := realize signature.{u}
  (fun _ _ _ => fun _ _ => (-1 : ℂ)) (fun e => nomatch e)

private theorem zero_law (X : Type u) : KernelExtensionLaw (fun _ _ : X => (0 : ℂ)) :=
  (extensionLaw_iff_kernel_posSemidef _).mpr Matrix.PosSemidef.zero

private theorem negative_not_law :
    ¬ KernelExtensionLaw (fun _ _ : ULift.{u} Unit => (-1 : ℂ)) := by
  intro h
  have hp := extensionLaw_finiteGram_posSemidef _ h 1 (fun _ => ULift.up ())
  have hn := hp.diag_nonneg (i := (0 : Fin 1))
  norm_num [finiteGram, Complex.nonneg_iff] at hn

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, (fun _ _ => (0 : ℂ)), (fun _ _ => (-1 : ℂ)), ?_⟩
  intro h
  have he := congrArg (fun F : ULift.{u} Unit → ULift.{u} Unit → ℂ =>
    F (ULift.up ()) (ULift.up ())) h
  norm_num [actual, realize] at he

private theorem sensitivity (law : Realization signature.{u} → Prop) (hbad : ¬ law rejected.{u}) :
    Sensitivity ⟨signature.{u}, law⟩ actual := by
  constructor
  · intro i
    refine ⟨rejected.{u}, ?_, rfl, hbad⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim
  · intro e
    exact nomatch e

private theorem zero_certificate (X : Type u) :
    ∀ n (L : Fin n → X), CertifiedHistory (fun _ _ : X => (0 : ℂ)) n L := by
  intro n
  induction n with
  | zero => intro L; trivial
  | succ n ih =>
      intro L
      obtain ⟨c, r, heq⟩ := zero_law X n (fun i => L i.succ) (L 0)
      exact ⟨ih _, c, r, heq⟩

private theorem zero_cover (X : Type u) :
    CertifiedFiniteCover (fun _ _ : X => (0 : ℂ)) := by
  classical
  intro s
  let e := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, (fun i => (e i).val), zero_certificate X _ _, ?_⟩
  intro x hx
  exact ⟨e.symm ⟨x, hx⟩, by simp⟩

namespace Finite
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (K : X → X → ℂ), KernelExtensionLaw (R.readout () X K) ↔
      ∀ (n : ℕ) (L : Fin n → X), (finiteGram K L).PosSemidef
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz : ∀ (n : ℕ) (L : Fin n → ULift.{u} Unit),
      (finiteGram (fun _ _ => (0 : ℂ)) L).PosSemidef := by
    intro n L
    exact Matrix.PosSemidef.zero
  exact negative_not_law ((@h (ULift.{u} Unit) (fun _ _ => 0)).mpr hz)
def family : Registration arena.{u} (type_of% (@extensionLaw_iff_finiteGram_posSemidef.{u})) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨@extensionLaw_iff_finiteGram_posSemidef.{u}, rejected.{u}, rejected_law⟩
  sensitivity := sensitivity.{u} arena.{u}.Law rejected_law
  dependence := dependence.{u}

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@extensionLaw_iff_finiteGram_posSemidef.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.HistoryKernelConverse.extensionLaw_iff_finiteGram_posSemidef.audit
  realizationName := `Reg.D5.S3.Quantum.Completion.HistoryKernelConverse.Finite.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ K => K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.HistoryKernelConverse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Finite

namespace Global
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (K : X → X → ℂ),
    KernelExtensionLaw (R.readout () X K) ↔ (Matrix.of K).PosSemidef
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact negative_not_law ((@h (ULift.{u} Unit) (fun _ _ => 0)).mpr Matrix.PosSemidef.zero)
def family : Registration arena.{u} (type_of% (@extensionLaw_iff_kernel_posSemidef.{u})) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨@extensionLaw_iff_kernel_posSemidef.{u}, rejected.{u}, rejected_law⟩
  sensitivity := sensitivity.{u} arena.{u}.Law rejected_law
  dependence := dependence.{u}

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@extensionLaw_iff_kernel_posSemidef.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.HistoryKernelConverse.extensionLaw_iff_kernel_posSemidef.audit
  realizationName := `Reg.D5.S3.Quantum.Completion.HistoryKernelConverse.Global.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ K => K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.HistoryKernelConverse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Global

namespace Cover
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (K : X → X → ℂ),
    CertifiedFiniteCover K → KernelExtensionLaw (R.readout () X K)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact negative_not_law (@h (ULift.{u} Unit) (fun _ _ => 0) (zero_cover _))
def family : Registration arena.{u} (type_of% (@certifiedFiniteCover_extensionLaw.{u})) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨@certifiedFiniteCover_extensionLaw.{u}, rejected.{u}, rejected_law⟩
  sensitivity := sensitivity.{u} arena.{u}.Law rejected_law
  dependence := dependence.{u}

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@certifiedFiniteCover_extensionLaw.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.HistoryKernelConverse.certifiedFiniteCover_extensionLaw.audit
  realizationName := `Reg.D5.S3.Quantum.Completion.HistoryKernelConverse.Cover.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ K => K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.HistoryKernelConverse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Cover

end Reg.D5.S3.Quantum.Completion.HistoryKernelConverse
