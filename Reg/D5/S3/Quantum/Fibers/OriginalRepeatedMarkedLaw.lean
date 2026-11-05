import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw
import Reg.Support.DependentFamily

/-! The native interior bound uses the actual height observation. -/

open Set
open _root_.D5.S3.Quantum.Fibers
open OriginalControlComposition OriginalRepeatedPrefix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature (fun _ _ x => x) (fun a => nomatch a)
def rejected := realize signature (fun _ _ _ => (-1 : ℝ)) (fun a => nomatch a)

def theoremLaw (R : Realization signature) : Prop :=
  ∀ (c U chi : ℝ) (k : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) U k (fun _ => chi))
    (t : ℝ) (ht : t ∈ Icc 0 U), R.readout () () (k t) ∈ Ioo 0 c

abbrev arena : Arena where
  signature := signature
  Law := theoremLaw

private def band : Band :=
  ⟨1/5,3/10,2/5,by norm_num,by norm_num,by norm_num,by norm_num⟩

private theorem actual_law : arena.Law actual := by
  intro c U chi k hk t ht
  exact _root_.D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw.native_bounds
    c U chi k hk t ht

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hk := (band.suffix_facts 0 false).1
  have he := h band.c 1 0 band.lateSuffix hk 0 (by norm_num)
  norm_num [rejected, realize] at he

def family : Registration arena
    (type_of% (@_root_.D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw.native_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw.native_bounds)
    (type_of% (realize signature (fun _ _ x => x) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw
