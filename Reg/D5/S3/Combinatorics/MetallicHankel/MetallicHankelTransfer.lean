import D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransfer
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransfer

open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Input where
  n : ℕ
  z : ℤ × ℤ

def claimAt (a : Input) : Prop :=
  (topWord a.n).foldl (fun z c => (c.1 * z.1 - c.2 * z.2, z.1)) a.z = a.z

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Input) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ a => claimAt a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (hn : 2 ≤ n) (z : ℤ × ℤ), r.readout () () ⟨n, z⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 2 (by omega) (1, 0)

def badInput : Input := ⟨0, (1, 0)⟩

private theorem bad_claim : ¬ claimAt badInput := by
  norm_num [claimAt, badInput, topWord, List.foldl_cons, List.foldl_nil]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), badInput, ⟨2, (1, 0)⟩, ?_⟩
  intro h
  apply bad_claim
  exact Eq.mpr h (top_word_identity 2 (by omega) (1, 0))

def family : Registration arena (type_of% (@top_word_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@top_word_identity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@top_word_identity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransfer.top_word_identity.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => claimAt a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms top_word_identity
#print axioms family
#print axioms registration

end Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransfer
