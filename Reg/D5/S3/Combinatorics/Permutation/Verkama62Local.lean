import Reg.D5.S3.Combinatorics.Permutation.Verkama62Count

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Permutation.Verkama62Local
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.Verkama62Local
open _root_.D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)
open Reg.D5.S3.Combinatorics.Permutation.Verkama62Count (sampleDouble)

abbrev signature : Signature where
  Params := ℕ
  State n := Equiv.Perm (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ π => Contains pattern π)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False)
  (fun e => nomatch e)

def sampleFresh : Fresh pattern {0,1,2,4} where
  a := 0
  b := 1
  c := 2
  d := 4
  ha := by decide
  hb := by decide
  hc := by decide
  hd := by decide
  hab := by decide
  hbc := by decide
  hcd := by decide
  hval₁ := by decide
  hval₂ := by decide
  hval₃ := by decide
  rightmost := by intro i hi; fin_cases i <;> simp_all
  topmost := by intro i hi; fin_cases i <;> norm_num [pattern] at *
  right := by intro i hi; fin_cases i <;> simp_all
  top := by intro i hi; fin_cases i <;> norm_num [pattern] at *

theorem id_avoids : ¬ Contains pattern (Equiv.refl (Fin 6)) := by
  rintro ⟨f,h⟩
  have hp : pattern 2 < pattern 0 := by decide
  have hf := f.strictMono (show (0 : Fin 6) < 2 by decide)
  have hv := (h 2 0).mp hp
  change f 2 < f 0 at hv
  omega

theorem observation_varies : ObservationalDependence signature actual := by
  intro i
  refine ⟨6, pattern, Equiv.refl _, ?_⟩
  intro h
  exact id_avoids (Eq.mp h (sampleFresh.toTerminal.forces sampleDouble))

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)},
    Terminal π S → Double π S → R.readout () n π
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 6 pattern {0,1,2,4} sampleFresh.toTerminal sampleDouble

def family : Registration arena (type_of% (@Terminal.forces)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Terminal.forces, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := observation_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@Terminal.forces) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.Terminal.forces.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Local.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ π => Contains pattern π) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Local
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Permutation.Verkama62Local
