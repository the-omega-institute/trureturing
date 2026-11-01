import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S1.Words.AdmissibleWords.AdmissibleCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.AdmissibleWords.AdmissibleCount.Adjacency

open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := Reg.Support.SingleDependentReadout.signature Nat
  (fun n => Fin n → Bool) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ n word => decide (Adm n word)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ (n : Nat) (b : Fin n → Bool),
    F.readout () n b = true ↔
      ∀ i j : Fin n, i.val + 1 = j.val → b i = false ∨ b j = false

theorem positive : arena.Law actual := by
  intro n b
  simpa [actual, realize] using (adm_iff_no_adjacent_true n b)

theorem bridge : (type_of% (@adm_iff_no_adjacent_true)) ↔ arena.Law actual := by
  constructor
  · intro h n b
    simpa [actual, realize] using h n b
  · intro h n b
    simpa [actual, realize] using h n b

theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := (law 0 (fun i => Fin.elim0 i)).mpr (by
    intro i
    exact Fin.elim0 i)
  change false = true at h
  cases h

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, ![false, false], ![true, true], ?_⟩
  change decide (Adm 2 ![false, false]) ≠ decide (Adm 2 ![true, true])
  decide

def evidence : Registration arena (type_of% (@adm_iff_no_adjacent_true)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ negative
  dependence := dependence

end Reg.D5.S1.Words.AdmissibleWords.AdmissibleCount.Adjacency

namespace Reg.D5.S1.Words.AdmissibleWords.AdmissibleCount.Adjacency

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@adm_iff_no_adjacent_true) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.AdmissibleCount.adm_iff_no_adjacent_true.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.AdmissibleCount.Adjacency.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.AdmissibleCount
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.AdmissibleWords.AdmissibleCount.Adjacency
