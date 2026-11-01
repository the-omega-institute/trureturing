import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPathNSSP
import Reg.Support.DependentFamily

/-! Full-family source-bound attempt for even looped path nSSP. -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPathNSSP

open _root_.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
open _root_.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPathNSSP (result)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := Finset (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Set (Matrix (Fin n) (Fin n) ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ L => {A | ∀ i j, A i j ≠ 0 ↔ pathPattern L i j})
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 0 < n → Even n → ∀ L : Finset (Fin n), L.Nonempty →
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A ∈ R.readout () n L ∧ HasNSSP A

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hbad, _⟩ := h 2 (by decide) (by decide) {0} (by simp)
  exact hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨A, hs, _⟩ := result 2 (by decide) (by decide) {0} (by simp)
  have hnot : ¬ (∀ i j, A i j ≠ 0 ↔ pathPattern ({1} : Finset (Fin 2)) i j) := by
    intro h
    have hn : A 0 0 ≠ 0 := (hs 0 0).mpr (by simp [pathPattern])
    have H := (h 0 0).mp hn
    norm_num [pathPattern] at H
  refine ⟨2, {0}, {1}, ?_⟩
  change {A : Matrix (Fin 2) (Fin 2) ℝ | ∀ i j, A i j ≠ 0 ↔ pathPattern {0} i j} ≠
    {A : Matrix (Fin 2) (Fin 2) ℝ | ∀ i j, A i j ≠ 0 ↔ pathPattern {1} i j}
  intro heq
  have hm := congrArg (fun S : Set (Matrix (Fin 2) (Fin 2) ℝ) => A ∈ S) heq
  exact hnot (hm.mp hs)

def source_registration : Registration arena
    _root_.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPathNSSP.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPathNSSP.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPathNSSP.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ L => {A | ∀ i j, A i j ≠ 0 ↔ pathPattern L i j}) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPathNSSP
