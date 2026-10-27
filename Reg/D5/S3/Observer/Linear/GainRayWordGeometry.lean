import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.GainRayWordGeometry
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Linear.GainRayWordGeometry
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
open scoped Matrix Classical

abbrev signature : Signature where
  Params := List Bool
  State _ := Mat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ w L => (Finset.univ.filter (fun i : Fin (w.length+1) =>
    ∃ c : ℝ, acquisition (w.take i.val) = c • L)).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ w _ => w.length+1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (w : List Bool) (m : ℕ) (_hlen : w.length = 2*m) (_hM : false ∈ w)
    (L : Mat), R.readout () w L ≤ m

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h [false,false] 1 rfl (by simp) 0
  norm_num [rejected,realize] at hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cumulative_proportionality_card_even,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    classical
    intro i
    refine ⟨[], (0 : Mat), (1 : Mat), ?_⟩
    have he : acquisition [] = (1 : Mat) := by
      simpa using acquisition_pure false 0
    change (Finset.univ.filter (fun j : Fin 1 =>
      ∃ c : ℝ, acquisition ([].take j.val) = c • (0 : Mat))).card ≠
      (Finset.univ.filter (fun j : Fin 1 =>
      ∃ c : ℝ, acquisition ([].take j.val) = c • (1 : Mat))).card
    simp [he, show ∃ c : ℝ, (1 : Mat) = c • (1 : Mat) from ⟨1,by simp⟩]

def entry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@cumulative_proportionality_card_even)
    (type_of% (realize signature (fun _ w L => (Finset.univ.filter
      (fun i : Fin (w.length+1) => ∃ c : ℝ, acquisition (w.take i.val) = c • L)).card)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.evenUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ w L => (Finset.univ.filter
    (fun i : Fin (w.length+1) => ∃ c : ℝ, acquisition (w.take i.val) = c • L)).card)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Linear.GainRayWordGeometry, definition := none, coordinates := #[0], readouts := #[{ path := #["body","body","body","body","body","fn","arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Observer.Linear.GainRayWordGeometry
