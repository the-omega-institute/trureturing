import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords

/-! Exact source reconstruction and dependent-family interventions for the
membership-word length and original-host periodic-word bridge. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords

open _root_.D5.S3.Combinatorics.Graph.MutualVisibility
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiLanguage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev visibilityScope := type_of% (@visible_iff_word_periodic_avoidance)
abbrev lengthScope := type_of% (@membership_word_length)

abbrev visibilitySignature : Signature where
  Params := ℕ
  State m := Finset (Vertex m)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def visibilityActual : Realization visibilitySignature :=
  realize visibilitySignature (fun i m X => by
    classical
    exact if i then decide (PeriodicAvoidance (membershipWord m X))
      else decide (Visible (host m) X)) (fun e => nomatch e)

abbrev visibilityArena : Arena where
  signature := visibilitySignature
  Law r := ∀ m, 1 ≤ m → ∀ X,
    (r.readout false m X = true ↔ r.readout true m X = true)

theorem visibility_source_bridge : visibilityScope ↔ visibilityArena.Law visibilityActual := by
  simp [visibilityScope, visibilityActual, realize]

theorem visibility_actual_positive : visibilityArena.Law visibilityActual :=
  visibility_source_bridge.mp visible_iff_word_periodic_avoidance

private theorem visibility_empty (i : Bool) :
    visibilityActual.readout i 1 ∅ = true := by
  have hp : PeriodicAvoidance (membershipWord 1 ∅) :=
    (visible_iff_word_periodic_avoidance 1 (by omega) ∅).mp (visible_empty _)
  cases i <;> simp [visibilityActual, realize, hp, visible_empty]

private theorem visibility_full (i : Bool) :
    visibilityActual.readout i 1 Finset.univ = false := by
  have ho : Obstruction 1 Finset.univ :=
    ⟨0,1,by omega,by omega,by simp,by simp,by simp⟩
  have hv : ¬ Visible (host 1) Finset.univ := by
    intro h
    exact (visible_iff_no_obstruction 1 Finset.univ).mp h ho
  have hp : ¬ PeriodicAvoidance (membershipWord 1 Finset.univ) := by
    intro h
    exact hv ((visible_iff_word_periodic_avoidance 1 (by omega) Finset.univ).mpr h)
  cases i <;> simp [visibilityActual, realize, hp, hv]

def visibilityRejected (i : Bool) : Realization visibilitySignature :=
  realize visibilitySignature (fun j m X =>
    if j = i then false else visibilityActual.readout j m X) (fun e => nomatch e)

private theorem visibility_rejected_law (i : Bool) :
    ¬ visibilityArena.Law (visibilityRejected i) := by
  intro h
  have he := h 1 (Nat.le_refl 1) ∅
  cases i <;> simp [visibilityRejected, realize] at he <;>
    rw [visibility_empty] at he <;> contradiction

def visibilityFamily : Registration visibilityArena visibilityScope where
  actual := visibilityActual
  bridge := visibility_source_bridge
  variation := ⟨visibility_actual_positive, visibilityRejected false, visibility_rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨visibilityRejected i, ?_, rfl, visibility_rejected_law i⟩
      intro j hji
      funext m X
      simp [visibilityRejected, realize, hji]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1, ∅, Finset.univ, ?_⟩
    rw [visibility_empty, visibility_full]
    intro he
    cases he

abbrev lengthSignature : Signature where
  Params := Unit
  State _ := Σ m : ℕ, Finset (Vertex m)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def lengthActual : Realization lengthSignature :=
  realize lengthSignature (fun i _ s =>
    if i then 3*s.1+2 else (membershipWord s.1 s.2).length) (fun e => nomatch e)

abbrev lengthArena : Arena where
  signature := lengthSignature
  Law r := ∀ m X, r.readout false () ⟨m,X⟩ = r.readout true () ⟨m,X⟩

theorem length_source_bridge : lengthScope ↔ lengthArena.Law lengthActual := by
  simp [lengthScope, lengthActual, realize]

theorem length_actual_positive : lengthArena.Law lengthActual :=
  length_source_bridge.mp membership_word_length

def lengthRejected (i : Bool) : Realization lengthSignature :=
  realize lengthSignature (fun j p s =>
    if j = i then lengthActual.readout j p s + 1 else lengthActual.readout j p s)
    (fun e => nomatch e)

private theorem length_rejected_law (i : Bool) : ¬ lengthArena.Law (lengthRejected i) := by
  intro h
  have he := h 0 ∅
  cases i <;> norm_num [lengthRejected, lengthActual, realize, membership_word_length] at he

def lengthFamily : Registration lengthArena lengthScope where
  actual := lengthActual
  bridge := length_source_bridge
  variation := ⟨length_actual_positive, lengthRejected false, length_rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lengthRejected i, ?_, rfl, length_rejected_law i⟩
      intro j hji
      funext p s
      simp [lengthRejected, realize, hji]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), ⟨0,∅⟩, ⟨1,∅⟩, ?_⟩
    cases i <;> norm_num [lengthActual, realize, membership_word_length]

noncomputable def registration_visibility :
    Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0} (@visible_iff_word_periodic_avoidance)
      (type_of% (realize visibilitySignature (fun i m X => by
        classical
        exact if i then decide (PeriodicAvoidance (membershipWord m X))
          else decide (Visible (host m) X)) (fun e => nomatch e)))
      (Type → Type) Unit where
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords.visible_iff_word_periodic_avoidance
    "Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords/visibilityArena/[anonymous]")
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords.visibilityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨visibilityArena⟩
  objectArena := .source ⟨visibilityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source visibilityArena ⟨visibilityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize visibilitySignature (fun i m X => by
    classical
    exact if i then decide (PeriodicAvoidance (membershipWord m X))
      else decide (Visible (host m) X)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Finset
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def registration_length :
    Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0} (@membership_word_length)
      (type_of% (realize lengthSignature (fun i _ s =>
        if i then 3*s.1+2 else (membershipWord s.1 s.2).length) (fun e => nomatch e)))
      (Type → Type) Unit where
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords.membership_word_length
    "Reg.D5.S3.Combinatorics/Graph/MutualVisibility/AndrasfaiWords/lengthArena/[anonymous]")
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords.lengthFamily
  realizationSource := none
  generated := false
  arena := .source ⟨lengthArena⟩
  objectArena := .source ⟨lengthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lengthArena ⟨lengthFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lengthSignature (fun i _ s =>
    if i then 3*s.1+2 else (membershipWord s.1 s.2).length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Finset
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev countZeroScope := type_of% (@count_zero)

abbrev countZeroSignature : Signature where
  Params := Unit
  State _ := Unit
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def countZeroActual : Realization countZeroSignature :=
  realize countZeroSignature (fun i _ _ => if i then 4 else count 0) (fun e => nomatch e)

abbrev countZeroArena : Arena where
  signature := countZeroSignature
  Law r := r.readout false () () = r.readout true () ()

theorem count_zero_source_bridge : countZeroScope ↔ countZeroArena.Law countZeroActual := by
  simp [countZeroScope, countZeroActual, realize]

theorem count_zero_actual_positive : countZeroArena.Law countZeroActual :=
  count_zero_source_bridge.mp count_zero

/-- A closed numeric source has no state-dependent readout in this exact arena. -/
def countZeroCertificate : Option (Registration countZeroArena countZeroScope) := none

end
end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords
