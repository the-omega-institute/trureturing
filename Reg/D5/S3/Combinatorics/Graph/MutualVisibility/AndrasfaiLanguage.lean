import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiLanguage

/-! Exact source telescopes and dependent readout bridges. No four-slot
validation is claimed by the optional certificates below. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiLanguage

open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiLanguage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev languageScope := type_of% (@accepts_iff_avoids)
abbrev uniqueScope := type_of% (@closed_run_unique)
abbrev existenceScope := type_of% (@exists_unique_closed_run)

abbrev languageSignature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 5
  Anchor := Empty
  finiteAnchor := inferInstance

def languageActual : Realization languageSignature :=
  realize languageSignature (fun _ _ w => machine.eval w) (fun e => nomatch e)

abbrev languageArena : Arena where
  signature := languageSignature
  Law r := ∀ w, r.readout () () w ≠ 4 ↔ ¬ ContainsForbidden w

theorem language_source_bridge : languageScope ↔ languageArena.Law languageActual := by
  rfl

theorem language_actual_positive : languageArena.Law languageActual :=
  language_source_bridge.mp accepts_iff_avoids

abbrev runSignature : Signature where
  Params := List Bool
  State _ := Fin 5
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 5
  Anchor := Empty
  finiteAnchor := inferInstance

def runActual : Realization runSignature :=
  realize runSignature (fun _ w q => machine.evalFrom q w) (fun e => nomatch e)

abbrev uniqueArena : Arena where
  signature := runSignature
  Law r := ∀ w, w.length % 3 ≠ 0 → ∀ q t : Fin 5, q ≠ 4 → t ≠ 4 →
    r.readout () w q = q → r.readout () w t = t → q=t

abbrev existenceArena : Arena where
  signature := runSignature
  Law r := ∀ w, w.length % 3 ≠ 0 →
    (PeriodicAvoidance w ↔ ∃! q : Fin 5, q ≠ 4 ∧ r.readout () w q = q)

theorem unique_source_bridge : uniqueScope ↔ uniqueArena.Law runActual := Iff.rfl

theorem existence_source_bridge : existenceScope ↔ existenceArena.Law runActual := Iff.rfl

theorem unique_actual_positive : uniqueArena.Law runActual :=
  unique_source_bridge.mp closed_run_unique

theorem existence_actual_positive : existenceArena.Law runActual :=
  existence_source_bridge.mp exists_unique_closed_run

/-- The exact bridges do not supply intervention or compiled source-selection evidence. -/
def languageCertificate : Option (Registration languageArena languageScope) := none

def uniqueCertificate : Option (Registration uniqueArena uniqueScope) := none

def existenceCertificate : Option (Registration existenceArena existenceScope) := none

end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiLanguage
