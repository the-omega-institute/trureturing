import Lean
import LeanInformationAudit.Census.Certificate
import Mathlib.Data.Finset.Card

namespace LeanInformationAudit

open Lean

instance : ToExpr CensusKeyManifest where
  toTypeExpr := mkConst ``CensusKeyManifest
  toExpr value := mkApp4 (mkConst ``CensusKeyManifest.mk) (toExpr value.headSha)
    (toExpr value.reportSha256) (toExpr value.censusRoot) (toExpr value.keys)

/-- This adapter stays outside the Init-only final environment. It claims an id
set equality, not the inventory's Name-level `ExactlyCovers` (elaborator-bound). -/
theorem ids_toFinset_eq_of_eq {ids reportIds : List Nat} (h : ids = reportIds) :
    ids.toFinset = reportIds.toFinset := congrArg List.toFinset h

def CensusKeyManifest.IdCoverage (ids : List Nat) (requested : Nat)
    (reportIds : Finset Nat) : Prop :=
  ids.Nodup ∧ ids.length = requested ∧ ids.toFinset = reportIds

theorem CensusKeyManifest.idCoverage_of_certificate (ids : List Nat)
    (requested : Nat) (reportIds : List Nat)
    (h : CensusKeyManifest.Certificate ids requested reportIds) :
    CensusKeyManifest.IdCoverage ids requested reportIds.toFinset :=
  ⟨strictlyAscending_nodup _ h.1, h.2.1, ids_toFinset_eq_of_eq h.2.2⟩

end LeanInformationAudit
