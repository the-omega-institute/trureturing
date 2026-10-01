/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Pieces
   mirror-E: none(waiver:first-record-cut-and-replay)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Data.Vector.Basic]
   utility: none
   digest: Defines recursively ordered original-site pieces and their chronological replay. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Pure
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Vector.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Pieces

open WeakAscent215Pure

def PureHistory := {steps : List PureStep // ∃ ending, PureRun [] steps ending}

inductive OriginalPieces : ℕ → Type where
  | final {gap : ℕ} (history : PureHistory) : OriginalPieces gap
  | cut {gap : ℕ} (site : Fin gap) (history : PureHistory)
      (rest : OriginalPieces site.val) : OriginalPieces gap

def OriginalPieces.replay {gap : ℕ} (old : Bool) : OriginalPieces gap → List PureStep
  | .final history => history.val.map (PureStep.shift (gap + if old then 1 else 0))
  | .cut site history rest =>
      history.val.map (PureStep.shift (gap + if old then 1 else 0)) ++
        .descend site.val :: rest.replay false

def OriginalPieces.sites {gap : ℕ} : OriginalPieces gap → List (Fin gap)
  | .final _ => []
  | .cut site _ rest =>
      site :: rest.sites.map (Fin.castLE (Nat.le_of_lt site.is_lt))

def OriginalPieces.pieces {gap : ℕ} : OriginalPieces gap → List PureHistory
  | .final history => [history]
  | .cut _ history rest => history :: rest.pieces

end D5.S3.Combinatorics.WeakAscent.WeakAscent215Pieces
