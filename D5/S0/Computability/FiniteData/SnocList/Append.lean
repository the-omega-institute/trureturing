/- GID: D5/S0/Computability/FiniteData/SnocList/Append
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Concatenation of lists built by successive appends. -/

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import D5.S0.Computability.FiniteData.SnocList

/-!
Omega original.

Concatenation of lists built by successive appends.
-/

noncomputable section

@[expose] public section

namespace Omega.SnocList

/-- Append the elements of the second list in their insertion order. -/
def append {A : Type u} (first : SnocList A) : SnocList A → SnocList A :=
  SnocList.rec (motive := fun _ => SnocList A) first
    (fun _ last earlier => earlier.pushBack (last True.intro))

end Omega.SnocList
