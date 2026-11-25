/- GID: D5/S0/History/SpliceEquations
   generality: G
   mirror-B: D5/B/S0/History/SpliceEquations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The defining recursion of marker-history splicing, with a two-marker witness. -/

module
prelude
public import OmegaMath.Data.SnocList.Append

namespace D5.S0.History

open Omega

/-- With histories read from the last inserted marker back to the first,
splicing places the second history before the first in the displayed word. -/
public theorem splice_recursion_equations {Marker : Type u} :
    And (∀ h : SnocList Marker, Eq (h.append .empty) h)
      (∀ (marker : Marker) (h g : SnocList Marker),
        Eq (h.append (g.pushBack marker)) ((h.append g).pushBack marker)) :=
  And.intro (fun _ => Eq.refl) (fun _ _ _ => Eq.refl)

/-- Reading the last inserted marker first puts `true` before `false`. -/
example :
    Eq (((SnocList.empty : SnocList Bool).pushBack .false).append
      ((SnocList.empty : SnocList Bool).pushBack .true))
      (((SnocList.empty : SnocList Bool).pushBack .false).pushBack .true) :=
  Eq.refl

end D5.S0.History
