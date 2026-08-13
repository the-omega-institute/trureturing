/- GID: D5/S0/Naming/CoordinateDependence
   generality: G
   mirror-B: D5/B/S0/Naming/CoordinateDependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dependency coordinates admit separating pairs with distinct invariant values. -/

import Mathlib.Data.Set.Basic

namespace D5.S0.Naming.CoordinateDependence

/-- The coordinates at which some separating pair has distinct invariant values. -/
def dependencySet {Coordinate : Type*} {System : Type*} {Value : Type*}
    (separatesAt : Coordinate -> System -> System -> Prop)
    (invariant : System -> Value) : Set Coordinate :=
  {coordinate | exists left right,
    separatesAt coordinate left right /\ invariant left ≠ invariant right}

/-- A witnessed separating pair can make a coordinate dependent. -/
example :
    0 ∈ dependencySet
      (fun (coordinate : Nat) (left right : Bool) =>
        coordinate = 0 /\ left = false /\ right = true)
      id := by
  exact ⟨false, true, ⟨rfl, rfl, rfl⟩, by decide⟩

/-- A constant invariant has no dependent coordinates, even when every pair separates. -/
example :
    dependencySet
      (fun (_ : Unit) (_ _ : Bool) => True)
      (fun _ : Bool => 0) = ∅ := by
  ext coordinate
  simp [dependencySet]

end D5.S0.Naming.CoordinateDependence
