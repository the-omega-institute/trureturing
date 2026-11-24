/- GID: D5/S0/Computability/LayerShiftNaturality
   generality: G
   mirror-B: D5/B/S0/Computability/LayerShiftNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A layer-shift natural transformation commutes with every lifting morphism. -/

module
prelude
public import OmegaMath.CategoryTheory.Naturality

namespace D5.S0.Computability.LayerShiftNaturality

open Omega
open Omega.CategoryTheory

/-- A natural layer shift commutes with each lifting morphism. -/
public theorem layer_shift_naturality {Obj : Type u} {Arrow : Obj → Obj → Type v}
    (C : Category Obj Arrow) (_categoryLaws : C.Laws)
    {Current Shifted : Functor Arrow Arrow}
    (_currentLaws : Current.Laws C C) (_shiftedLaws : Shifted.Laws C C)
    (shift : Transformation Current Shifted) (natural : Transformation.IsNatural shift C)
    {X Y : Obj} (lift : Arrow X Y) :
    Eq (C.comp (Current.map lift) (shift Y)) (C.comp (shift X) (Shifted.map lift)) :=
  natural lift

end D5.S0.Computability.LayerShiftNaturality
