/- GID: D5/S0/Computability/LayerShiftNaturality
   generality: G
   mirror-B: D5/B/S0/Computability/LayerShiftNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A layer-shift natural transformation commutes with every lifting morphism. -/

import Mathlib.CategoryTheory.NatTrans

/- Provenance: thin honest wrapper over pinned Mathlib's naturality square
   (`CategoryTheory.NatTrans.naturality`). -/

namespace D5.S0.Computability.LayerShiftNaturality

open CategoryTheory

universe u v

/-- A layer shift represented by a natural transformation is compatible with
every lifting morphism: shifting after the current-layer action equals acting
at the shifted layer after shifting the source. -/
theorem layer_shift_naturality {C : Type u} [Category.{v} C]
    {Current Shifted : C ⥤ C} (shift : NatTrans Current Shifted)
    {X Y : C} (lift : X ⟶ Y) :
    Current.map lift ≫ shift.app Y = shift.app X ≫ Shifted.map lift :=
  shift.naturality lift

end D5.S0.Computability.LayerShiftNaturality
