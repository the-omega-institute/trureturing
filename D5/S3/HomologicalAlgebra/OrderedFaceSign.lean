/- GID: D5/S3/HomologicalAlgebra/OrderedFaceSign
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/OrderedFaceSign
   mirror-E: none(waiver:definition-support)
   anchors: []
   utility: none
   digest: Integral orientation signs for ordered simplex incidences. -/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Int.Basic

@[expose] public section

set_option autoImplicit false

namespace D5.S3.HomologicalAlgebra.OrderedFaceSign

/-- The sign of an insertion or deletion at the position of a vertex in increasing order.
The count is the same on the source and target faces of the incidence. -/
def insertionSign {V : Type*} [LinearOrder V] (F : Finset V) (x : V) : ℤ :=
  (-1) ^ (F.filter (· < x)).card

end D5.S3.HomologicalAlgebra.OrderedFaceSign
