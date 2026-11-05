import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Polygons.PolygonEarSlide

/-!
The complete source telescope for the actual ear-slide equivalence is retained
here as an audit witness. A faithful four-slot registration is not asserted:
the theorem ranges over a dependent family of ZMod-indexed Finset fibres and
its source descriptor has no enrolled arena/readout/variation/sensitivity
certificate for that telescope.
-/
namespace Reg.D5.S3.Geometry.Polygons.PolygonEarSlide

abbrev condition_fibre_equiv_at_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.condition_fibre_equiv_at)

def condition_fibre_equiv_at_source : condition_fibre_equiv_at_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual.condition_fibre_equiv_at

end Reg.D5.S3.Geometry.Polygons.PolygonEarSlide
