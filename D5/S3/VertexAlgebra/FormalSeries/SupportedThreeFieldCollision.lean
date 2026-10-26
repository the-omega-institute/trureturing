/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native three-variable coefficient index. -/
import D5.S3.VertexAlgebra.FormalSeries.UngradedLocalWordSeries
/-! Three nonnegative degrees specify a native coefficient index. -/
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.SupportedThreeFieldCollision
noncomputable def index3 (x a b : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 x + Finsupp.single 1 a + Finsupp.single 2 b

end D5.S3.VertexAlgebra.SupportedThreeFieldCollision
