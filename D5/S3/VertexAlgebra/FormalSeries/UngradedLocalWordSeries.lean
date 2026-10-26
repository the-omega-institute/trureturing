/- GID: D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed coefficient indices and zero extension of formal series. -/
import D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
import Mathlib.RingTheory.MvPowerSeries.Basic
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.UngradedLocalWordSeries
open UniformGradedLocalCorrelator
noncomputable section
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
def signedIndex (e : Exponent N) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i).toNat)

def signedExtend (P : MvPowerSeries (Fin N) V) (e : Exponent N) : V :=
  if ∀ i, 0 ≤ e i then P (signedIndex e) else 0

end
end D5.S3.VertexAlgebra.UngradedLocalWordSeries
