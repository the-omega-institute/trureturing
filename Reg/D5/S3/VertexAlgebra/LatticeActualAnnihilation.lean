import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeActualAnnihilation
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeActualAnnihilation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.ActualSeriesDerivation

noncomputable section

namespace ExponentialSeries

abbrev signature : Signature where
  Params := Σ data : LatticeData, Derivation ℂ (Oscillator data) (Oscillator data)
  State parameter := {series : PowerSeries (Oscillator parameter.1) // PowerSeries.constantCoeff series = 0}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := PowerSeries (Oscillator parameter.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameter series => seriesDerivation parameter.1 parameter.2
    ((PowerSeries.exp (Oscillator parameter.1)).subst series.val)) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law observation := ∀ (data : LatticeData)
    (derivation : Derivation ℂ (Oscillator data) (Oscillator data))
    (series : PowerSeries (Oscillator data)) (zero : PowerSeries.constantCoeff series = 0),
    observation.readout () ⟨data, derivation⟩ ⟨series, zero⟩ =
      (PowerSeries.exp (Oscillator data)).subst series * seriesDerivation data derivation series

theorem actual_law : arena.Law actual := actual_exponential_derivation_series

end ExponentialSeries
end
end Reg.D5.S3.VertexAlgebra.LatticeActualAnnihilation
