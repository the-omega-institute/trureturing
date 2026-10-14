import D5.S3.VertexAlgebra.RelativePairing.NativePhysicalNoGhost
import Reg.D5.S3.VertexAlgebra.RelativePairing.OriginalPhysicalDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace Reg.D5.S3.VertexAlgebra.RelativePairing.NativePhysicalNoGhost

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
  _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
  _root_.D5.S3.VertexAlgebra.OriginalQPhysicalPairing
  _root_.D5.S3.VertexAlgebra.OriginalQEnergyInclusionPairing
  _root_.D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization
  _root_.D5.S3.VertexAlgebra.RelativePairing.NativePhysicalNoGhost
  _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockForm
  _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric

noncomputable section

structure ProjectionParameters extends OriginalPhysicalDescent.Parameters where
  realRows : ∀ row column, star (frame row column) = frame row column

structure Parameters extends ProjectionParameters where
  lorentzian : _root_.D5.S3.QuadraticForms.ActualSignature.signature
    (gramReal lattice).toQuadraticForm' = (lattice.rank : ℤ) - 2

abbrev Image (parameter : ProjectionParameters) :=
  physicalImage parameter.lattice parameter.matrix parameter.charge parameter.level

def originalForm (parameter : ProjectionParameters) :
    Image parameter →ₗ⋆[ℂ] Image parameter →ₗ[ℂ] ℂ :=
  imageForm parameter.lattice parameter.matrix parameter.charge parameter.level
    parameter.frame parameter.inverse parameter.leftGram parameter.rightGram
    parameter.leftFrame parameter.rightFrame parameter.direction parameter.xAxis parameter.yAxis
    parameter.critical parameter.null parameter.nonzero parameter.distinct
    parameter.xRow parameter.yRow parameter.xDual parameter.yDual parameter.shell

def originalExtraction (parameter : ProjectionParameters) :
    Image parameter →ₗ[ℂ]
      TransverseDownIndex parameter.lattice parameter.xAxis parameter.yAxis parameter.level →₀ ℂ :=
  imageProjection parameter.lattice parameter.matrix parameter.frame parameter.inverse
    parameter.leftGram parameter.rightGram parameter.leftFrame parameter.rightFrame
    parameter.charge parameter.direction parameter.xAxis parameter.yAxis parameter.level
    parameter.critical parameter.null parameter.nonzero parameter.distinct
    parameter.xRow parameter.yRow parameter.xDual parameter.yDual parameter.shell

def projectionLaw : Prop := ∀ (parameter : ProjectionParameters) (first second : Image parameter),
  originalForm parameter first second = -fockForm parameter.lattice
    (transverseDownOscillator parameter.lattice parameter.frame parameter.xAxis parameter.yAxis
      parameter.level (originalExtraction parameter first))
    (transverseDownOscillator parameter.lattice parameter.frame parameter.xAxis parameter.yAxis
      parameter.level (originalExtraction parameter second))

theorem projectionSourceBridge : (type_of% (@imageForm_projection)) ↔ projectionLaw := by
  constructor
  · intro source parameter first second
    exact source parameter.lattice parameter.matrix parameter.frame parameter.inverse
      parameter.leftGram parameter.rightGram parameter.leftFrame parameter.rightFrame
      parameter.charge parameter.direction parameter.xAxis parameter.yAxis parameter.level
      parameter.critical parameter.null parameter.nonzero parameter.distinct
      parameter.xRow parameter.yRow parameter.xDual parameter.yDual parameter.shell
      parameter.realRows first second
  · intro law lattice matrix frame inverse leftGram rightGram leftFrame rightFrame
      charge direction xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell
      realRows first second
    exact law ⟨⟨lattice, matrix, frame, inverse, leftGram, rightGram, leftFrame, rightFrame,
      charge, direction, xAxis, yAxis, level, critical, null, nonzero, distinct,
      xRow, yRow, xDual, yDual, shell⟩, realRows⟩ first second

def noGhostLaw : Prop := ∀ parameter : Parameters,
  (∀ state : Image parameter.toProjectionParameters, state ≠ 0 →
    0 < (-originalForm parameter.toProjectionParameters state state).re ∧
      (-originalForm parameter.toProjectionParameters state state).im = 0) ∧
  (∀ state : Image parameter.toProjectionParameters,
    (∀ other, originalForm parameter.toProjectionParameters state other = 0) ↔ state = 0) ∧
  (∀ state : Image parameter.toProjectionParameters,
    (∀ other, originalForm parameter.toProjectionParameters other state = 0) ↔ state = 0)

theorem noGhostSourceBridge : (type_of% (@imageForm_noGhost)) ↔ noGhostLaw := by
  constructor
  · intro source parameter
    exact source parameter.lattice parameter.matrix parameter.frame parameter.inverse
      parameter.leftGram parameter.rightGram parameter.leftFrame parameter.rightFrame
      parameter.charge parameter.direction parameter.xAxis parameter.yAxis parameter.level
      parameter.critical parameter.null parameter.nonzero parameter.distinct
      parameter.xRow parameter.yRow parameter.xDual parameter.yDual parameter.shell
      parameter.realRows parameter.lorentzian
  · intro law lattice matrix frame inverse leftGram rightGram leftFrame rightFrame
      charge direction xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell
      realRows lorentzian
    exact law ⟨⟨⟨lattice, matrix, frame, inverse, leftGram, rightGram, leftFrame, rightFrame,
      charge, direction, xAxis, yAxis, level, critical, null, nonzero, distinct,
      xRow, yRow, xDual, yDual, shell⟩, realRows⟩, lorentzian⟩

abbrev ProjectionTarget := type_of% (@imageForm_projection)
abbrev NoGhostTarget := type_of% (@imageForm_noGhost)

end
end Reg.D5.S3.VertexAlgebra.RelativePairing.NativePhysicalNoGhost
