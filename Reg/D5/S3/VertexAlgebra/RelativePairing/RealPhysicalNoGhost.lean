import D5.S3.VertexAlgebra.RelativePairing.RealPhysicalNoGhost
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.RelativePairing.RealPhysicalNoGhost

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
  _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
  _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
  _root_.D5.S3.VertexAlgebra.OriginalQPhysicalPairing
  _root_.D5.S3.VertexAlgebra.RelativePairing.RealPhysicalNoGhost

noncomputable section

structure Parameters where
  lattice : LatticeData
  matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftGram : matrix * gramComplex lattice = 1
  rightGram : gramComplex lattice * matrix = 1
  charge : Charge lattice
  level : ℤ
  critical : lattice.rank = 26
  shell : chosenH lattice charge + (level : ℂ) - 1 = 0
  chargeNonzero : charge ≠ 0
  lorentzian : _root_.D5.S3.QuadraticForms.ActualSignature.signature
    (gramReal lattice).toQuadraticForm' = (lattice.rank : ℤ) - 2

abbrev Image (parameter : Parameters) :=
  physicalImage parameter.lattice parameter.matrix parameter.charge parameter.level

def originalForm (parameter : Parameters) : Image parameter →ₗ⋆[ℂ] Image parameter →ₗ[ℂ] ℂ :=
  canonicalForm parameter.lattice parameter.matrix parameter.leftGram parameter.rightGram
    parameter.charge parameter.level parameter.critical parameter.shell parameter.chargeNonzero
    parameter.lorentzian

def noGhostLaw : Prop := ∀ parameter : Parameters,
  (∀ state : Image parameter, state ≠ 0 →
    0 < (-originalForm parameter state state).re ∧ (-originalForm parameter state state).im = 0) ∧
  (∀ state : Image parameter, (∀ other, originalForm parameter state other = 0) ↔ state = 0) ∧
  (∀ state : Image parameter, (∀ other, originalForm parameter other state = 0) ↔ state = 0)

theorem noGhost_sourceBridge : (type_of% (@canonicalForm_noGhost)) ↔ noGhostLaw := by
  constructor
  · intro source parameter
    exact source parameter.lattice parameter.matrix parameter.leftGram parameter.rightGram
      parameter.charge parameter.level parameter.critical parameter.shell parameter.chargeNonzero
      parameter.lorentzian
  · intro law lattice matrix leftGram rightGram charge level critical shell chargeNonzero lorentzian
    exact law ⟨lattice, matrix, leftGram, rightGram, charge, level, critical, shell,
      chargeNonzero, lorentzian⟩

def radicalsLaw : Prop := ∀ parameter : Parameters,
  LinearMap.ker (originalForm parameter) = ⊥ ∧
    (⨅ other : Image parameter, LinearMap.ker (originalForm parameter other)) = ⊥

theorem radicals_sourceBridge : (type_of% (@canonicalForm_radicals_bot)) ↔ radicalsLaw := by
  constructor
  · intro source parameter
    exact source parameter.lattice parameter.matrix parameter.leftGram parameter.rightGram
      parameter.charge parameter.level parameter.critical parameter.shell parameter.chargeNonzero
      parameter.lorentzian
  · intro law lattice matrix leftGram rightGram charge level critical shell chargeNonzero lorentzian
    exact law ⟨lattice, matrix, leftGram, rightGram, charge, level, critical, shell,
      chargeNonzero, lorentzian⟩

def frameIndependenceLaw : Prop := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (leftGram : matrix * gramComplex lattice = 1)
    (rightGram : gramComplex lattice * matrix = 1) (charge : Charge lattice) (level : ℤ)
    (critical : lattice.rank = 26) (shell : chosenH lattice charge + (level : ℂ) - 1 = 0)
    (firstFrame secondFrame : AdmissibleFrame lattice charge),
  frameForm lattice matrix leftGram rightGram charge level critical shell firstFrame =
    frameForm lattice matrix leftGram rightGram charge level critical shell secondFrame

theorem frameIndependence_sourceBridge :
    (type_of% (@imageForm_frame_independent)) ↔ frameIndependenceLaw := Iff.rfl

abbrev NoGhostTarget := type_of% (@canonicalForm_noGhost)
abbrev RadicalsTarget := type_of% (@canonicalForm_radicals_bot)
abbrev FrameIndependenceTarget := type_of% (@imageForm_frame_independent)
abbrev RecoveryTarget := type_of% (@canonicalForm_recovery)
abbrev ProjectionTarget := type_of% (@canonicalForm_projection)
abbrev IntrinsicTarget := type_of% (@original_imageForm_noGhost)

#print axioms noGhost_sourceBridge
#print axioms radicals_sourceBridge
#print axioms frameIndependence_sourceBridge

end
end Reg.D5.S3.VertexAlgebra.RelativePairing.RealPhysicalNoGhost
