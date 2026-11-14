import D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact source-type mirrors preserve the original theorem telescopes. A mirror
is compiled audit evidence, not a four-slot registration or a binding verdict. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource

abbrev sourceScope_auxiliary_coefficient := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.auxiliary_coefficient.{u})
theorem source_actual_auxiliary_coefficient : sourceScope_auxiliary_coefficient.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.auxiliary_coefficient.{u}

abbrev sourceScope_affineMoment_coefficient := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.affineMoment_coefficient.{u})
theorem source_actual_affineMoment_coefficient : sourceScope_affineMoment_coefficient.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.affineMoment_coefficient.{u}

abbrev sourceScope_auxiliary_sum := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.auxiliary_sum.{u})
theorem source_actual_auxiliary_sum : sourceScope_auxiliary_sum.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.auxiliary_sum.{u}

abbrev sourceScope_affineMoment_zero := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.affineMoment_zero.{u})
theorem source_actual_affineMoment_zero : sourceScope_affineMoment_zero.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.affineMoment_zero.{u}

abbrev sourceScope_affineMoment_step := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.affineMoment_step.{u})
theorem source_actual_affineMoment_step : sourceScope_affineMoment_step.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.affineMoment_step.{u}

abbrev sourceScope_chargedCorr_linearForms := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.chargedCorr_linearForms.{u})
theorem source_actual_chargedCorr_linearForms : sourceScope_chargedCorr_linearForms.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.chargedCorr_linearForms.{u}

abbrev sourceScope_jet_mixed := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.jet_mixed)
theorem source_actual_jet_mixed : sourceScope_jet_mixed :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.jet_mixed

abbrev sourceScope_wick_flat_cons := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.wick_flat_cons)
theorem source_actual_wick_flat_cons : sourceScope_wick_flat_cons :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource.wick_flat_cons

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
