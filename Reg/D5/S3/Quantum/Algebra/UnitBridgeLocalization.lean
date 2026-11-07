import D5.S3.Quantum.Algebra.UnitBridgeLocalization
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full-telescope source application for the original nonlinear localization.
This application supplies no whole-family intervention, sensitivity,
observational dependence or enrolled-template realization bridge. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Algebra.UnitBridgeLocalization

open _root_.D5.S3.Quantum.Algebra.UnitBridgeRawGeometry

abbrev localizationSourceScope : Prop := type_of% (@original_localization.{u})

theorem localization_source_application : localizationSourceScope.{u} :=
  @original_localization.{u}

end Reg.D5.S3.Quantum.Algebra.UnitBridgeLocalization
