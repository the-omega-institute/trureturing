import Reg.D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockRegularChargedScalar

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.ChargedNormalJetRegistrationTransient

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

example : ¬ ObservationalDependence
    LatticeHalfFockFormalTwoSheetSubstitution.signature
    LatticeHalfFockFormalTwoSheetSubstitution.relationReadout := by
  intro dependence
  obtain ⟨parameter, first, second, distinct⟩ := dependence ()
  cases first
  cases second
  exact distinct rfl

example : ¬ ObservationalDependence
    LatticeHalfFockFormalTwoSheetSubstitution.signature
    LatticeHalfFockFormalTwoSheetSubstitution.rootReadout := by
  intro dependence
  obtain ⟨parameter, first, second, distinct⟩ := dependence ()
  cases first
  cases second
  exact distinct rfl

example : ¬ ObservationalDependence
    LatticeHalfFockFormalTwoSheetSubstitution.signature
    LatticeHalfFockFormalTwoSheetSubstitution.labelReadout := by
  intro dependence
  obtain ⟨parameter, first, second, distinct⟩ := dependence ()
  cases first
  cases second
  exact distinct rfl

example : ¬ ObservationalDependence
    LatticeHalfFockRegularChargedScalar.signature
    LatticeHalfFockRegularChargedScalar.scalarReadout := by
  intro dependence
  obtain ⟨parameter, first, second, distinct⟩ := dependence ()
  cases first
  cases second
  exact distinct rfl

example : ¬ ObservationalDependence
    LatticeHalfFockRegularChargedScalar.signature
    LatticeHalfFockRegularChargedScalar.ratioReadout := by
  intro dependence
  obtain ⟨parameter, first, second, distinct⟩ := dependence ()
  cases first
  cases second
  exact distinct rfl

end Reg.D5.S3.VertexAlgebra.ChargedNormalJetRegistrationTransient
