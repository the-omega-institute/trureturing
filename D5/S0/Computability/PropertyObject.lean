/- GID: D5/S0/Computability/PropertyObject
   generality: G
   mirror-B: D5/B/S0/Computability/PropertyObject
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Property objects are losslessly equivalent to their seven typed components. -/

import Mathlib.Logic.Equiv.Prod

namespace D5.S0.Computability.PropertyObject

/-- A property internalized as its generation history, encoding, finite reading,
ledger, self-code, dynamic update, and certificate. -/
structure InternalProperty
    (History Encoding Reading Ledger SelfCode Update Certificate : Type*) where
  history : History
  encoding : Encoding
  reading : Reading
  ledger : Ledger
  selfCode : SelfCode
  update : Update
  certificate : Certificate

/-- The nested product of all components of an internal property object. -/
abbrev PropertyComponents
    (History Encoding Reading Ledger SelfCode Update Certificate : Type*) :=
  History × Encoding × Reading × Ledger × SelfCode × Update × Certificate

/-- Forget the field names without losing any component. -/
def propertyObjectEquivComponents
    (History Encoding Reading Ledger SelfCode Update Certificate : Type*) :
    InternalProperty History Encoding Reading Ledger SelfCode Update Certificate ≃
      PropertyComponents History Encoding Reading Ledger SelfCode Update Certificate where
  toFun object :=
    (object.history, object.encoding, object.reading, object.ledger,
      object.selfCode, object.update, object.certificate)
  invFun components :=
    { history := components.1
      encoding := components.2.1
      reading := components.2.2.1
      ledger := components.2.2.2.1
      selfCode := components.2.2.2.2.1
      update := components.2.2.2.2.2.1
      certificate := components.2.2.2.2.2.2 }
  left_inv object := by cases object; rfl
  right_inv components := by
    rcases components with ⟨history, encoding, reading, ledger, selfCode, update, certificate⟩
    rfl

/-- The seven-component representation of an internal property object is lossless. -/
theorem property_object_components_bijective
    (History Encoding Reading Ledger SelfCode Update Certificate : Type*) :
    Function.Bijective
      (propertyObjectEquivComponents
        History Encoding Reading Ledger SelfCode Update Certificate) :=
  (propertyObjectEquivComponents
    History Encoding Reading Ledger SelfCode Update Certificate).bijective

end D5.S0.Computability.PropertyObject
