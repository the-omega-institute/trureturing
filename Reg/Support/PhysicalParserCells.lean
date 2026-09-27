import D5.S0.Computability.Coding.PhysicalSixParser
import Reg.Support.BoundedRunSpace

namespace Reg.Support.PhysicalParserCells

open _root_.D5.S0.Computability.Coding.PhysicalSixParser
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

/-- Observe the original Boolean tape cells, preserving control and head coordinates. -/
def observeCells (r : PrimitiveRealization (cutSignature Bool Bool))
    (c : Configuration) : Configuration :=
  { c with cell := fun t z => r.readout () (c.cell t z) }

/-- Erasure loses every true cell, including cells required by the source frame. -/
def erased : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun _ : Bool => false)

end Reg.Support.PhysicalParserCells
