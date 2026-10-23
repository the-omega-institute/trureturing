import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Selection.CompactZeroDimensional

/-!
# Exact original selection scopes

The full carrier universes, topology instances, open-hit condition and empty
carrier cases are preserved. A source-bound dependent-family observation for
continuous fiber membership must retain the function B → K and all its
fiberwise tests. For the prescribed theorem it must additionally retain the
chosen base and target points and the equality at that base point.

The bindings below establish the actual-positive statements. They are partial
audit evidence, not four-slot registrations. The realization bridge, lawful
readout binding, whole-family variation and sensitivity, and observational
dependence remain unspecified. In particular a fixed empty base has only the
empty function, so nonconstant observation cannot be asserted in every fiber.
-/

namespace Reg.D5.S3.Topology.Selection.CompactZeroDimensional

universe u v

open _root_.D5.S3.Topology.Selection.CompactZeroDimensional

abbrev selectionScope := type_of%
  (@exists_continuous_selection.{u,v})

theorem selection_actual : selectionScope.{u,v} :=
  @exists_continuous_selection.{u,v}

abbrev prescribedSelectionScope := type_of%
  (@exists_continuous_selection_through.{u,v})

theorem prescribed_selection_actual : prescribedSelectionScope.{u,v} :=
  @exists_continuous_selection_through.{u,v}

end Reg.D5.S3.Topology.Selection.CompactZeroDimensional
