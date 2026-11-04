import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

/- Exact original dependent telescopes; these source mirrors are not four-slot registrations.
The dependent-family realization, its source-equivalence bridge, whole-family variation,
role sensitivity, observational dependence and source selection remain unproved.
Open audit: https://github.com/the-omega-institute/trureturing/issues/22144 -/
abbrev sourceScope_self_products :=
  type_of% (@_root_.D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector.self_products)

theorem source_actual_self_products : sourceScope_self_products :=
  @_root_.D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector.self_products

abbrev sourceScope_virasoro_commutator :=
  type_of% (@_root_.D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector.virasoro_commutator)

theorem source_actual_virasoro_commutator : sourceScope_virasoro_commutator :=
  @_root_.D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector.virasoro_commutator

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
