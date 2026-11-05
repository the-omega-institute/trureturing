import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.FiniteObservationVariation

/-!
The original theorem's complete telescope and proof are retained for source
reconstruction. Four-slot registration is incomplete. A dependent source arena
must retain the topology and measurable dictionaries, all four universes, the
dependent sensor family and its point-separation premise, the signed family
and both Jordan regularity premises, and the positive accuracy. Its selected
observation is the finite joint readout inside each signed pushforward; the
finite budget is existentially bound in the conclusion.

An enrolled readout with exact sourceSelection and a realization equivalence
has not been established. Whole-family law violation, sensitivity with the
other operands fixed, and actual observational dependence remain unproved.
Neither a constant observation nor an assumed injective finite readout supplies
these obligations. No Contract.Registration or declared_validated claim is made.
The unfinished audit is tracked at
https://github.com/the-omega-institute/trureturing/issues/24040.
-/

namespace Reg.D5.S3.Topology.Measures.FiniteObservationVariation

universe u v w z

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Topology.Measures.FiniteObservationVariation.exists_common_finite_readout_variation.{u,v,w,z})

theorem source_proof : sourceScope.{u,v,w,z} :=
  @_root_.D5.S3.Topology.Measures.FiniteObservationVariation.exists_common_finite_readout_variation.{u,v,w,z}

end Reg.D5.S3.Topology.Measures.FiniteObservationVariation
