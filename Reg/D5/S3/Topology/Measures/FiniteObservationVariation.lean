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

/- The compact-family target has a different telescope from the finite-family
source above: A is arbitrary and a StrongDual norm-compact range premise is
present. A faithful dependent arena must retain all those dictionaries and
premises. A candidate role is the joint finite readout, with the existential
J remaining in the original conclusion, not chosen in advance or assumed
injective. Exact binding below is only a partial same-delivery attempt.
No law-equivalent realization, sourceSelection, whole-family intervention,
role sensitivity, or actual observational dependence is certified. -/
abbrev uniformScope := type_of%
  (@_root_.D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation.{u,v,w,z})

theorem uniform_source_proof : uniformScope.{u,v,w,z} :=
  @_root_.D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation.{u,v,w,z}

/- The new target(s) above have an unfinished four-slot audit tracked at
https://github.com/the-omega-institute/trureturing/issues/24319.
The older finite-family issue 24040 is not used to cover this extension. -/

end Reg.D5.S3.Topology.Measures.FiniteObservationVariation
