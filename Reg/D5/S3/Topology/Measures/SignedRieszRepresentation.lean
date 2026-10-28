import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.SignedRieszRepresentation

/-!
# Original signed representation source scope

The source scope retains arbitrary compact Hausdorff Borel carriers and all
real continuous linear functionals, including empty carriers and zero norm.
The represented object is an actual signed measure and regularity is asserted
of its actual total variation. This binding is partial audit evidence.

A faithful dependent-family audit needs the original carrier/dictionary
parameters, an arena whose states retain the signed measures and arbitrary dual inputs,
and observations of their integration functionals and variation masses.
The exact source includes regular-signed uniqueness, the norm identity for
every regular signed measure, and arbitrary-dual representation. A compiled source reconstruction
and sourceSelection, the lawful enrolled readout and realization bridge,
whole-family variation/sensitivity and actual observational dependence remain
absent. No four-slot Contract.Registration or declared_validated status is
asserted. Unknown continuation supplies none of these missing proofs.
-/

namespace Reg.D5.S3.Topology.Measures.SignedRieszRepresentation

open _root_.D5.S3.Topology.Measures.SignedRieszRepresentation

universe u

abbrev representationScope := type_of% (@signed_riesz_markov_kakutani.{u})

theorem representation_actual : representationScope.{u} :=
  @signed_riesz_markov_kakutani.{u}

end Reg.D5.S3.Topology.Measures.SignedRieszRepresentation
