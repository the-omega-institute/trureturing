import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.L1WeakExtraction

/-!
Exact original source telescopes for Hilbert weak extraction. These bindings
retain arbitrary universes and all original typeclass dictionaries. They are
partial audit evidence: no four-slot registration is asserted. A source-family
realization, lawful readout, whole-family variation, sensitivity, observational
dependence and source-coordinate reconstruction remain to be supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.L1WeakExtraction

abbrev commonScope.{u} := type_of%
  (@_root_.D5.S3.Topology.Measures.L1WeakExtraction.exists_common_weak_subsequence.{u})

abbrev approximationScope.{u, v} := type_of%
  (@_root_.D5.S3.Topology.Measures.L1WeakExtraction.exists_weak_subsequence_of_hilbert_approximation.{u, v})

theorem common_actual.{u} : commonScope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1WeakExtraction.exists_common_weak_subsequence.{u}

theorem approximation_actual.{u, v} : approximationScope.{u, v} :=
  @_root_.D5.S3.Topology.Measures.L1WeakExtraction.exists_weak_subsequence_of_hilbert_approximation.{u, v}

end Reg.D5.S3.Topology.Measures.L1WeakExtraction
