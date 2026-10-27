import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.L1UniformIntegrableWeak

/-!
Exact original source telescope for finite-measure L1 weak extraction. Zero
measure, arbitrary sigma algebras and the full continuous dual are retained.
This is partial source-binding evidence, not a validated four-slot audit.
Source-family realization, readout, variation, sensitivity, observational
dependence and raw source-coordinate reconstruction remain open.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.L1UniformIntegrableWeak

abbrev weakScope.{u} := type_of%
  (@_root_.D5.S3.Topology.Measures.L1UniformIntegrableWeak.exists_weak_subsequence.{u})

theorem weak_actual.{u} : weakScope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1UniformIntegrableWeak.exists_weak_subsequence.{u}

end Reg.D5.S3.Topology.Measures.L1UniformIntegrableWeak
