import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.NormPreservingLifts

/-!
# Exact original all-lifts source scope

The raw theorem includes arbitrary carrier and index universes, compact
Hausdorff Borel K, Hausdorff Borel L, every filter (including bottom), actual
signed measures, equal variation masses, clopen concentration, and eventual
fibre constancy separately for each locally constant test. No restriction to
finite carriers, Dirac measures, nonempty spaces or a nontrivial filter is made.

This source binds the exact actual-positive theorem. It is partial audit
evidence, not a four-slot Contract.Registration. The dependent source arena,
source reconstruction and realization equivalence, lawful enrolled readout,
whole-family variation and sensitivity, and actual observational dependence
have not been supplied. The missing registration is disclosed in the linked
issue named in the delivery; successful theorem binding does not discharge it.
-/

namespace Reg.D5.S3.Topology.Measures.NormPreservingLifts

universe u v w

open _root_.D5.S3.Topology.Measures.NormPreservingLifts

abbrev arbitraryLiftsScope := type_of% (@arbitrary_lifts_tendsto.{u,v,w})

theorem arbitrary_lifts_actual : arbitraryLiftsScope.{u,v,w} :=
  @arbitrary_lifts_tendsto.{u,v,w}

end Reg.D5.S3.Topology.Measures.NormPreservingLifts
