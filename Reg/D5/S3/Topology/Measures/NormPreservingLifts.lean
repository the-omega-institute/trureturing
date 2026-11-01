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

/-- Exact scopes for the finite positive-difference integration suppliers.
These source bindings supply no four-slot realization or sensitivity evidence. -/
theorem difference_integral_actual :
    type_of% (@signedFunctional_sub_toSignedMeasure.{u}) :=
  @signedFunctional_sub_toSignedMeasure.{u}

theorem difference_variation_actual :
    type_of% (@totalVariation_sub_toSignedMeasure_le.{u}) :=
  @totalVariation_sub_toSignedMeasure_le.{u}

/- Same-delivery partial source binding for the moved continuous pushforward
supplier. A faithful role selects actual p and g pullback evaluation across
arbitrary compact Borel carriers, including empty carriers. Replacing it by a
constant equality or a finite nonempty carrier specialization would lose the
source telescope. Realization equivalence, exact sourceSelection and global
intervention/sensitivity/dependence are not established. -/
theorem functional_map_actual : type_of% (@functional_map.{u,v}) :=
  @functional_map.{u,v}

/- The new target(s) above have an unfinished four-slot audit tracked at
https://github.com/the-omega-institute/trureturing/issues/24319.
The older finite-family issue 24040 is not used to cover this extension. -/

end Reg.D5.S3.Topology.Measures.NormPreservingLifts
