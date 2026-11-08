# Original smooth domain and closable smeared fields

## Abstract

The common dense invariant smooth domain and opposite-charge formal pairing.

smoothFamilies is the submodule of families x(k) in H_k satisfying inclusion(j,k)x(k)=x(j) for every j<=k. Smooth is this compatible-family space. Evaluation at k=0 is injective by injectivity of the Sobolev inclusions. smoothDomain is its range as an actual submodule of the original Hilbert completion H_0, and domainEquiv identifies compatible families with that range. The family of embeddings of every original finite carrier vector is compatible. Thus smoothDomain contains the dense finite carrier and is dense in H_0.

smearFamily(a,f) sends x to the family whose k-th component is smear(a,f,k)x(order(a)+k). The proved compatibility of the bounded smear maps makes this another compatible family. field(a,f) is the resulting Hilbert-valued partial linear map with domain exactly smoothDomain. This constructs invariance of the common H_infinity domain; it imposes no finite energy support on the image.

eta(a)=paritySign(chargeEnergy(D,a)) is proved equal to epsilon(D,a,-a). opposite(a,f) is eta(a) times field(-a,conjugate(f)), on the same explicit domain. The original mode identity first extends to the Sobolev completions by density in both variables. Absolute convergence then passes the pairing through the two-sided sums, reindexing m to -m and using coefficient_conjugate. With the inner product conjugate linear in the first slot, the phase remains in the second slot: inner(field(a,f)u,v)=inner(u,eta(a)*field(-a,conjugate(f))v).

This identity establishes field_formal. Density gives the inclusion of field(a,f) into the adjoint of opposite(a,f). Mathlib's closedness of that adjoint supplies a closed extension and proves field_closable. OriginalSmearingCore consumes these private results for minimal-closure and core statements; OriginalSmoothFields uses the same formal pairing, density and field construction. No equality with a maximal adjoint, essential self-adjointness, strong commutation or strong locality is asserted. These consumed support components have no separate theorem Describes. Original source-pairing attributions and Mathlib's partial-operator and adjoint attribution remain with their suppliers.

## References

- Dependency: [D5/S3/VertexAlgebra/Analysis/OriginalInfiniteSmearing](OriginalInfiniteSmearing.md)
