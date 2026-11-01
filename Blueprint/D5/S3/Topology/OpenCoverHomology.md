# Positive singular homology from open covers

## Abstract

Reduced Mayer–Vietoris gives actual positive-degree open-cover splittings.

**Definition 1.1 (The actual Mayer–Vietoris inclusion is an isomorphism).**

Lean statement: `D5/S3/Topology/OpenCoverHomology.inclusionIso`

*Formalization.* `D5/S3/Topology/OpenCoverHomology.inclusionIso` (`✓ std3`).

*Citation.* Allen Hatcher (2002). *Algebraic Topology*. URL: <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>.

*Commentary.*

Let C be an abelian category with the required coproducts and R a coefficient object. For two open subsets U,V covering a TopCat space X, if their intersection is empty or contractible, the actual Mayer–Vietoris map from H_q(U;R) biproduct H_q(V;R) to H_q(X;R) is invertible for every q>0. Exactness at the biproduct gives injectivity and exactness at X gives surjectivity. The connecting map factors through reduced H_(q-1) of the intersection. In degree one this is reduced H_0; ordinary H_0 of a nonempty contractible intersection is not asserted to vanish. The proof directly uses TopCat.mayerVietoris_exact₂, TopCat.mayerVietoris_exact₃, TopCat.reducedMayerVietorisδ_comp_ι and the TauCeti reduced-homology vanishing and successor comparison. This is the classical open Mayer–Vietoris argument from Hatcher, Chapter 2, implemented using the existing TauCeti source port.

**Definition 1.2 (Additivity for a binary topological sum).**

Lean statement: `D5/S3/Topology/OpenCoverHomology.sumIso`

*Formalization.* `D5/S3/Topology/OpenCoverHomology.sumIso` (`✓ std3`).

*Citation.* Allen Hatcher (2002). *Algebraic Topology*. URL: <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>.

*Commentary.*

For arbitrary topological spaces X,Y and q>0, their actual singular homology biproduct maps isomorphically to H_q(X sum Y;R). The summand ranges are disjoint open subsets covering the sum; their subspaces are identified by actual homeomorphisms. The empty intersection uses the empty-space branch of inclusionIso. This is not an assumed chain-level coproduct comparison.

## References

- Truth anchor: `D5/S3/Topology/OpenCoverHomology.inclusionIso`
- Truth anchor: `D5/S3/Topology/OpenCoverHomology.sumIso`
