# Signed boundaries of legal-word toggle graphs

## Abstract

At every length, the signed boundary of the actual legal-word graph has mass-zero image and gives the natural short exact sequence for singleton occupation.

Legal n consists of the existing Boolean words on Fin n satisfying Adm. The value at position j represents membership of j+1 in the independent support in positions 1 through n. legalWordGraph n is the existing induced hypercube: adjacency means exactly one differing coordinate. The edge space has one real coordinate for each actual unordered edge, and the vertex space has one real coordinate for each actual legal word.

Orientation G chooses an ordered pair of endpoints for each member of G.edgeSet, whose unordered pair is that same edge. No edge is doubled. edgeVector is the real cast of the existing signedIncidence column: the delta at the head minus the delta at the tail. vertexDelta v is Pi.single v 1. signedBoundary o sends a real edge coefficient function f to the sum of f e times edgeVector o e. Coefficients may have either sign; reference orientation places no restriction on an executable direction.

totalMass sums all vertex coordinates, and totalMassZero is its linear kernel. observation n sends a vertex function v to the coordinate whose value at i is the sum of v b over all actual words with b.val i=true. This is precisely singleton occupation of that same support carrier.

kernelBoundaryInclusion A o is the linear map from ker B to ker(A B) sending f to the identical edge function f. restrictedBoundary A o sends f in ker(A B) to B f in ker(A restricted to totalMassZero), retaining the mass-zero and observation-zero certificates. These definitions specify the maps in the sequence, rather than only asserting the existence of some isomorphic spaces.

**Theorem 1.1 (The image and the natural short exact sequence).**

$$\forall n \in \mathbb{N},\; \forall o \in \mathrm{Orientation}\left(\mathrm{legalWordGraph}\left(n\right)\right),\; \mathrm{range}\left(\mathrm{signedBoundary}\left(o\right)\right) = \mathrm{totalMassZero}\left(\mathrm{Legal}\left(n\right)\right) \land \left(\mathrm{Injective}\left(\mathrm{kernelBoundaryInclusion}\left(\mathrm{observation}\left(n\right), o\right)\right) \land \left(\mathrm{Exact}\left(\mathrm{kernelBoundaryInclusion}\left(\mathrm{observation}\left(n\right), o\right), \mathrm{restrictedBoundary}\left(\mathrm{observation}\left(n\right), o\right)\right) \land \mathrm{Surjective}\left(\mathrm{restrictedBoundary}\left(\mathrm{observation}\left(n\right), o\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/SignedBoundary.native_boundary_image_short_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every reference orientation o of legalWordGraph n, the image of signedBoundary o is totalMassZero. The stated kernel inclusion is injective, its image is the kernel of restrictedBoundary, and restrictedBoundary is surjective. Thus the zero spaces at the two ends complete a short exact sequence of real vector spaces. No connectivity, rank or image equality is assumed.

Delete an occupied coordinate using the existing legal-word deletion operation. Its existing adjacency and occupation identities show that this is an actual graph step and that occupation decreases by one. Strong induction therefore gives a path from every legal word to the empty word, proving connectivity of the native graph at every length.

For an adjacent pair, the chosen orientation agrees with the path direction or reverses it. Assigning coefficient 1 or -1 to that one unordered edge gives the desired endpoint delta difference. Induction on a walk telescopes these differences. Every mass-zero function x is the sum, over all vertices v, of x v times the delta at v minus the delta at a fixed root. Each difference is a boundary, and every boundary has mass zero; these two inclusions prove the image equality.

If a mass-zero vertex function has zero observation, lift it through the image equality to an edge function f. Then A B f=0, so the lift lies in the middle kernel. The restricted map has kernel exactly ker B, giving exactness. At n=0 there is one legal vertex and no edge; both the image and mass-zero space are zero and the same statement applies. This does not assert that A B vanishes on the whole edge space. Dimension and numerical count formulas are separate claims.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/SignedBoundary.native_boundary_image_short_exact`
- Dependency: [D5/S3/Combinatorics/Graph/LegalWords/EdgeCount](EdgeCount.md)
- Dependency: [D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity](../../../Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity.md)
