# Sharp whole-source native law

## Abstract

Exact static and complete names-only online minima for the fixed native two-channel source.

**Theorem 1.1 (Both attained minima and all closed thresholds).**

$$\forall h, epsilon: \mathbb{R}, \forall C, E: \operatorname{Vector}, ((0 < h) \land (0 < epsilon)) \Rightarrow (\operatorname{LeastCost}\left(\operatorname{StaticCost}\left(h, epsilon, C, E\right), \operatorname{quantum}\left(h, epsilon\right)^{2}\right)) \land ((\operatorname{LeastCost}\left(\operatorname{OnlineCost}\left(h, epsilon, C, E\right), \operatorname{quantum}\left(h, epsilon\right)^{2}\right)) \land ((\operatorname{Feasible}\left(h, epsilon, C, E, \operatorname{const}\left(\operatorname{History}, ()\right)\right) \iff 2 epsilon < h) \land (\forall k: \mathbb{N}, k h \le 2 epsilon \Rightarrow 2 epsilon < (k + 1) h \Rightarrow \operatorname{quantum}\left(h, epsilon\right) = k + 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/TypedCocycleSharpNative.whole_sharp_native_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For h>0, epsilon>0 and fixed C,E, quantum is floor(2epsilon/h)+1. LeastCost means an attained cost together with a lower bound for every feasible competing cost. Feasible requires one decoder returning the entire original ordered word for every point of the full closed coordinate box, from exactly its endpoint, final supplement and joint vector. Negative observations near the empty word are retained. Neither definition mentions quantum or the asserted optimum.

Static labels are arbitrary functions on the infinite whole legal-history domain with finite actual range, without prefix compatibility. Online registers have a single initialization and a total update on names alone. Their cost is the complete actual reached range over all legal histories at p,s,t together. The reached range is never assumed closed under source-illegal names. Every persistent variable belongs to the charged state.

The lower bound uses actual s histories with counts m=k+2i-j and n=k+j-i, for 0<=i,j<=k. Their native coordinates are C+h(2k+i,3k+j). A single observation C+h(2k+k/2,3k+k/2) belongs to all their original closed boxes whenever hk<=2epsilon. Decoder correctness injects this square into any actual label range. Every online register induces such a static label. Appending e translates the square by E at t.

For attainment, the entire state is (x,y) in (Z/qZ)^2, initialized at (0,0). The single a update is (x+1,y), c is (0,x), and e is the identity. The register values are (m,0) at p and (n,m) at s,t. Every pair is reached at s with nonnegative representatives, so the complete range has q squared states. Equal endpoint and equal residues, together with a common allowed observation, force both integer native coordinates equal; the inverse integer matrix then forces both original counts equal.

The decoder is a mathematical factorization of compatible explanations through the permitted final input. Mathlib Function.factorsThrough_iff supplies this factorization after uniqueness is proved. Mathlib modular equality, integer divisibility bounds, and finite-cardinality injections supply the generic algebra and counting. This is not an effective representation claim for unspecified real constants.

Both exact minima equal q squared for every positive h,epsilon. The constant-label contract holds exactly when h>2epsilon. For every k>=0 with kh<=2epsilon<(k+1)h, quantum=k+1, hence both minima are (k+1) squared. The left endpoint is closed, including positive equality thresholds; k=0 retains epsilon>0 and q=1. All original empty, zero-lap, intermediate and terminal uses share this same update and decoder.

The parameterized result concerns the fixed native instrument A=h(1,1), B=h(1,2), without retuning edge vectors. C,E may be arbitrary real offsets in the theorem, which includes the source positive case. It asserts no result for other source propositions, other native matrices, scalar acquisition, physical instruments, finite clock range or total chronological storage.

## References

- Truth anchor: `D5/S3/Observer/Completion/TypedCocycleSharpNative.whole_sharp_native_law`
- Dependency: [D5/S3/Observer/Completion/TypedCocycleSource](TypedCocycleSource.md)
