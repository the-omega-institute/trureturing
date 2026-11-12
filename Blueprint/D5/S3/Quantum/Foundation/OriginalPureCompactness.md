# Compactness of the original pure locus

## Abstract

The entire extreme-point locus of the original normalized cone base is compact under complete exclusion balls and weak orthogonal-pair properness.

**Theorem 1.1 (Original pure-point compactness).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\operatorname{weakPair}\left(C, u\right) \Rightarrow \operatorname{IsCompact}\left(\operatorname{pure}\left(C, u\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalPureCompactness.whole_pure_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a nonzero finite dimensional real normed vector space, C a closed generating pointed cone, and u a real linear functional strictly positive on every nonzero point of C. The normalized base K is the entire intersection of C with u=1. Its pure locus P consists of all extreme points. Effects range over every original linear functional between zero and u on all of C. Each complete original exclusion fibre is a nondegenerate affine Euclidean ball, and every original orthogonal pure pair generates a proper face. Then P is compact in V. No closedness or finiteness of P is assumed.

The full effect interval is closed. Choose a finite basis from the spanning original pure locus. Every proper effect has values between zero and one on this basis, so the basis operator-norm estimate bounds the entire interval. Finite dimensionality makes that closed bounded interval compact.

Joint completion makes the map sending a pure point to its entire exclusion ball injective: complete one point to a joint triple; the other two points have a singleton common exclusion. Two exclusion balls containing two different states are equal, since their intersection is a nonpoint face of each strictly convex ball.

Suppose an original effect a confirms x and vanishes at y and z, while another original effect distinguishes y and z. The face where a=1 contains x. If this face were a nonpoint ball, take two antipodal extreme points s and t in it. The same a would put both y and z into both complete exclusion balls D_s and D_t. These balls must coincide, and injectivity forces s=t, contradicting their antipodality. The confirming face is therefore a pure singleton, and x is pure.

Consider all triples x,y,z in K and all pairs of original effects a,b satisfying a(x)=1, a(y)=a(z)=0, b(y)=1 and b(z)=0. This is a closed subset of a compact product. Its projection onto x is contained in P by the preceding argument. Conversely every original pure point has such a configuration by joint completion and the common confirming effects of complete exclusion balls. Thus this projection equals the entire P and is compact.

This supplies closedness of the original pure locus for limits of complete exclusion balls. It does not itself establish uniform semiaxis bounds, continuity of the complete balls, or local triviality of their direction spaces.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalPureCompactness.whole_pure_compact`
- Dependency: [D5/S3/Quantum/Foundation/OrthogonalJointCompletion](OrthogonalJointCompletion.md)
