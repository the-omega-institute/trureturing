# Uniform noncollapse of entire original exclusion balls

## Abstract

All original pure labels and all whole three-ball exclusion charts share one positive lower bound on every linear direction.

Let V be a nonzero finite dimensional real normed space, C a closed pointed generating convex cone, and u a real-linear functional strictly positive on every nonzero cone vector. K is the entire base cut out by u equal to one. P consists of all extreme points of K. The effects are the entire interval from zero to u on the original cone. At each p in P the entire original exclusion has an injective affine parametrization by the closed Euclidean three-ball, and its width over all original effects equals one.

**Theorem 1.1 (all_label_uniform_noncollapse).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionUniformNoncollapse.all_label_uniform_noncollapse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionUniformNoncollapse.all_label_uniform_noncollapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one positive constant eta such that eta times the norm of v is at most the norm of the linear image of v, for every original pure label, every entire three-ball chart of its exclusion, and every Euclidean vector v. The constant controls all charts simultaneously; no continuous chart selection is required.

Full width makes every original pure label saturated. Compactness of the saturated label set therefore gives closedness of P. Compactness of K bounds all chart centers and linear operator norms. Compactness of the complete effect interval bounds the norms of all effects. An attained unit oscillation then supplies a positive lower bound on the chart operator norm.

Consider the closed bounded family of all affine ball maps with image in K, sphere image in P, and operator norm at least this fixed positive bound. Suppose a member has a nonzero kernel vector. Adding a scalar multiple of that vector does not change its linear image. The norm along that line is continuous and becomes at least one, so the intermediate value theorem pads every point of the closed ball to the unit sphere with the same image. Hence the entire affine ball lies in P. Its center is an extreme point, and the midpoint of every pair of opposite images forces both images to equal the center. The linear map must vanish, contradicting its positive operator norm.

Every map in this compact family is thus injective. Evaluation of its linear part on the compact unit sphere has a positive attained minimum. Rescaling an arbitrary vector gives the asserted lower bound. This argument does not use Pair, weakPair, a Jordan product, a common physical inner product, regular labels, or an assumed closed pure locus.

The scalar cone gives a distinct boundary case. On the real line with the nonnegative cone and the identity unit, the entire normalized base and its pure locus are both the singleton containing one. Every effect confirming that label reads one at the only normalized state, so the original exclusion is empty. It cannot be the affine image of a nonempty closed three-ball. The cone assumptions alone therefore do not imply the ball premise.

For the native complex model take V to be the entire Hermitian three-by-three carrier, C the full positive semidefinite cone and u the trace. The positive and negative parts generate the real carrier, and strict trace positivity holds on every nonzero positive element. The whole rank-one-generated cone theorem and the full pure-carrier theorem identify every original pure label with a normalized rank-one projector. Extend its unit vector to a complex orthonormal basis. The other two basis vectors give orthogonal native pure states in the entire support exclusion. Pairing against the first of these rank-one projectors is an original legal effect: positivity gives its lower bound, and the trace-product inequality gives its upper bound by the original trace. It reads one and zero on the two chosen states. Their oscillation forces width one at every original pure label. HermitianExclusionBall.all_pure_charts supplies the whole charts. SectionROGFrame.whole_pure_carrier and rog_frame give the pure carrier and orthonormal basis, and HermitianExclusionKernel.exclusion_iff_kernel identifies the original full-effect exclusion with the support face. These results give all premises of the uniform theorem on the full original model, with no assumed all-label width or ball premise. This is an occurrence of the theorem in a specified mathematical cone, not an identification of an arbitrary cone with that model. The uniform lower-bound clause is the result proved here. Continuity of the entire exclusion family, continuous range and shape data, a rank-three vector bundle, and a linear identification of the entire original cone with the full complex three-by-three positive semidefinite cone are separate conclusions.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionUniformNoncollapse.all_label_uniform_noncollapse`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionWidthCompactness](ExclusionWidthCompactness.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalFacePolarity](OriginalFacePolarity.md)
- Dependency: [D5/S3/Quantum/Matrix/NumericalRange](../Matrix/NumericalRange.md)
