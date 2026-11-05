# The Positive Flip-Average Trace

## Abstract

The Positive Flip-Average Trace

**Theorem 1.1 (The Positive Flip-Average Trace).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FlipAverage.actual_flip_average_trace`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FlipAverage.actual_flip_average_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be the representation on the exact ActualGround selected by actual_twisted_ground_representation for integral symmetric even lattice data with integer unit determinant. Let A be the finite average on complex bilinear forms and let F exchange the two arguments. The trace of F composed with A is one, in every rank including zero.

For an endomorphism T, the operator B(u,v) to B(Tv,Tu) has trace tr(T squared). In the elementary bilinear basis its diagonal coefficients are T(i,j) times T(j,i); their double sum is the trace of the square. Applied to the contragredient action, this turns the flip-average trace into the average of the ground character at squared inverse group elements.

Inversion permutes the finite group. The square of a reduced extension element with charge a is the central element with sign modTwoCocycle(a,a). Its character is complexSign of this sign times the dimension of ActualGround. The positive quadratic Gauss sum evaluates the charge sum. The two central signs, the quotient order and the selected-rank equation give trace one.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FlipAverage.actual_flip_average_trace`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/GaussElimination](GaussElimination.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/InvariantPairing](InvariantPairing.md)
