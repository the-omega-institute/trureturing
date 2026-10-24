# The actual law excludes supported positive rectangular words

## Abstract

The actual law excludes supported positive rectangular words

**Definition 1.1 (The original word product).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.product`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.product` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite stationary binary presentation theta and binary list w, product(theta,w) is the ordered product of the original matrices associated with the letters of w. The empty product is the identity matrix.

**Definition 1.2 (A finite original-clock word cylinder).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.block`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an integer starting time t and a binary list w, block(t,w) fixes z(t+k) to the kth bit of w for every natural k strictly below the length of w.

**Theorem 1.3 (List and finite-coordinate products coincide).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.product_word`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.product_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every presentation theta and binary list w, the ordered list product equals wordMatrix(theta.matrix,length(w),w.get) on the same original hidden state type.

**Theorem 1.4 (Concatenation splits the actual cylinder).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.block_append`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.block_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer t and binary lists u and v, block(t,u appended to v) is exactly the intersection of block(t,u) and block(t+length(u),v). The identity includes empty words.

**Theorem 1.5 (All original word entries are nonnegative).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.product_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.product_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every stationary nonnegative binary presentation theta, every binary list w and every original state pair i,j, product(theta,w)(i,j) is nonnegative. Structural zeros and zero-length products are retained.

**Theorem 1.6 (General same-law supported-word exclusion).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.supported_word_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.supported_word_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every stationary finite marked presentation, suppose every legal output cylinder is positive and the native complete-exterior posterior is the actual bit almost surely. Every positive word product has no nonempty exact positive rectangular support. The no11 condition of Presentation makes every positive word legal. Protected words w0x0w for both x are legal and positive; arbitrary nonnegative farther messages give a uniform two-sided posterior interval on the positive guard. Native finite exterior conditional expectations converge to the complete exterior on this same law, contradicting the binary full posterior. Zero-total atoms require no normalization, and the matrix support need not have rank one.

**Theorem 1.7 (The complete-law positive trimming boundary).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_trimmed_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_trimmed_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every stationary finite presentation θ of the actual P, positive-mass trimming has complete visible law equal to θ and every trimmed word product excludes nonempty exact positive rectangular support. The original same-law trimming cylinder identity and complete bilateral cylinder uniqueness identify the canonical trimmed law. Strict positivity of every retained initial mass makes a rectangular product a positive-probability word. The empty word, structural zeros and original zero-mass states stay within the stated scope.

**Theorem 1.8 (Every irreducible same-law presentation is excluded).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_irreducible_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_irreducible_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite stationary marked presentation of the original twelve-state visible law, assume that each ordered hidden-state pair has a strictly positive transition-power entry at some natural time. Then no original word matrix at any length has nonempty exact positive rectangular support. Stationarity and this reachability first imply strictly positive stationary mass at every state, so any such word would have positive occurrence probability and contradict actual_every_presentation. No aperiodicity or rank-one hypothesis is used.

**Definition 1.9 (The protected exterior event).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.guard`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.guard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

guard(w) fixes the finite word w followed by zero on coordinates -(length(w)+1) through -1, and zero followed by w on coordinates one through length(w)+1. The missing center is unconstrained.

**Theorem 1.10 (Every presentation of the same output law is excluded).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_every_presentation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_every_presentation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite hidden type with measurable singletons, every stationary marked presentation theta with visibleLaw(theta) equal to the original twelve-state visible law, every length n and every Boolean word w of strictly positive actual occurrence probability, its original word matrix cannot have nonempty exact positive rectangular support. All included entries are positive, all other entries are zero; rank is unrestricted. The proof expresses actual finite exterior atoms as original matrix products, decomposes every farther completion into nonnegative actual row and column messages, and applies one uniform epsilon to both protected center masses. Both protected words are legal and have positive actual mass. Zero-total atoms are never normalized. The native finite conditional distribution equals the actual cell ratio; the increasing exterior filtration and same-law full-erasure theorem give the contradiction on the positive guard event. Equality of the entire visible measures, rather than separate-radius identities, transports this argument to every presentation. Unsupported ghost words are outside this conclusion.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_every_presentation`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_irreducible_obstruction`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.actual_trimmed_obstruction`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.block`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.block_append`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.guard`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.product`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.product_nonneg`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.product_word`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw.supported_word_obstruction`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ErasedExteriorFiltration](ErasedExteriorFiltration.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages](PositiveRectangleMessages.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure](TwelveStateFullErasure.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateGhost](TwelveStateGhost.md)
