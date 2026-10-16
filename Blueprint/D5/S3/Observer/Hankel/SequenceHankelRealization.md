# Minimal Linear Realization from Sequence Data

## Abstract

Finite-rank input-output data constructs its own reachable and observable minimal linear realization, with finite-window rank attainment and an undersized-compression witness.

## Application: phase-zero irrational rotation and exact linear dimension

Fix any irrational real alpha and phase zero. Let z(n) = exp(2 pi i (n alpha)), zeta = exp(2 pi i alpha), and y(n) = (Re z(n), Im z(n)) for every natural n. The complex and real statements concern this same sequence, with the real output retaining both coordinates in the stated order.

The exponential identity exp(n w) = exp(w)^n, with w = 2 pi i alpha, gives z(n) = zeta^n for every n after distributing the real-to-complex cast and commuting the scalar factors. Hence every Hankel entry is z(i+j) = zeta^i zeta^j = z(i) z(j). This is an identity at all indices, with z(0) = 1, not a numerical observation about a selected finite block.

To apply the sequence owner, take K = U = Y = C and m(n) = toSpanSingleton C C (z(n)), so m(n)u = u z(n). For every age j and scalar u the entire tail i -> m(i+j)u is (u zeta^j) times the function z. Conversely the age-zero, unit-input tail is z itself. Thus tailSpace(m) is exactly span_C{z}; z is nonzero because its value at zero is 1. This full residual space is finite-dimensional and has dimension 1. For a single action, words identify with their lengths and concatenation adds lengths, so this is the complete residual rank of Definition 5.1.

An explicit complex realization has state space C, initial state v0 = 1, total linear endomorphism A(v) = zeta v, and total readout C(v) = v. The multiplication-endomorphism power identity gives C(A^n v0) = z(n) for every n, and dim_C C = 1. Its input map is B = toSpanSingleton C C v0: B(u) = u v0. Input 1 represents the fixed initial state; it is not a time-dependent input or an external clock. Linearity gives C A^n B = m(n) as an equality of linear maps for every n.

The existing finite_tailSpace_of_realization supplies finite dimensionality from this actual model. The singleton-span equality supplies dimension 1. Applying realizationFromSequence_is_minimal then gives the canonical model on the complete tail space, its exact all-time behavior, and its attained minimum against every competing FiniteLinearRealization in that bundle. Applying dataHankel_rank_eq_tailSpace afterwards gives rank 1 for every finite block with at least one row and one column; this finite-block conclusion follows from the complete-sequence argument.

The lower bound also covers an arbitrary state universe independently of the concrete bundle. Let V be any finite-dimensional complex vector space, A any total linear endomorphism, v0 any initial state, and C any fixed total linear readout, with C(A^n v0) = z(n) at every n. At n = 0, C(v0) = 1, so v0 is nonzero and dim_C V is at least 1. Zero-dimensional competitors are included and ruled out by this argument. No reachability, observability, invertibility, positive-dimension or rank hypothesis is imposed.

For the real realization use the same carrier C as an R-vector space, with A(v) = zeta v, v0 = 1, and C = Complex.equivRealProdLm, the total real-linear map v -> (Re v, Im v). Its state dimension is 2 and its output is y(n) at every natural time. The sequence-owner parameter correspondence is K = U = R, Y = R x R and m(n)u = u y(n), with B = toSpanSingleton R C v0. In real coordinates this is the usual rotation, without restricting the state carrier to the unit circle.

To prove the real minimum, put theta = 2 pi alpha. If sin(theta) were zero, Real.sin_eq_zero_iff would give an integer k with k pi = theta = (2 alpha) pi. Cancelling the nonzero factor pi gives k = 2 alpha. But Irrational.natCast_mul at the nonzero natural 2 makes 2 alpha irrational, and Irrational.ne_int excludes this equality. Therefore sin(theta) is nonzero. The first two ordered outputs are y(0) = (1,0) and y(1) = (cos(theta),sin(theta)). They are linearly independent: a multiple a y(1) equal to y(0) would force a = 0 by the second coordinate and then 0 = 1 by the first.

Now let V be any finite-dimensional real vector space in an independent universe, with total linear A, initial v0 and a single fixed total linear readout C into R x R reproducing y at all times. Every y(n) lies in range(C), witnessed by A^n v0. In particular both independent outputs lie in that same subspace. Independence pulls back along its inclusion into R x R, giving 2 <= dim_R range(C) <= dim_R V. This excludes both zero- and one-dimensional states and, together with the actual two-dimensional realization, proves the attained minimum. There are no additional observability, reachability or invertibility assumptions.

These dimensions count linear coordinates, not distinguishable discrete states. Both exact carriers have infinitely many values. The separate finite-autonomous-state question fixes a finite nonempty S, a total time-independent update G, an initial s0, and an arbitrary complex-valued readout h; its all-time errors are |h(G^n(s0)) - z(n)|. The worst-error lower bound 1 and impossibility of a uniform error epsilon < 1 asserted in Theorem 9.2 are separate from this linear calculation. The simultaneous assertion in Proposition 9.6 requires that obstruction at this same alpha, phase zero and literal z. The linear argument alone supplies neither that discrete obstruction nor any permanent finite-precision error guarantee.

**Definition 1.1 (Output tail from data).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.dataTail`

*Formalization.* `D5/S3/Observer/Hankel/SequenceHankelRealization.dataTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an input direction u and age j, the i-th future coordinate is m(i+j)u. The data sequence is the only input to this definition.

**Definition 1.2 (Infinite data Hankel column space).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.tailSpace`

*Formalization.* `D5/S3/Observer/Hankel/SequenceHankelRealization.tailSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the linear span of all data tails in the full output-sequence space. Finite rank is expressed by FiniteDimensional on this carrier, since natural-valued finrank alone does not detect infinite dimension.

**Definition 1.3 (Shift on output sequences).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceShift`

*Formalization.* `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left shift advances a sequence by one coordinate. Its restriction is justified by a proved invariance argument on the data-tail generators.

**Definition 1.4 (A history direction as a state).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.tailState`

*Formalization.* `D5/S3/Observer/Hankel/SequenceHankelRealization.tailState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A single input direction at a specified age gives a canonical element of the data-tail span.

**Definition 1.5 (Dynamics constructed from data).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceDynamics`

*Formalization.* `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceDynamics` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict the left shift to the invariant data-tail span. The map is constructed here; it is not a field requiring a caller-supplied realization.

**Definition 1.6 (Canonical input map).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceInput`

*Formalization.* `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input map sends a direction to its unshifted output tail.

**Definition 1.7 (Canonical output map).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceOutput`

*Formalization.* `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate a canonical state at its present coordinate.

**Theorem 1.8 (Iterated dynamics advances coordinates).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceDynamics_pow_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceDynamics_pow_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The n-th iterate of the constructed dynamics sends coordinate i to coordinate i+n, for every state in the tail span.

**Theorem 1.9 (Input iterates are the data tails).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceDynamics_pow_input`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceDynamics_pow_input` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the constructed dynamics n times to an injected input produces precisely the data tail of age n.

**Theorem 1.10 (Every future output reads a coordinate).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceOutput_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceOutput_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Future output at time n equals coordinate n of the canonical state. This identity supplies the distinguishing observation in the compression theorem.

**Theorem 1.11 (All Markov parameters match the supplied data).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequence_markovParameter_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.sequence_markovParameter_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical realization reproduces every m(n), with no modal, eigenvalue, diagonalizability or stability hypothesis.

**Theorem 1.12 (Canonical reachability).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequence_reachable_eq_top`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.sequence_reachable_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input iterates span the entire constructed state space. This is proved by transporting the data-tail generators into the existing reachableSubspace owner.

**Theorem 1.13 (Canonical observability).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequence_eventualKernel_eq_bot`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.sequence_eventualKernel_eq_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A canonical state with zero output at every future time has all coordinates zero. The result uses the existing eventualKernel definition.

**Definition 1.14 (All-future observation of a competing model).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.futureOutput`

*Formalization.* `D5/S3/Observer/Hankel/SequenceHankelRealization.futureOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map a competing state to the sequence of outputs obtained under repeated application of its dynamics.

**Theorem 1.15 (Every realization contains the data-tail behavior).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.tailSpace_le_futureOutput_range`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.tailSpace_le_futureOutput_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any realization matching the complete data, every data tail is the future observation of a reachable state. Taking linear spans gives the range inclusion needed for the dimension lower bound.

**Theorem 1.16 (Finite models force finite data rank).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.finite_tailSpace_of_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.finite_tailSpace_of_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The range of a finite-dimensional state model is finite-dimensional. The proved inclusion therefore forces finite dimensionality of the full data-tail span.

**Theorem 1.17 (A universal linear-state dimension lower bound).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.tailSpace_finrank_le_stateDimension`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.tailSpace_finrank_le_stateDimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite-dimensional realization of the complete sequence has state dimension at least the data-tail dimension. This concerns linear state dimension, not general nonlinear memory or DFA state count.

**Definition 1.18 (A finite realization from finite-rank data).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.realizationFromSequence`

*Formalization.* `D5/S3/Observer/Hankel/SequenceHankelRealization.realizationFromSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under finite dimensionality of the data-tail span, package the constructed dynamics, input and output in the existing FiniteLinearRealization structure. No pre-existing system is assumed.

**Theorem 1.19 (Finite Hankel rank characterizes finite realizability).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.finite_tailSpace_iff_exists_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.finite_tailSpace_iff_exists_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The infinite block Hankel column span is finite-dimensional exactly when there is a finite linear realization of the complete sequence. This is an algebraic realization theorem, not an algorithm for noisy finite samples.

**Theorem 1.20 (The lower bound is attained).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.realizationFromSequence_is_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.realizationFromSequence_is_minimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named data-only construction matches the sequence and has exactly the data-tail dimension. Every competing finite realization has at least this dimension.

**Definition 1.21 (Finite block Hankel windows from data).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.dataHankel`

*Formalization.* `D5/S3/Observer/Hankel/SequenceHankelRealization.dataHankel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The block at row i and column j is m(i+j). This definition has no hidden dependence on a supplied state model.

**Theorem 1.22 (Finite windows attain the infinite data rank).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.dataHankel_rank_eq_tailSpace`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.dataHankel_rank_eq_tailSpace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When both horizons are at least the tail-space dimension, the finite data Hankel range has exactly that dimension. This theorem consumes the existing stable-Hankel theorem after establishing reachability and observability of the newly constructed model.

**Theorem 1.23 (A witness against undersized linear compression).**

Lean statement: `D5/S3/Observer/Hankel/SequenceHankelRealization.smaller_compression_has_future_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/SequenceHankelRealization.smaller_compression_has_future_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any linear compression to a strictly smaller finite-dimensional space kills some canonical state direction whose output is nonzero at a finite future time. States represent finite linear combinations of histories; no collision between two discrete input words is claimed.

## References

- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.dataHankel`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.dataHankel_rank_eq_tailSpace`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.dataTail`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.finite_tailSpace_iff_exists_realization`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.finite_tailSpace_of_realization`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.futureOutput`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.realizationFromSequence`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.realizationFromSequence_is_minimal`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceDynamics`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceDynamics_pow_apply`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceDynamics_pow_input`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceInput`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceOutput`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceOutput_pow`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequenceShift`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequence_eventualKernel_eq_bot`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequence_markovParameter_eq`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.sequence_reachable_eq_top`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.smaller_compression_has_future_witness`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.tailSpace`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.tailSpace_finrank_le_stateDimension`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.tailSpace_le_futureOutput_range`
- Truth anchor: `D5/S3/Observer/Hankel/SequenceHankelRealization.tailState`
- Dependency: [D5/S3/Observer/Hankel/HankelMinimalStateDimension](HankelMinimalStateDimension.md)
