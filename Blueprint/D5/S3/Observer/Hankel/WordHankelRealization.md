# Word Hankel Rank and Full-Block Recovery

## Abstract

Complete word residuals give minimal matrix realizations and exact recovery under a global rank hypothesis.

**Definition 1.1 (Residual after a prefix).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.residual`

*Formalization.* `D5/S3/Observer/Hankel/WordHankelRealization.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a response f on all finite words, residual f u is the function v ↦ f(u ++ v). Concatenation reads the prefix before the suffix.

**Definition 1.2 (Complete residual space).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.residualSpace`

*Formalization.* `D5/S3/Observer/Hankel/WordHankelRealization.residualSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the linear span of every word residual in the entire function space. FiniteDimensional is a separate hypothesis; natural-valued finrank is never used to test finite dimensionality.

**Definition 1.3 (Invariant letter update).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.canonicalShift`

*Formalization.* `D5/S3/Observer/Hankel/WordHankelRealization.canonicalShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ambient map sends g(v) to g(a :: v). On generators it sends f_u to f_(u ++ [a]). Restrict its domain to the residual space before restricting the codomain. The fold identity is proved for every initial residual-space state and every suffix.

**Definition 1.4 (Ordered word product).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.wordProduct`

*Formalization.* `D5/S3/Observer/Hankel/WordHankelRealization.wordProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty product is the identity. A leading letter contributes its matrix on the left, so the product is A_a1 ... A_at in input order. Letters need not commute.

**Definition 1.5 (Row-coordinate realization).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.MatrixRealization`

*Formalization.* `D5/S3/Observer/Hankel/WordHankelRealization.MatrixRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A dimension-d realization consists of alpha, one d-by-d matrix for each letter, beta, and equality f(w) = alpha A_w beta for every word. Fin d permits d = 0. No positivity, characteristic-zero or nonempty-alphabet assumption is imposed.

**Definition 1.6 (Canonical realization at residual rank).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.canonicalMatrixRealization`

*Formalization.* `D5/S3/Observer/Hankel/WordHankelRealization.canonicalMatrixRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose the finite basis supplied by Mathlib on the full residual carrier. Transpose toMatrix to obtain row-coordinate letter matrices. The initial row represents f_empty and the final column evaluates basis vectors at the empty word. The generalized fold proof gives all-word correctness, including zero dimension.

**Theorem 1.7 (Finite Hankel rank and attained minimum dimension).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.finite_hankel_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/WordHankelRealization.finite_hankel_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement jointly gives finite residual dimension iff a finite matrix realization exists, the rank lower bound for every competing realization, and attainment at exactly the residual finrank. From any realization, map each row state to its complete future response; residuals lie in that linear-map range. From finite residual dimension, construct the invariant residual dynamics and transport the all-word fold identity through a basis. These are the arbitrary-word clauses of original theorem 5.3.

**Theorem 1.8 (Square invertible evaluations of independent functions).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.finite_evaluation_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/WordHankelRealization.finite_evaluation_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any field K, arbitrary type T and r > 0, r independent functions have r jointly separating evaluation points. Apply Mathlib Submodule.span_eq_top_of_ne_zero to evaluation functionals on their finite-dimensional span. Select a basis from the evaluation family using Submodule.exists_fun_fin_finrank_span_eq, transport its index along the dual-dimension equality, and use the original basis dual-coordinate equivalence to obtain independent matrix columns. No individual-point nonvanishing argument replaces joint invertibility. This is original lemma 5.2.

**Definition 1.9 (Prefix-suffix block).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.block`

*Formalization.* `D5/S3/Observer/Hankel/WordHankelRealization.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The (i,j) entry is f(p_i ++ s_j). Prefixes and suffixes are arbitrary word families; invertibility itself enforces any independence that is needed.

**Definition 1.10 (One-letter shifted block).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.shiftedBlock`

*Formalization.* `D5/S3/Observer/Hankel/WordHankelRealization.shiftedBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The (i,j) entry inserts a single letter between the original prefix and suffix: f(p_i ++ [a] ++ s_j).

**Definition 1.11 (Recovery with the global rank premise).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.recoveredRealization`

*Formalization.* `D5/S3/Observer/Hankel/WordHankelRealization.recoveredRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The construction requires finite dimensionality of the entire residual space and finrank equal to the block size. Invertibility makes the selected residuals independent, and the global rank makes them a basis. For any state g with row coordinates c, evaluations at the chosen suffixes are cH. Consequently c = eval(g) H⁻¹. Applying this to f_empty and the shifted selected basis vectors yields alpha = hH⁻¹, A_a = H_aH⁻¹ and beta = b. Correctness comes from the same all-state, all-word coordinate construction.

**Theorem 1.12 (Every full-rank block recovers the complete minimal model).**

Lean statement: `D5/S3/Observer/Hankel/WordHankelRealization.full_rank_block_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/WordHankelRealization.full_rank_block_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume finite residual dimension r > 0. For every chosen prefix/suffix family with invertible block, the displayed recovery formulas reproduce every word and every realization has dimension at least r. Existence of some invertible full block is a separate conjunct depending only on the global hypotheses: select a residual basis from the generating family and apply finite evaluation separation. An invertible finite block alone supplies no upper bound on the global rank. Original proposition 5.5 therefore remains fully compatible with this theorem.

The classical background is Stefan Kiefer, Notes on Equivalence and Minimization of Weighted Automata, arXiv:2009.01217v1, sections 1, 3 and 4 (https://arxiv.org/html/2009.01217v1): arbitrary fields, finite alphabets, zero-state semantics, the universal rank bound, and the Hankel realization. Kiefer uses suffix coordinates for H⁻¹H_a; the row-residual basis here gives the conjugate formula H_aH⁻¹. No algorithmic or novelty claim is attached to the abstract-field theorem.

The existing SequenceHankelRealization owner treats Nat-indexed tails and one operator; FiniteHoKalmanBlocks treats finite samples from a supplied single-operator model. Their hypotheses do not provide the arbitrary-word residual construction. FiniteWordReachability studies ordered endomorphism products and bounded reachability, with the head acting after the tail; it does not provide these response-coordinate and recovery identities.

## References

- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.MatrixRealization`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.block`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.canonicalMatrixRealization`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.canonicalShift`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.finite_evaluation_separation`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.finite_hankel_realization`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.full_rank_block_recovery`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.recoveredRealization`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.residual`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.residualSpace`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.shiftedBlock`
- Truth anchor: `D5/S3/Observer/Hankel/WordHankelRealization.wordProduct`
