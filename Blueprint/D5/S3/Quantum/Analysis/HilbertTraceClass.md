# Hilbert Trace Class and Positive Trace

## Abstract

Intrinsic CFC trace class and basis-independent positive trace on arbitrary complex Hilbert spaces.

This module is an A17.2 source transplant of seven declarations from Tom Ole Diem’s physlib TraceClass/Basic at revision 0aeb3dc7e249f9acc9032252060d4fa5f35c7e20. The upstream declaration statements and proofs are retained; this is known mathematics and carries no claim of a new theorem or independent proof. The complete Apache 2.0 license is in docs/reports/hilbert-trace-class/physlib-LICENSE.txt. The verified immutable upstream tree has no NOTICE file.

**Definition 1.1 (Intrinsic trace class).**

$$\forall H \in \operatorname{Type}\left(u\right),\; \forall normed \in \operatorname{NormedAddCommGroup}\left(H\right),\; \forall inner \in \operatorname{InnerProductSpace}\left(\mathbb{C}, H\right),\; \forall complete \in \operatorname{CompleteSpace}\left(H\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; \operatorname{IsTraceClass}\left(T\right) \Leftrightarrow \left(\exists w \in \operatorname{Set}\left(H\right),\; \exists b \in \operatorname{HilbertBasis}\left(\operatorname{Subtype}\left(w\right), \mathbb{C}, H\right),\; \operatorname{Summable}\left((i: \operatorname{Subtype}\left(w\right) \mapsto \operatorname{re}\left(\operatorname{innerC}\left(b\left(i\right), \operatorname{CfcAbs}\left(T\right)\left(b\left(i\right)\right)\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/HilbertTraceClass.IsTraceClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate asks for one set-indexed Hilbert basis whose real diagonal of CFC.abs T is summable. CFC.abs is the continuous-functional-calculus square root of the adjoint-product operator. No finite dimension, separability, chosen physical basis or positivity premise is added.

**Lemma 1.2 (Parseval in a set-indexed Hilbert basis).**

$$\forall H \in \operatorname{Type}\left(u\right),\; \forall normed \in \operatorname{NormedAddCommGroup}\left(H\right),\; \forall inner \in \operatorname{InnerProductSpace}\left(\mathbb{C}, H\right),\; \forall w \in \operatorname{Set}\left(H\right),\; \forall b \in \operatorname{HilbertBasis}\left(\operatorname{Subtype}\left(w\right), \mathbb{C}, H\right),\; \forall y \in H,\; \operatorname{HasSum}\left((i: \operatorname{Subtype}\left(w\right) \mapsto \operatorname{pow}\left(\operatorname{norm}\left(\operatorname{innerC}\left(b\left(i\right), y\right)\right), 2\right)), \operatorname{pow}\left(\operatorname{norm}\left(y\right), 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/HilbertTraceClass.hasSum_norm_sq_inner_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary vector y, the sum of squared norms of its complex inner products with the Hilbert basis equals the squared norm of y. This lemma omits the completeness assumption. The proof takes real parts of the pinned HilbertBasis inner-product sum; it is consumed by the self-adjoint norm-square comparison.

**Lemma 1.3 (Basis independence of the squared image norms).**

$$\forall H \in \operatorname{Type}\left(u\right),\; \forall normed \in \operatorname{NormedAddCommGroup}\left(H\right),\; \forall inner \in \operatorname{InnerProductSpace}\left(\mathbb{C}, H\right),\; \forall complete \in \operatorname{CompleteSpace}\left(H\right),\; \forall S \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; \forall hS \in \operatorname{IsSelfAdjoint}\left(S\right),\; \forall w \in \operatorname{Set}\left(H\right),\; \forall v \in \operatorname{Set}\left(H\right),\; \forall b \in \operatorname{HilbertBasis}\left(\operatorname{Subtype}\left(w\right), \mathbb{C}, H\right),\; \forall c \in \operatorname{HilbertBasis}\left(\operatorname{Subtype}\left(v\right), \mathbb{C}, H\right),\; \forall hb \in \operatorname{Summable}\left((i: \operatorname{Subtype}\left(w\right) \mapsto \operatorname{pow}\left(\operatorname{norm}\left(S\left(b\left(i\right)\right)\right), 2\right))\right),\; \operatorname{HasSum}\left((j: \operatorname{Subtype}\left(v\right) \mapsto \operatorname{pow}\left(\operatorname{norm}\left(S\left(c\left(j\right)\right)\right), 2\right)), \operatorname{tsum}\left((i: \operatorname{Subtype}\left(w\right) \mapsto \operatorname{pow}\left(\operatorname{norm}\left(S\left(b\left(i\right)\right)\right), 2\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/HilbertTraceClass.hasSum_norm_sq_apply_of_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a bounded self-adjoint S and two arbitrary Hilbert bases, summability of the squared image norms in the first basis yields HasSum in the second basis with the first basis sum. The original nonnegative double-series and Parseval argument is retained. This is used by absolute-diagonal summability and the positive trace formula.

**Lemma 1.4 (Absolute-diagonal summability in every basis).**

$$\forall H \in \operatorname{Type}\left(u\right),\; \forall normed \in \operatorname{NormedAddCommGroup}\left(H\right),\; \forall inner \in \operatorname{InnerProductSpace}\left(\mathbb{C}, H\right),\; \forall complete \in \operatorname{CompleteSpace}\left(H\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; \forall h \in \operatorname{IsTraceClass}\left(T\right),\; \forall w \in \operatorname{Set}\left(H\right),\; \forall b \in \operatorname{HilbertBasis}\left(\operatorname{Subtype}\left(w\right), \mathbb{C}, H\right),\; \operatorname{Summable}\left((i: \operatorname{Subtype}\left(w\right) \mapsto \operatorname{re}\left(\operatorname{innerC}\left(b\left(i\right), \operatorname{CfcAbs}\left(T\right)\left(b\left(i\right)\right)\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/HilbertTraceClass.summable_inner_abs_of_hilbertBasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An intrinsically trace-class bounded operator has a summable real diagonal of its CFC absolute value in every Hilbert basis. The proof applies the self-adjoint comparison to the positive square root of CFC.abs T, retaining the actual operator meaning of trace class.

**Definition 1.5 (Complex trace from a trace-class witness).**

$$\forall H \in \operatorname{Type}\left(u\right),\; \forall normed \in \operatorname{NormedAddCommGroup}\left(H\right),\; \forall inner \in \operatorname{InnerProductSpace}\left(\mathbb{C}, H\right),\; \forall complete \in \operatorname{CompleteSpace}\left(H\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; \forall h \in \operatorname{IsTraceClass}\left(T\right),\; \operatorname{trace}\left(T, h\right) = \operatorname{tsum}\left((i: \operatorname{Subtype}\left(\operatorname{choose}\left(h\right)\right) \mapsto \operatorname{innerC}\left(\operatorname{choose}\left(\operatorname{chooseSpec}\left(h\right)\right)\left(i\right), T\left(\operatorname{choose}\left(\operatorname{chooseSpec}\left(h\right)\right)\left(i\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/HilbertTraceClass.trace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace is the complex diagonal sum in the Hilbert basis selected by the trace-class witness. The positive trace theorem below identifies this value with the sum in every other Hilbert basis. No unrestricted non-self-adjoint basis-independence claim is made.

**Lemma 1.6 (Complex summability for positive operators).**

$$\forall H \in \operatorname{Type}\left(u\right),\; \forall normed \in \operatorname{NormedAddCommGroup}\left(H\right),\; \forall inner \in \operatorname{InnerProductSpace}\left(\mathbb{C}, H\right),\; \forall complete \in \operatorname{CompleteSpace}\left(H\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; \forall hT \in 0 \le T,\; \forall h \in \operatorname{IsTraceClass}\left(T\right),\; \forall w \in \operatorname{Set}\left(H\right),\; \forall b \in \operatorname{HilbertBasis}\left(\operatorname{Subtype}\left(w\right), \mathbb{C}, H\right),\; \operatorname{Summable}\left((i: \operatorname{Subtype}\left(w\right) \mapsto \operatorname{innerC}\left(b\left(i\right), T\left(b\left(i\right)\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/HilbertTraceClass.summable_inner_of_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity makes the diagonal real and identifies CFC.abs T with T. The theorem converts the real absolute-diagonal summability into complex diagonal summability in every arbitrary Hilbert basis. Its full intrinsic trace-class and positivity hypotheses remain explicit.

**Lemma 1.7 (Positive trace in every Hilbert basis).**

$$\forall H \in \operatorname{Type}\left(u\right),\; \forall normed \in \operatorname{NormedAddCommGroup}\left(H\right),\; \forall inner \in \operatorname{InnerProductSpace}\left(\mathbb{C}, H\right),\; \forall complete \in \operatorname{CompleteSpace}\left(H\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; \forall hT \in 0 \le T,\; \forall h \in \operatorname{IsTraceClass}\left(T\right),\; \forall w \in \operatorname{Set}\left(H\right),\; \forall b \in \operatorname{HilbertBasis}\left(\operatorname{Subtype}\left(w\right), \mathbb{C}, H\right),\; \operatorname{trace}\left(T, h\right) = \operatorname{tsum}\left((i: \operatorname{Subtype}\left(w\right) \mapsto \operatorname{innerC}\left(b\left(i\right), T\left(b\left(i\right)\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/HilbertTraceClass.trace_eq_of_hilbertBasis_of_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive bounded trace-class operator, the witness-defined trace equals the complex diagonal sum in every Hilbert basis. The proof compares square-root norm sums across the witness and target bases. Zero spaces and zero operators remain in the universal domain.

The receiver remains on its own Lean v4.33.0 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d pins. Retirement is decided only at the receiver’s adopted pin: an explicit finite replacement map must supply the same intrinsic predicate, trace and theorem telescopes, and all live consumer applications and standard-axiom checks must pass. Then consumers are replaced and this transplant is removed in the same change. An external merge or an unpinned release is not a retirement trigger.

For a physical positive heat operator B, a diagonal HasSum in the physical Hermite basis can construct the intrinsic trace-class witness after reindexing the basis by its range. The positive trace formula then transfers that sum to every Hilbert basis. The same argument applies to the positive scalar-normalized Gibbs operator after scaling its diagonal sum. Those are consumer applications requiring their own exact checks; this supplier alone does not establish a partition function, physical tensor factorization, metaplectic realization or the whole parent theorem.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/HilbertTraceClass.IsTraceClass`
- Truth anchor: `D5/S3/Quantum/Analysis/HilbertTraceClass.hasSum_norm_sq_apply_of_selfAdjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/HilbertTraceClass.hasSum_norm_sq_inner_basis`
- Truth anchor: `D5/S3/Quantum/Analysis/HilbertTraceClass.summable_inner_abs_of_hilbertBasis`
- Truth anchor: `D5/S3/Quantum/Analysis/HilbertTraceClass.summable_inner_of_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/HilbertTraceClass.trace`
- Truth anchor: `D5/S3/Quantum/Analysis/HilbertTraceClass.trace_eq_of_hilbertBasis_of_nonneg`
