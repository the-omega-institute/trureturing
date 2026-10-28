# Fixed-block recorded quantum outputs

## Abstract

Trace-class terminal and continuous-record outputs with an exact norming positive decomposition.

Let H and K be arbitrary complete complex Hilbert spaces, X any measurable space with measure mu, and I a finite mode type. Output is WithLp 1 of TraceClass H times PiLp 1 of the I-indexed Bochner L1(X,mu;TraceClass K) spaces. Its norm is the terminal trace norm plus the sum of the integrated trace norms of the exact record densities. Positivity means operator positivity of the terminal block and almost-everywhere operator positivity of every record block. No separability, countability of the record space, finite-dimensional reference or finite-rank condition is imposed.

traceMass is the continuous real part of the trace pairing with the identity, using the genuine trace-class Banach norm. mass is the continuous real-linear sum of terminal traceMass and each record projection composed with the Bochner integral and traceMass. It equals terminal traceMass plus the integrals of the record traceMass. Positive outputs have norm equal to mass. pack uses Integrable.toL1, so record densities are genuine Bochner-integrable trace-class-valued functions rather than formal pointwise expressions.

**Theorem 1.1 (The positive cq norm is total trace mass).**

$$\forall H \in CompleteComplexHilbertSpace, K \in CompleteComplexHilbertSpace, X \in MeasurableSpace, mu \in MeasureX, I \in FiniteType, q \in Output,\; Positive\left(q\right) \Rightarrow norm\left(q\right) = mass\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/RecordedOutput.norm_eq_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive q in Output(H,K,I,mu), norm(q)=mass(q). On the terminal and almost every record block, the genuine positive trace norm equals real trace. The WithLp 1 product norm, PiLp 1 finite-mode norm and Bochner L1 norm add exactly these positive masses. This equality supplies the norm law needed by an actual cq target and by both norming parts.

**Theorem 1.2 (Exact norming positive decomposition).**

$$\forall H \in CompleteComplexHilbertSpace, K \in CompleteComplexHilbertSpace, X \in MeasurableSpace, mu \in MeasureX, I \in FiniteType, s \in TraceClassH, A \in ModeTraceClassK, h \in ModeRecordRealFunction,\; \left(SelfAdjoint\left(s\right) \land \left(AllPositive\left(A\right) \land AllIntegrable\left(h, mu\right)\right)\right) \Rightarrow \left(\exists P \in Output, N \in Output,\; Positive\left(P\right) \land \left(Positive\left(N\right) \land \left(pack\left(mu, s, scalarFixedBlocks\left(h, A\right)\right) = subtract\left(P, N\right) \land add\left(mass\left(P\right), mass\left(N\right)\right) = norm\left(pack\left(mu, s, scalarFixedBlocks\left(h, A\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/RecordedOutput.fixed_block_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For self-adjoint trace-class s, positive fixed trace-class blocks A_i, and arbitrary real integrable coefficients h_i, let q=pack(s,(t maps to h_i(t) A_i)). There are positive P,N in the same complete cq carrier with q=P-N and mass(P)+mass(N)=norm(q). The success parts are the existing CFC positive and negative parts, using the original trace-class membership lemmas. Their norm sum is the trace norm of s by the common Hilbert-basis diagonal formula and the CFC identity s-positive+s-negative=abs(s). The record parts are max(h_i,0) A_i and max(-h_i,0) A_i. Scalar positive/negative part integrability and constant scalar multiplication prove their Bochner integrability; the sum of their integrated norms is exactly integral |h_i| norm(A_i). This constructs only the decomposition needed for common fixed positive record blocks. It makes no global operator-valued Jordan measurability or trace-norm Lipschitz assertion.

**Theorem 1.3 (Positive mass-nonincreasing joint actions).**

$$\forall H \in CompleteComplexHilbertSpace, K \in CompleteComplexHilbertSpace, X \in MeasurableSpace, mu \in MeasureX, I \in FiniteType, s \in TraceClassH, A \in ModeTraceClassK, h \in ModeRecordRealFunction, W \in RealSeminormedSpace, D \in TargetPositivePredicate, v \in TargetMassFunction, Phi \in RealLinearMap,\; \left(FixedBlockHypotheses\left(mu, s, A, h\right) \land \left(PositiveTargetNormEqualsMass\left(D, v\right) \land PositiveMassNonincreasingRealLinear\left(Phi, D, v\right)\right)\right) \Rightarrow norm\left(apply\left(Phi, pack\left(mu, s, scalarFixedBlocks\left(h, A\right)\right)\right)\right) \le norm\left(pack\left(mu, s, scalarFixedBlocks\left(h, A\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/RecordedOutput.fixed_block_contracts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real seminormed target W, target positivity D and real mass v satisfying norm(w)=v(w) on D, let Phi be one real-linear map from this actual cq carrier into W. Suppose every positive q is mapped into D and v(Phi q)<=mass(q). Then norm(Phi(pack(s,h_i A_i)))<=norm(pack(s,h_i A_i)). Apply the exact norming decomposition before Phi, use real linearity and the triangle inequality, identify both positive target norms with their masses, and apply mass nonincrease to both norming parts. Contraction on these differences is derived from these laws; no operator norm bound is a map hypothesis. Mass preservation is a special case. The statement concerns unnormalized outputs; it asserts no normalized-postselection estimate, execution semantics or access permission.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/RecordedOutput.fixed_block_contracts`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/RecordedOutput.fixed_block_decomposition`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/RecordedOutput.norm_eq_mass`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/LogRegularization](LogRegularization.md)
