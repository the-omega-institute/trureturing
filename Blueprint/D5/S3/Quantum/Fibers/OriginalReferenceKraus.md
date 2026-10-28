# Original jump outputs with a reference

## Abstract

Original absorbing Kraus rows retain arbitrary reference correlations.

**Theorem 1.1 (The actual row selects the same input block).**

$$\forall H \in CompleteComplexHilbertSpace, c \in Real, a \in Real, k \in Real, S \in Real, g \in \operatorname{Functions}\left(\operatorname{Fin}\left(5\right), Real\right), i \in \operatorname{Fin}\left(5\right), rho \in \operatorname{End}\left(\operatorname{B}\left(\operatorname{Fin}\left(5\right), H\right)\right),\; \left(\left(\operatorname{lessThanHalf}\left(c\right) \land \left(\operatorname{interior}\left(a, c\right) \land \operatorname{interior}\left(k, c\right)\right)\right) \land \left(0 \le S \land 0 \le \operatorname{apply}\left(g, i\right)\right)\right) \Rightarrow \operatorname{conjugate}\left(\operatorname{referenceJump}\left(c, a, k, S, g, i\right), rho\right) = \operatorname{smul}\left(\operatorname{coefficient}\left(c, a, k, S, g, i\right), \operatorname{compression}\left(rho, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalReferenceKraus.actual_jump_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be an arbitrary complete complex Hilbert reference and let B(Fin5,H)=PiLp 2 with five copies of H. The finite tensor coordinates identify this with the finite live system tensored with the unchanged reference. referenceJump is the sum over j of the actual original jumpKraus(c,a,k,S,g,i)[0,j] times the bounded coordinate projection pi_j. The row is derived from absorbingRow times successfulKraus, rather than prescribed by a desired output law. It equals alpha_i pi_i, where alpha_i=sqrt(g_i)*sqrt(S)*sqrt(p_i(k)/p_i(a)). For c<1/2, 0<a,k<c, S>=0 and g_i>=0, alpha_i times its complex conjugate equals f_i=g_i*S*p_i(k)/p_i(a). Expanding the actual conjugation gives J_i rho J_i*=f_i*pi_i rho iota_i, for the same arbitrary joint operator rho. No diagonal, finite-rank, pure, or product-state restriction is made.

**Theorem 1.2 (The genuine trace norm of the retained reference output).**

$$\forall H \in CompleteComplexHilbertSpace, c \in Real, a \in Real, k \in Real, S \in Real, g \in \operatorname{Functions}\left(\operatorname{Fin}\left(5\right), Real\right), i \in \operatorname{Fin}\left(5\right), rho \in \operatorname{TraceClass}\left(\operatorname{B}\left(\operatorname{Fin}\left(5\right), H\right)\right),\; \left(\left(\left(\operatorname{lessThanHalf}\left(c\right) \land \left(\operatorname{interior}\left(a, c\right) \land \operatorname{interior}\left(k, c\right)\right)\right) \land \left(0 \le S \land 0 \le \operatorname{apply}\left(g, i\right)\right)\right) \land 0 \le \operatorname{operator}\left(rho\right)\right) \Rightarrow \left(\operatorname{operator}\left(\operatorname{failureOutput}\left(c, a, k, S, g, i, rho\right)\right) = \operatorname{conjugate}\left(\operatorname{referenceJump}\left(c, a, k, S, g, i\right), \operatorname{operator}\left(rho\right)\right) \land \operatorname{norm}\left(\operatorname{failureOutput}\left(c, a, k, S, g, i, rho\right)\right) = \operatorname{multiply}\left(\operatorname{coefficient}\left(c, a, k, S, g, i\right), \operatorname{Re}\left(\operatorname{trace}\left(\operatorname{compression}\left(\operatorname{operator}\left(rho\right), i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalReferenceKraus.actual_jump_trace_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive trace-class joint rho, the heterogeneous positive compression theorem makes pi_i rho iota_i a genuine TraceClass H element. failureOutput is f_i times this element in its trace-norm Banach space. The preceding operator identity proves that its underlying operator is exactly the original amplified Kraus output. Positivity gives norm(pi_i rho iota_i)=Re Tr(pi_i rho iota_i); scalar homogeneity then gives the displayed norm. This statement is pointwise in time. It imposes no normalization assumption, and applies in particular to every normalized entangled input. The whole repeated-pair result additionally requires the actual time integrals, disjoint suffix supports, operational supremum, and the six-dimensional terminal block calculation.

**Theorem 1.3 (The absorbing successor preserves the reference norm).**

$$\forall H \in CompleteComplexHilbertSpace, c \in Real, a \in Real, k \in Real, S \in Real, g \in \operatorname{Functions}\left(\operatorname{Fin}\left(5\right), Real\right), i \in \operatorname{Fin}\left(5\right), rho \in \operatorname{TraceClass}\left(\operatorname{B}\left(\operatorname{Fin}\left(5\right), H\right)\right),\; \left(\left(\left(\operatorname{lessThanHalf}\left(c\right) \land \left(\operatorname{interior}\left(a, c\right) \land \operatorname{interior}\left(k, c\right)\right)\right) \land \left(0 \le S \land 0 \le \operatorname{apply}\left(g, i\right)\right)\right) \land 0 \le \operatorname{operator}\left(rho\right)\right) \Rightarrow \left(\operatorname{operator}\left(\operatorname{absorbingFailureOutput}\left(c, a, k, S, g, i, rho\right)\right) = \operatorname{conjugate}\left(\operatorname{absorbingJump}\left(c, a, k, S, g, i\right), \operatorname{operator}\left(rho\right)\right) \land \operatorname{norm}\left(\operatorname{absorbingFailureOutput}\left(c, a, k, S, g, i, rho\right)\right) = \operatorname{norm}\left(\operatorname{failureOutput}\left(c, a, k, S, g, i, rho\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalReferenceKraus.absorbing_jump_trace_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed absorbing successor is coordinate five of B(Fin6,H). The map absorbingJump is iota_f after the actual referenceJump. Expanding its adjoint conjugation gives iota_f times the reference output times pi_f. The positive compression of the same input is trace class on H; embedding it in coordinate f preserves its trace and positive trace norm. Scalar homogeneity therefore shows that absorbingFailureOutput is exactly the six-coordinate Kraus output and has the same trace norm as failureOutput. This conclusion starts from a five-coordinate live joint input. It does not assert the extension for a general initially live-and-stopped six-coordinate input or its terminal coherences.

**Theorem 1.4 (All mode-block masses belong to the same joint input).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{TraceClass}\left(\operatorname{B}\left(\operatorname{Fin}\left(5\right), H\right)\right),\; 0 \le \operatorname{operator}\left(rho\right) \Rightarrow \operatorname{sumReferenceBlockNorms}\left(rho\right) = \operatorname{norm}\left(rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalReferenceKraus.actual_output_mass_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive trace-class input the reference block at mode i is pi_i rho iota_i. Its positive trace norm is its real trace. Splitting the trace of rho on the full finite block Hilbert basis proves that the five trace norms sum to the trace norm of rho. For a normalized positive input their sum is one. The blocks are all taken from the same rho; off-diagonal reference correlations are not replaced by independently selected inputs.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalReferenceKraus.absorbing_jump_trace_norm`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalReferenceKraus.actual_jump_operator`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalReferenceKraus.actual_jump_trace_norm`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalReferenceKraus.actual_output_mass_partition`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks](../Analysis/TraceClass/FiniteBlocks.md)
- Dependency: [D5/S3/Quantum/Fibers/OriginalControlMarkedJump](OriginalControlMarkedJump.md)
