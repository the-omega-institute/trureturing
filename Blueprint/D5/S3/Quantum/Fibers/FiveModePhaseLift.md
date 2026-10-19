# Five-Mode Phase Lift

## Abstract

A phase-sensitive projector separates a convex segment invisible to the actual real menu and the odd-rejection branch.

Use the coordinate order of FiveModeRealResponse and ReadoutInstrument. The rays have coordinate 2 equal to one, coordinate 4 equal to plus or minus i, and all other coordinates zero. Pplus and Pminus denote one half of their outer products with their conjugates. Thus they are the pure states of the normalized vectors obtained by dividing the rays by the square root of two. For q in the real closed unit interval, rho(q) is q times Pplus plus (1 minus q) times Pminus. Born(X) means the real part of trace(X Pplus). Branch(X) is the trace of the original branch-7 Kraus map applied to X. Response(X,P,h) is ludersLaw menu P X h for the actual menu of FiveModeRealResponse.

**Theorem 1.1 (A constant response fiber with an exact phase readout).**

$$\forall q\in \operatorname{IccReal}(0,1),\operatorname{PSD}(Pplus)\land \operatorname{Tr}(Pplus)=1\land \operatorname{PSD}(Pminus)\land \operatorname{Tr}(Pminus)=1\land PplusPplus=Pplus\land PminusPminus=Pminus\land PplusPminus=0\land \\\operatorname{PSD}(1-Pplus)\land \neg \operatorname{IsDiag}(Pplus)\land \operatorname{PSD}(\operatorname{rho}(q))\land \operatorname{Tr}(\operatorname{rho}(q))=1\land \\(\forall r\in \operatorname{IccReal}(0,1),\forall P:\operatorname{Protocol}(\operatorname{Fin}(5)),\forall h:\operatorname{Record}(P),\operatorname{Response}(\operatorname{rho}(q),P,h)=\operatorname{Response}(\operatorname{rho}(r),P,h))\land \\\operatorname{Branch}(\operatorname{rho}(q))=\frac{1}{2}\land \operatorname{Born}(\operatorname{rho}(q))=q$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiveModePhaseLift.phase_lift_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two endpoint matrices are positive trace-one orthogonal rank-one projections. The complement of Pplus is positive, so Pplus defines a projective two-outcome measurement together with its complement. Its coordinate (2,4) is nonzero and purely imaginary, hence it is non-diagonal. Convexity gives positivity of rho(q), and linearity of trace gives normalization. Every rho(q) has the same entrywise real part: its diagonal coordinates 2 and 4 are one half and all its real off-diagonal coordinates vanish. The exact real-response fiber theorem therefore supplies equality for every finite feedback protocol and each retained record, with arbitrary nonnegative real waits.

The arbitrary-input branch theorem gives Branch(rho(q)) equal to rho(q) at coordinate (4,4), namely one half. Orthogonality and idempotence give trace(rho(q) Pplus) equal to q, exactly and without an error term. Distinct real mixing parameters therefore have distinct Born readouts even though all old responses and branch masses agree. This is a finite-dimensional operational construction. It supplies no Source, event map, or common stochastic realization connecting q to the Fibonacci JointLaw parameter. In particular q, kappa, p at coordinate 4, the (4,4) population, and the (2,4) coherence are not identified. No physical preparation, QFT realization, compression channel, or literature novelty is asserted.

**Theorem 1.2 (The old menu and diagonal branch do not determine the phase measurement).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiveModePhaseLift.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here claim asserts the following universal implication for every pair X,Y of five-dimensional positive trace-one matrices: if Response(X,P,h) equals Response(Y,P,h) for every finite protocol P and record h, and Branch(X) equals Branch(Y), then Born(X) equals Born(Y). The endpoint mixtures q equal to zero and one satisfy the premises and have Born values zero and one. Thus no rule defined only by the complete old responses and branch trace can predict this added observable on all density states. The obstruction concerns the specified observation family; adding the phase-sensitive measurement resolves the mixing coordinate on this segment.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/FiveModePhaseLift.phase_lift_certificate`
- Truth anchor: `D5/S3/Quantum/Fibers/FiveModePhaseLift.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary](../../Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.md)
- Dependency: [D5/S3/Quantum/Fibers/FiveModeRealResponse](FiveModeRealResponse.md)
