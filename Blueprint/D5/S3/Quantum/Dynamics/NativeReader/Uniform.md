# Native reader pulse nonvanishing

## Abstract

Uniform absence of current-coordinate zeros in the original fifteen auxiliary pulses.

**Theorem 1.1 (One punctured parameter neighborhood for every pulse and both sectors).**

$$\exists eta: Real, 0 < eta \land eta < \operatorname{min}\left(alpha, 2 \times pi - alpha\right) \land \forall lambda: Real, \operatorname{PuncturedDistanceLess}\left(lambda, alpha, eta\right) \implies \forall i: Bool, \forall k: \operatorname{Fin}\left(15\right), \forall s: Real, \operatorname{during}\left(i, lambda, k, s, \operatorname{readyTail}\left(i\right)\right) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeReader/Uniform.reader_uniform_nonvanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source carrier consists of every binary path from b0=0 to b10=0 with no adjacent ones. Its fixed exterior is b(-1)=1, b11=1, b12=0. The extended carrier keeps every path b0 through b14 with endpoints zero and exterior b15=1, b16=0. The source-sector coordinate is b9. A complete auxiliary fiber is the path (i,z10,z11,z12,z13,z14,1); no legal configuration is removed. The unique ready tail is (i,0,1,0,0,0,1), and the physical report coordinate is b13, initially zero.

The Perron weights are d(0)=1 and d(1)=x, with x the inverse golden ratio and y=sqrt(x). The exact weighted legal-path projection supplies every local matrix entry. The common angle alpha is 3*pi/5. Only addresses eleven and thirteen use lambda; all other addresses retain alpha. The fifteen full forward calls have physical addresses (10,11,10,12,11,10,13,12,11,10,14,13,12,11,10). The parameter s denotes internal history within a call, rather than an executable fractional control. The full global phase exp(i*t) is retained.

The theorem gives a single positive eta smaller than min(alpha,2*pi-alpha). For every fixed lambda with 0<abs(lambda-alpha)<eta, every sector i, every call k from zero through fourteen, and every real internal time s, the ready-coordinate amplitude of during(i,lambda,k,s) is nonzero. In particular all closed physical call intervals and both values at their seams are included. The quantifier over all real s is an algebraic strengthening of the physical interval statement, not an additional operation.

At addresses eleven and thirteen the exact row support is proved to be the legal two-point edge containing the ready tail. The block is Q=((x,x*y),(x*y,x*x)). The difference between its Q quadratic form and the opposite diagonal coefficient times its squared norm is conserved. A zero current coordinate would force this charge to vanish. The entrance charge is real analytic in lambda because the literal entrance recursion uses finitely many matrix products of complex exponentials. At the mathematical reference parameter zero, the changed pulses are identities and each unchanged pulse preserves the ready column up to a nonzero phase. The resulting charge is nonzero. The analytic identity principle and isolated-zero theorem therefore give a punctured neighborhood of alpha for each entrance; a finite intersection gives one eta. Zero is used only to prove nonidentity of the analytic expression.

The charge-conservation, finite-root or analytic-isolation, scalar phase and matrix algebra steps are standard suppliers and bookkeeping. The source-specific proof obligation is their live application to the exact legal-edge supports and literal entrance recursion, without a supplied no-zero or invariant certificate. Helpers are consumed in this derivation; no global novelty claim is made.

This statement concerns the actual source-defined finite pulse matrices and ready columns. It does not construct the native Bell source probability space, prove its square-law marginal, instantiate arbitrary original preparation and future words, establish ideal reader correctness, or identify full report-dependent causal archives. Those additional obligations are necessary for the complete probabilistic instability theorem. In particular this result alone supplies neither the address-nine probability x nor a full-history total-variation statement.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeReader/Uniform.reader_uniform_nonvanishing`
- Dependency: [D5/S3/Quantum/Dynamics/NativeReader/Invariants](Invariants.md)
