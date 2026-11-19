# Analytic dependence of literal entrances

## Abstract

Analytic dependence of literal entrances.

**Theorem 1.1 (Analytic dependence of literal entrances).**

$$\forall i: Bool, \forall k: Nat, \forall z: \operatorname{Tail}\left(i\right), \forall t: Real, \operatorname{RealAnalyticAt}\left(\operatorname{EntranceCoordinate}\left(i, k, z\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeReader/Pulses.entrance_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix projection(i,j) is the original weighted legal-path projection at interior tail position j+1. Its Hermitian and idempotent properties directly apply weighted_legal_path_temperley_lieb with the actual adjacency and Perron data. Pulse(i,j,t)=exp(i*t)*(I+(exp(i*t)-1)*projection(i,j)); its global phase is retained. Only j=1 and j=3 use the common lambda; other j use alpha=3*pi/5. The physical word is (10,11,10,12,11,10,13,12,11,10,14,13,12,11,10), with local indices obtained by subtracting ten. Each entrance executes all preceding full unit-time calls.

EntranceCoordinate(i,k,z) denotes lambda mapped to entrance(i,lambda,k)(z). The theorem states real analyticity at every real t, for either sector, every natural k and every coordinate in its complete tail carrier. Induction uses the actual recursion, the real-linear complex inclusion, complex exponential analyticity and finite matrix sums. At the mathematical reference parameter zero, changed calls are identities; the ready row and column of every unchanged call are derived from the actual projection support and legality. Thus reference_entrance is a nonzero phase multiple of the unique ready vector. No zero-parameter operation is added to the control menu. All these helpers are consumed by the source charge and uniform nonvanishing proof.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeReader/Pulses.entrance_analytic`
- Dependency: [D5/S3/Quantum/Dynamics/NativeReader/Carrier](Carrier.md)
