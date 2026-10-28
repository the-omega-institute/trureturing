# Weighted nonprime residual

## Abstract

The exact weighted residual separates prime terms from all remaining Mangoldt terms.

**Theorem 1.1 (The original real-endpoint finite split).**

Lean statement: `D5/S3/Weil/Mertens/Estimates.sub_E1p_eq_sum_nonprime`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/Estimates.sub_E1p_eq_sum_nonprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x, the original difference Mertens.E1Lambda(x)-Mertens.E1p(x) is sum(if n is not prime then Lambda(n)/n else 0,0<n<=floorNat(x)). The logarithmic terms cancel and Lambda(p)=log(p) at each prime p. The cutoff is inclusive, so a prime power equal to x remains present. No lower bound on x is needed.

The same finite identity gives the nonprime partial sums in the weighted prime-limit argument and the selected-prime-power lower bound in the explicit Mertens envelope.

## References

- Truth anchor: `D5/S3/Weil/Mertens/Estimates.sub_E1p_eq_sum_nonprime`
