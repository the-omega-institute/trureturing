# Exact Ternary Raney Zero Runs

## Abstract

The literal Raney quotient R(3,1) modulo three has exactly the positive maximal zero-run lengths 3^m-1 for m>=1, in strictly increasing order, each at its unique first interval.

The sequence is the natural quotient choose(3*n+1,n)/(3*n+1), with n ranging over all nonnegative integers. This document treats the prime-three assertion of Ma and Zhang's complete small-prime record spectra. The modulus divides the Raney parameter k=3, so the coprimality hypothesis of the general coefficient-family theorem does not apply.

The literal sequence and maximal-interval convention are `D5/S1/Recurrence/Raney/ZeroRunFamilies.raneyNumber` and `D5/S1/Recurrence/Raney/MaximalBlockEvolution.IsMaximalDeltaInterval`. A maximal interval is nonempty, zero throughout, has a nonzero right neighbor, and either begins at zero or has a nonzero left neighbor. A record allows equality with previous run lengths.

**Theorem 1.1 (Complete support, maximal intervals, and tied records at three).**

Lean statement: `D5/S1/Recurrence/Raney/ExactTernaryRuns.raney_three_exact_zero_runs`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/ExactTernaryRuns.raney_three_exact_zero_runs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n the coefficient modulo three is one exactly when 2*n+1 is a power of three, and zero otherwise. Thus the support positions are s(m)=(3^m-1)/2, including s(0)=0 and s(1)=1. All positive maximal zero intervals, in both directions, are [(3^m+1)/2,(3^(m+1)-3)/2] for m>=1. Their lengths are 3^m-1, and these lengths are strictly increasing in m. Every run starting no later than the displayed interval has length at most its length. Any run of that same length has both displayed endpoints, so this is its unique occurrence and hence its first occurrence.

The proof begins with exact division in the natural numbers. The adjacent-binomial identity and coprimality of n with 3*n+1 show that 3*n+1 divides choose(3*n+1,n). Casting the resulting product identity to ZMod(3) identifies the quotient with that binomial coefficient; no generating-series coefficient identity is assumed. Lucas' single-digit formula then gives coefficient preservation at 3*n+1, zero at every 3*n+2, and zero at positive 3*n. Descent on the index proves the complete support formula.

The support positions satisfy s(m+1)=3*s(m)+1 and are strictly increasing. Every natural index lies between two successive support positions. An index strictly between them has zero coefficient. Actual maximality forces a zero run to fill the whole gap [s(m)+1,s(m+1)-1]; the support formula makes both immediate neighbors nonzero, with coefficient one. The m=0 gap is empty and every m>=1 gap is nonempty. This proves completeness over the unbounded sequence, rather than over a finite prefix. The strict growth of gap lengths gives the tied-record statement and uniqueness.

## References

- Truth anchor: `D5/S1/Recurrence/Raney/ExactTernaryRuns.raney_three_exact_zero_runs`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockEvolution.IsMaximalDeltaInterval`
- Truth anchor: `D5/S1/Recurrence/Raney/ZeroRunFamilies.raneyNumber`
- Dependency: [D5/S1/Recurrence/Raney/ZeroRunFamilies](ZeroRunFamilies.md)
