# Resonant parity windows of the original weights

## Abstract

The original KBonacci weights give exact distinct-window counts on both resonant phase cosets.

Fix the original order k at least two and a positive block width m. Set T=k+1, g=gcd(m,T) and p=T/g, with g at least two. The weight G_n is dbonacci k (n+2), with initial values 2^n for n<k and the sum of its preceding k weights thereafter. The phase set P is the image of multiplication by g on ZMod T; P+1 is its translate by one. A window at a phase theta records the actual weights G_(theta.val+i) modulo two for all i in Fin j.

**Theorem 1.1 (Exact counts for every window length).**

$$(A_0=D_0=1)\qquad\land\qquad (\forall j\in\mathbb{N}, (j\geq1\implies(A_j=\min(p,2+\lfloor j/g\rfloor)\qquad\land\qquad D_j=\min(p,1+\lfloor(j+1)/g\rfloor))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciResonantWindowCounts.kbonacci_resonant_window_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A_j and D_j count distinct window vectors, the cardinalities of the actual window images over P and P+1. They count a shared zero vector once when some starts have no visible one. The formulas include p=1, g=2, empty windows and every length beyond a full period.

The original recurrence gives G_(n+k+1)+G_n=2G_(n+k). Thus parity has period T and ones exactly at residues zero and k. The cosets are enumerated exactly by qg and qg+1, for zero at most q below p. Their first-one offsets are zero at q=0 and (p-q)g-1 otherwise for P, and (p-q)g-2 for P+1. A visible first one distinguishes its window from every later first hit. All unseen hits yield the same zero window. Ordered first-hit representatives and one possible zero representative give the two image cardinalities.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciResonantWindowCounts.kbonacci_resonant_window_counts`
- Dependency: [D5/S0/Tower/DBonacciGeneral/UniformBaseGap](../../../S0/Tower/DBonacciGeneral/UniformBaseGap.md)
