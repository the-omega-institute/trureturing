# Balanced Phases and Missing Residues

## Abstract

At a balanced actual Fibonacci phase, a strict prime-power center deficit gives positive prefixes with identical short End responses and different complete futures.

**Definition 1.1 (The balanced integer envelope).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/BalancedPhaseMissingResidue.envelope`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/BalancedPhaseMissingResidue.envelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural window budget L, put r equal to floor(L/2). The envelope width B is (Fibonacci(3r+2)-1) plus (Fibonacci(3(L-r)+1)-1). Negative Fibonacci indices are integer representatives of the forward modular weights. They do not permit reading a word backwards.

**Theorem 1.2 (A strict deficit prevents short-word separation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/BalancedPhaseMissingResidue.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/BalancedPhaseMissingResidue.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every H at least two, prime p, positive exponent a equal to the exponent of p in H, and L at least one, suppose B+1 is strictly less than p^a-p^a/p. There exist two positive ActualPrefixes at the same past length. Their next rows are equal even before modular reduction, and the common modular row is the balanced row above. Every common literal suffix of at most L windows returns the same original H/gcd End response on both sources, while their complete future response functions are different. ActualPrefix computes the same live seam and End tag on both sources. The two unit initializations remain available.

A zero-window prefix followed by 001 reaches the balanced modular phase through a positive return period of the actual row update. The proof encloses every integer bit contribution between sums of minimum and maximum signed Fibonacci weights; the width is B. Their modular image therefore has at most B+1 centers. This enclosure need not be filled by legal words, and it executes no extra padding windows.

The short centers cannot meet the bottom sibling condition: summing the required p-1 centers over all p^(a-1) parents would exceed B+1. The actual-source identification criterion therefore supplies distinct source residues with equal successful short answers. Common-depth fullness realizes those residues at one shared actual depth, and full-future residue fidelity transfers their short answers to these representatives. Illegal seams and invalid End requests produce the same error. Equal gcd answers give equal H/gcd answers; the complete-future equivalence preserves their eventual difference. Empty suffixes are included, and a modular zero remains a positive integer source. Thus any distinguishing window horizon for the full original task is strictly greater than L. Failure of the sufficient inequality gives no horizon upper bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/BalancedPhaseMissingResidue.envelope`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/BalancedPhaseMissingResidue.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/BottomSiblingBlockResolution](BottomSiblingBlockResolution.md)
