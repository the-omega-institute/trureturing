# Physical

## Abstract

Second peak SecondPeakA2: Physical

Set p=2^(d-c), q=2^(c-2), and h=1 or 2 according as b=d+1 or b=d+2. Thus z=4q, t=4pq and y=8hpq. The generic physical banks allocate every original label exactly once. The same sigma and literal fresh ear at j satisfy both complete OriginalOrder structures at the unchanged original seed. No rotation or assumed source certificate is introduced.

**Theorem 1.1 (complete_original_orders).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Physical.complete_original_orders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Physical.complete_original_orders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem complete_original_orders (b c d : ℕ) (hc : 3≤c) (hd : c+2≤d)     (hb : b=d+1 ∨ b=d+2) :     ∃ sigma : List (Fin (2+b+c+d)), ∃ j : ℕ, j≤2+b+c+d ∧       OriginalOrder (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)) sigma ∧       OriginalOrder (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c)))         (earWord (2+b+c+d) sigma j)

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Physical.complete_original_orders`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Exhaustion](Exhaustion.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/SourceCertificate](../SecondPeakHighD/SourceCertificate.md)
