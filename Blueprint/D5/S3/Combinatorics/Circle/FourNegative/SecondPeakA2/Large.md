# Large

## Abstract

Second peak SecondPeakA2: Large

For all p>=64, q>=2 with q=2,4,8 or q>=16, and h=1 or 2, the integer or rational cover selects the first charged window. Exact stock estimates force 1<=v and 2v<=4pq. Rounding to a predecessor of a 32h block supplies M with all required low bits, strict m<M and strict physical stock.

**Theorem 1.1 (large_geometry).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large.large_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large.large_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem large_geometry (p q h : ℤ) (hp : 64≤p) (hq : 2≤q)     (hh : h=1 ∨ h=2) :     31*h*L p q<K p q h ∧ 2*K p q h+A p q h<t p q*A p q h ∧     62*h<y p q h

**Theorem 1.2 (integer_consumer_bounds).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large.integer_consumer_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large.integer_consumer_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem integer_consumer_bounds (p q h : ℤ) (hp : 64≤p) (hq : 16≤q)     (hh : h=1 ∨ h=2) :     0<D p q h ∧ 0≤1+60*h*Q q ∧     16*(1+60*h*Q q)≤D p q h ∧ 13*D p q h≤A p q h

**Theorem 1.3 (large_exists).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large.large_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large.large_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem large_exists (p q h : ℕ) (hp : 64≤p) (hq : 2≤q)     (hqs : q=2 ∨ q=4 ∨ q=8 ∨ 16≤q) (hh : h=1 ∨ h=2) :     ∃ v m M : ℕ, ∃ before : Bool, Good p q h v m M before

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large.integer_consumer_bounds`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large.large_exists`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large.large_geometry`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/ContinuousCover](ContinuousCover.md)
