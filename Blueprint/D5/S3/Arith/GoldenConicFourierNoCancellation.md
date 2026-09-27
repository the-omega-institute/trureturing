# No Complete Cancellation in the Golden Conic Fourier Sum

## Abstract

The actual two and four stationary phases cannot cancel in an odd-modulus golden orbit.

The modulus N is nonzero. Every exponential in the formulas is the actual canonical additive character ZMod.stdAddChar on ZMod N, with complex values. It is not an arbitrary measured function. The four-term scalar i is a ring element satisfying i squared equals minus one; it is distinct from the complex imaginary unit in the exponential notation.

**Definition 1.1 (Two opposite actual phases).**

$$\forall N \in \mathbb{N}, \operatorname{Implies}\left(\operatorname{Lt}\left(0, N\right), \forall a \in \operatorname{ZMod}\left(N\right), \forall s \in \mathbb{C}, \operatorname{pairPeriod}\left(a, s\right) = \operatorname{ZModStdAddChar}\left(a\right) + s \cdot \operatorname{ZModStdAddChar}\left(\operatorname{neg}\left(a\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenConicFourierNoCancellation.pairPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a in ZMod N and s in Complex, pairPeriod(a,s) is e_N(a)+s*e_N(-a). Only the theorem restricts s to plus or minus one. Both signs are needed because the odd-precision quadratic Gauss coefficient can change sign at the opposite stationary point.

**Definition 1.2 (Four scalar-root phases).**

$$\forall N \in \mathbb{N}, \operatorname{Implies}\left(\operatorname{Lt}\left(0, N\right), \forall a \in \operatorname{ZMod}\left(N\right), \forall i \in \operatorname{ZMod}\left(N\right), \forall s \in \mathbb{C}, \operatorname{quarterPeriod}\left(a, i, s\right) = \operatorname{pairPeriod}\left(a, 1\right) + s \cdot \operatorname{pairPeriod}\left(i \cdot a, 1\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenConicFourierNoCancellation.quarterPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

quarterPeriod(a,i,s) is pairPeriod(a,1) plus s*pairPeriod(i*a,1). With i squared equal to minus one, it is the actual four-phase expression on the scalar stabilizer {1,-1,i,-i}. The definition does not assume its nonvanishing.

**Theorem 1.3 (Both Gauss signs remain nonzero).**

$$\forall N \in \mathbb{N}, \operatorname{Implies}\left(\operatorname{And}\left(\operatorname{Le}\left(3, N\right), \operatorname{Odd}\left(N\right)\right), \forall a \in \operatorname{ZMod}\left(N\right), \forall ainv \in \operatorname{ZMod}\left(N\right), \operatorname{Implies}\left(a \cdot ainv = 1, \operatorname{And}\left(\forall s \in \mathbb{C}, \operatorname{Implies}\left(\operatorname{Or}\left(s = 1, s = \operatorname{neg}\left(1\right)\right), \operatorname{pairPeriod}\left(a, s\right) \neq 0\right), \forall i \in \operatorname{ZMod}\left(N\right), \operatorname{Implies}\left(i^{2} = \operatorname{neg}\left(1\right), \forall s \in \mathbb{C}, \operatorname{Implies}\left(\operatorname{Or}\left(s = 1, s = \operatorname{neg}\left(1\right)\right), \operatorname{quarterPeriod}\left(a, i, s\right) \neq 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenConicFourierNoCancellation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every odd natural N at least three, and every a,ainv in ZMod N with a*ainv=1, both pairPeriod(a,1) and pairPeriod(a,-1) are nonzero. For every i with i^2=-1, quarterPeriod(a,i,1) and quarterPeriod(a,i,-1) are also nonzero. The modulus need not be prime.

The proof first shows that canonical character values have odd order and cannot equal minus one. Faithfulness and the displayed inverse rule out equal or reciprocal phases when i^2=-1. Writing x=e_N(a), y=e_N(i*a), multiplication by x*y factors the plus expression as (x+y)*(x*y+1) and the minus expression as (x-y)*(x*y-1). Every zero factor would contradict those arithmetic exclusions.

Section 7 of the existing li2026nonwieferich theory note uses this kernel after proving that the original golden orbit has scalar stabilizer of size tau/rho in {1,2,4}. It completes the previously unresolved cancellation step in the full Fourier support. The note separately establishes the rank quotient, all-precision support, first-zero criterion and moment formulas; this theorem supplies the noncancellation step.

## References

- Truth anchor: `D5/S3/Arith/GoldenConicFourierNoCancellation.pairPeriod`
- Truth anchor: `D5/S3/Arith/GoldenConicFourierNoCancellation.quarterPeriod`
- Truth anchor: `D5/S3/Arith/GoldenConicFourierNoCancellation.result`
