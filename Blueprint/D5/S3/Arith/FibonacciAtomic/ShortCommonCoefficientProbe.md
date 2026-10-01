# Short Common Canonical Fibonacci Probes

## Abstract

Every modular coefficient pair has one short first-00 canonical word on all rows.

**Definition 1.1 (The first index above twice the modulus).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.firstIndex`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.firstIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural H, j=firstIndex(H) is the least index with F(j)>2H. The Fibonacci convention is F(0)=0, F(1)=1.

**Definition 1.2 (The integer-size cutoff).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.lengthIndex`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.lengthIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With q=F(firstIndex(H)), m=lengthIndex(H) is the least index with F(m)>=H(q+1). The defining set is nonempty.

**Definition 1.3 (The window bound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.lengthBound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.lengthBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The window budget is L(H)=(m+2)/3 in natural-number division, which is the ceiling of m/3.

**Definition 1.4 (The two basis-row coefficients).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.windowCoefficients`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.windowCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient pair of a literal word is its flattened Fibonacci evaluation at rows (1,0) and (0,1), in ZMod H.

**Definition 1.5 (The first two literal bits).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.firstTwoZero`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.firstTwoZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first two bits of the flattened word are both false.

**Definition 1.6 (Coefficient saturation by successful nonempty words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.Covers`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.Covers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Covers(H,L) requires every pair in (ZMod H)^2 to occur as the coefficient pair of a nonempty successful literal word of at most L windows. Success includes legality at the incoming true seam. For a nonempty word it also requires a nonzero last window.

**Definition 1.7 (Coefficient saturation with two leading zeros).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.Covers00`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.Covers00` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Covers00(H,L) adds the first-two-zero condition to the same nonempty successful word family.

**Definition 1.8 (The unrestricted saturation depth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.D`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D(H) is the infimum of the positive natural budgets satisfying Covers(H,L), in WithTop Nat. An empty set has infimum infinity.

**Definition 1.9 (The first-00 saturation depth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.D00`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.D00` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D00(H) is the infimum of the positive budgets satisfying Covers00(H,L), with the same infinity convention.

**Theorem 1.10 (One bounded canonical word works on every row and after every legal prefix).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Burton S. Kaliski Jr. (2017). *Targeted Fibonacci Exponentiation*. URL: <https://arxiv.org/abs/1711.02491v1>.

*Commentary.*

For every H>=2, j is at least five and 2H<F(j)<4H. For every pair A,B in ZMod H there is one nonempty word w of at most L(H) windows, beginning with two zero bits and having a successful canonical End. Its coefficient pair is (A,B), and for every row u,v its value is Au+Bv. The word may depend on H,A,B; it is common to all rows.

For either initialization bit epsilon and every literal prefix p legal at that bit, initialized(epsilon,p++w) returns some strictly positive natural N. This includes the empty legal prefix and the zero modular coefficient pair. Hence the modular zero readout never stands for the integer zero.

The saturation depths satisfy D(H)<=D00(H)<=L(H). An explicit logarithmic estimate is L(H)<=2 floor(log_2 H)+5, where the integer logarithm Nat.log takes base two. In terms of the real natural logarithm, L(H)<=7 log(H)/log(2), which gives O(log H).

A shifted rational Fibonacci grid supplies H<=n<H(q+1) with the prescribed integer and shifted-Zeckendorf residues. The Zeckendorf support of n lies below m. Place its digits at their original indices in an IndependentWord. The public LiteralWindowEnd equivalence supplies its successful inverse with the required length bound. Its padded-bit and numeric readout identities give the two basis coefficients; linearity extends them to shiftedFibSum(n)u+nv on every modular row. Its positive natural value excludes the empty word, and the two leading zeros preserve legality at either seam. The existing literal End theorem supplies positivity after a legal prefix. Finally 2^r<=F(2r+2) and H<2^(floor(log_2 H)+1) bound m by 4 floor(log_2 H)+12.

**Remark 1.11 (The modular Hofstadter G antecedent).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.result`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.result` (`✓ std3`).

*Citation.* Burton S. Kaliski Jr. (2017). *Targeted Fibonacci Exponentiation*. URL: <https://arxiv.org/abs/1711.02491v1>.

*Commentary.*

Kaliski, Appendix B, Lemma 5, Theorem 2 and Corollary 2 give simultaneous modular Hofstadter G pairs and logarithmic Zeckendorf length. The first-index constants used here adapt that arithmetic construction. The literal window alphabet, first two zeros, terminal trimming and arbitrary-prefix canonical End are additional statements.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.Covers`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.Covers00`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.D`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.D00`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.firstIndex`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.firstTwoZero`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.lengthBound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.lengthIndex`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.windowCoefficients`
- Dependency: [D5/S3/Analytic/GoldenEulerBetaZeckendorf](../../Analytic/GoldenEulerBetaZeckendorf.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd](LiteralWindowEnd.md)
