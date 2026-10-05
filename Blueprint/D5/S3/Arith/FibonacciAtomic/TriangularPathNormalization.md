# Reduced Triangular Paths

## Abstract

Binary output laws of reduced triangular paths.

**Definition 1.1 (Residual and retained labels).**

$$\operatorname{State}\left(r, e\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A state consists of natural numbers r and e. The first counts residual cylinders; the second counts labels sharing the anchor prefix. Legal states satisfy 0 <= r < e <= m.

**Definition 1.2 (Two column actions).**

$$one \lor \operatorname{zero}\left(h\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.Action` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The one action writes one to every retained label. The zero action writes one only to the last h retained labels, which then leave the retained group.

**Definition 1.3 (Successor state).**

$$\operatorname{successor}\left(s, a\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.successor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For one the successor is (2r-e,e). For zero(h) it is (2r-h,e-h). Natural subtraction is exact under the corresponding legal action conditions.

**Definition 1.4 (Legal state and action).**

$$\operatorname{Legal}\left(m, s, a\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In addition to 0 < e, r < e and e <= m, one requires e <= 2r. The zero(h) action instead requires 2r < e and h <= 2r. At (0,e), only zero(0) is legal and the successor equals the original state.

**Definition 1.5 (Legal infinite root path).**

$$\operatorname{RootPath}\left(m\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.RootPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A path gives a state and action at every natural depth, starts at (1,m), and satisfies legality and the successor equation at every step. A terminating path is extended by its zero residual self-loop.

**Definition 1.6 (Anchor digit).**

$$\operatorname{anchorDigit}\left(a\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.anchorDigit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The anchor digit is one for the one action and zero for every zero(h) action.

**Definition 1.7 (Actual label digit).**

$$\operatorname{digit}\left(gamma, i, d\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.digit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Indices i in Fin(m) represent labels i+1. At depth d, labels outside 0 <= i < e write zero. Retained labels write one for the one action; under zero(h), precisely e-h <= i < e write one. The digit belongs to Fin(2).

**Definition 1.8 (Output probability).**

$$\operatorname{p}\left(i\right) = \operatorname{tsum}\left(\frac{\operatorname{a}\left(i, d\right)}{2^{d+1}}\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.probability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each label, its probability is the sum of its depth d digit divided by 2^(d+1), for d starting at zero. Digits are interpreted as real numbers.

**Definition 1.9 (Anchor probability).**

$$t = \operatorname{tsum}\left(\frac{\operatorname{b}\left(d\right)}{2^{d+1}}\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.anchorMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The anchor mass is the same binary series formed from the anchor digits.

**Definition 1.10 (Residual layer cost).**

$$C = \operatorname{tsum}\left(\frac{\operatorname{r}\left(d\right)}{2^{d}}\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.pathCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The path cost sums r_d/2^d over all depths. It counts expected paid bits, rather than charging r_d bits for a single transition.

**Definition 1.11 (Integer digit prefix).**

$$\operatorname{prefix}\left(i, d+1\right) = 2\cdot\operatorname{prefix}\left(i, d\right)+\operatorname{a}\left(i, d\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.binaryPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty prefix is zero. Each new digit doubles the previous prefix and adds that digit. Thus a length D prefix represents the weighted sum of digits with weights 2^(D-1-d).

**Theorem 1.12 (Canonical law and exact layer cost).**

$$\forall m: \mathbb{N}, (m \ge 2 \implies \forall gamma: \operatorname{RootPath}\left(m\right), (\forall i: \operatorname{Fin}\left(m\right), 0 \le \operatorname{p}\left(i\right) \land (\operatorname{sum}\left(\operatorname{p}\left(i\right)\right) = 1 \land (\forall i: \operatorname{Fin}\left(m\right), \forall D: \mathbb{N}, \left\lfloor2^{D}\cdot\operatorname{p}\left(i\right)\right\rfloor = \operatorname{prefix}\left(i, D\right) \land (\operatorname{min}\left(p\right) = t \land (C = \operatorname{L}\left(p\right) \land (0 < t \implies \forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{p}\left(i\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m >= 2 and every legal root path, all output coordinates are nonnegative and sum to one. For every label and every depth D, floor(2^D p_i) equals the integer prefix of the first D written digits. The minimum coordinate equals t, and C equals the classical dyadic cost L(p). If t is positive then every coordinate is positive.

At each depth the total future output mass, in that depth's units, equals r. Every retained label has future mass at least that of the anchor. Hence the anchor future mass a satisfies 0 <= a <= r/e < 1. A label leaving at column D+1 exceeds the anchor by (1-a_(D+1))/2^(D+1), which is strictly positive. Labels that never leave write the anchor digits. The strict tail bound rules out all-one tails; the integer prefixes therefore coincide with actual floor prefixes. Summing these floors identifies every layer residual and the two costs.

Zero anchor mass and zero residual self-loops are included. The assertion concerns the reduced triangular graph; arbitrary paths in a larger carry graph can write noncanonical all-one tails.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.Action`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.Legal`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.RootPath`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.State`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.anchorDigit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.anchorMass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.binaryPrefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.digit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.pathCost`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.probability`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization.successor`
- Dependency: [D5/S3/Arith/FibonacciAtomic/DyadicSupportLines](DyadicSupportLines.md)
