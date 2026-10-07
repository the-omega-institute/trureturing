# Triangular First-Split Values

## Abstract

No-split orbits and discounted first-split path values.

**Definition 1.1 (Arbitrary starting state).**

$$\operatorname{Path}\left(e, r\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.Path` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A path starts at (r,e), uses the existing reduced triangular actions, and obeys legality and the successor equation at every natural depth. Its state bound is the initial retained label count e.

**Definition 1.2 (No-split residual orbit).**

$$(\operatorname{rho}\left(e, r, 0\right) = r \land \operatorname{rho}\left(e, r, j+1\right) = \operatorname{mod}\left(2\cdot \operatorname{rho}\left(e, r, j\right), e\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The orbit starts at r and repeatedly sends a to 2a modulo e. This also retains the zero residual self-loop.

**Definition 1.3 (First visits).**

$$\operatorname{J}\left(e, r\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set consists of j less than e for which no earlier orbit index has the same residual. Thus it comprises all indices before the first repetition.

**Definition 1.4 (No-split cost).**

$$\operatorname{U}\left(e, r\right) = \sum_{j \in \mathbb{N}}\frac{\operatorname{rho}\left(e, r, j\right)}{2^{j}}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cost is the infinite real series summing rho(e,r,j)/2^j over all natural j.

**Definition 1.5 (No-split affine value).**

$$\operatorname{K}\left(x, e, r\right) = \operatorname{U}\left(e, r\right)-\frac{x\cdot r}{e}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract x times r/e from U(e,r). Here x is any real price.

**Definition 1.6 (Path objective).**

$$\operatorname{pathValue}\left(x, gamma\right) = C_{gamma}-x\cdot t_{gamma}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.pathValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The objective is the sum of residual layer counts divided by 2^d, minus x times the sum of anchor digits divided by 2^(d+1). The anchor digit and legal actions have their original meanings.

**Definition 1.7 (Infimum over paths).**

$$\operatorname{W}\left(x, e, r\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the real infimum of the objectives of every infinite legal path from (r,e). Zero residual self-loops are included in this domain.

**Definition 1.8 (Finite positive split choices).**

$$\operatorname{splitChoices}\left(e, r\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.splitChoices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pair (j,h) is retained precisely when j belongs to J(e,r), 2rho(e,r,j) is less than e, and 1 <= h <= 2rho(e,r,j).

**Definition 1.9 (Discounted first-split corrections).**

$$\operatorname{corrections}\left(x, e, r\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.corrections` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set contains zero and, for every retained pair (j,h), the number [rho(e,r,j) + W(x,e-h,2rho(e,r,j)-h)/2 - K(x,e,rho(e,r,j))]/2^j.

**Definition 1.10 (Action without positive splitting).**

$$\operatorname{noSplitAction}\left(e, a\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.noSplitAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose the one action if e <= 2a, and otherwise choose zero(0).

**Definition 1.11 (Infinite no-split path).**

$$\operatorname{noSplit}\left(e, r\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.noSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r < e, the states are (rho(e,r,j),e) and each action is the corresponding no-split action.

**Definition 1.12 (Path from a later state).**

$$\operatorname{suffix}\left(gamma, n\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.suffix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Discard the first n transitions. The initial state and the state bound are those of the original path at depth n.

**Definition 1.13 (Path with a specified first split).**

$$\operatorname{splitPath}\left(e, r, j, h, delta\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.splitPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Follow the no-split path for j transitions, perform zero(h), and follow delta from the successor (2rho(e,r,j)-h,e-h). The parameters require r < e, 2rho(e,r,j) < e and h <= 2rho(e,r,j).

**Theorem 1.14 (Finite first-split recurrence and attainment).**

$$(\forall m: \mathbb{N}, (2 \le m \implies (\forall x: \mathbb{R}, (\forall e: \mathbb{N}, ((1 \le e \land e \le m) \implies (\forall r: \mathbb{N}, (r < e \implies (\operatorname{W}\left(x, e, 0\right) = 0 \land ((0 < r \implies \operatorname{W}\left(x, e, r\right) = \operatorname{K}\left(x, e, r\right)+\operatorname{min}\left(\operatorname{corrections}\left(x, e, r\right)\right)) \land (\exists gamma: \operatorname{Path}\left(e, r\right), \operatorname{pathValue}\left(x, gamma\right) = \operatorname{W}\left(x, e, r\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m >= 2, every real price x, every retained count 1 <= e <= m, and every natural residual r < e, W(x,e,0) is zero. If r is positive, W(x,e,r) equals K(x,e,r) plus the minimum of corrections(x,e,r). There exists an infinite legal path gamma from (r,e) whose objective equals W(x,e,r).

The corrections set contains zero and the discounted correction [rho_j + W(x,e-h,2rho_j-h)/2 - K(x,e,rho_j)]/2^j for every first visit j with 2rho_j < e and every 1 <= h <= 2rho_j. Each positive split strictly reduces e, so the values on the right are obtained at smaller retained counts.

Without a positive split, the residual follows the modular orbit, the cost is U(e,r), and the anchor mass is r/e. At the first positive split the common prefix cancels against this path, leaving the displayed correction. A later visit to the same residual has a smaller positive discount. A negative correction is therefore best at its first visit; a nonnegative correction cannot improve on zero. The finite minimum is attained by either the no-split path or a finite prefix, a split, and an attaining path at smaller e.

The infimum ranges over all legal infinite paths. Finite candidate indices compute its value and one attaining path. They do not exclude later visits with zero correction, including arbitrary finite waits around a cycle.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.J`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.K`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.Path`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.U`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.W`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.corrections`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.noSplit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.noSplitAction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.pathValue`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.rho`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.splitChoices`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.splitPath`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.suffix`
- Dependency: [D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization](TriangularPathNormalization.md)
