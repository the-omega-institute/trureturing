# Scalar Softmax Trees and a Three-Class Obstruction

## Abstract

Scalar bilinear trees with three affine logits have uniform classification, square and log risk floors.

Let m be any natural number and n=m+3. Word(m) is the full function space Fin(n) to Window, with positions starting at zero. Window has exactly the five low-to-high bit strings 000,100,010,101,001. The uniform law averages over all raw words, without restricting seams or terminal windows. Each word has mass 5 to the power minus n; independence concerns complete windows.

The existing first-rejection diagnostic task uses zero-based seam labels and a final terminal label. coarse(w) is 1 when task(w) is its label 0, 2 when task(w) is its label 1, and 0 for every other diagnostic or acceptance. Consequently it is 1 when last(w(0)) and first(w(1)) are true, otherwise 2 when last(w(1)) and first(w(2)) are true, and otherwise 0. All-zero windows still occupy coordinates. Here last is the high bit and first the low bit.

A task tree is full, its leaf labels are distinct, and its leaf set is all Fin(n). Each encoder f(i) is an arbitrary real function on Window. B(l,r) is an arbitrary real bilinear map from two real lines to the real line. scalarImplementation uses the existing tree evaluator with these encoders and mergers. Its value on an unused empty storage tree is zero. Every task message is scalar; a zero-dimensional message embeds as the constant zero coordinate. There are no additional inputs, input-dependent controls or internal affine constants. A bilinear map on real scalars is B(1,1) times the product of its arguments. Induction on the tree gives a coefficient times the product of its leaf values.

The head parameters u and v are arbitrary functions Fin(3) to the reals. logit(u,v,z,y)=u(y)z+v(y); probability is its exponential divided by the sum of all three exponentials. maxima is the set of maximal logit labels. LegalChoice(choose) means that choose selects a member of every nonempty label set. prediction uses this fixed function of maxima alone. errorRisk averages its error indicator; squareRisk averages the sum over all three labels of squared errors against the one-hot coarse label, without division by three; logRisk averages minus the natural logarithm of the true-class probability.

**Theorem 1.1 (Three Uniform Risk Floors).**

$$\left(\forall \left(m: \operatorname{Nat}\left(\right)\right), \left(\forall \left(t: \operatorname{Tree}\left(\operatorname{Fin}\left(m+3\right)\right)\right), \left(\forall \left(f: \operatorname{Fin}\left(m+3\right) \to \operatorname{Window}\left(\right) \to \operatorname{Real}\left(\right)\right), \left(\forall \left(B: \operatorname{Tree}\left(\operatorname{Fin}\left(m+3\right)\right) \to \operatorname{Tree}\left(\operatorname{Fin}\left(m+3\right)\right) \to \operatorname{Bilinear}\left(\operatorname{Real}\left(\right), \operatorname{Real}\left(\right), \operatorname{Real}\left(\right)\right)\right), \left(\forall \left(u: \operatorname{Fin}\left(3\right) \to \operatorname{Real}\left(\right)\right), \left(\forall \left(v: \operatorname{Fin}\left(3\right) \to \operatorname{Real}\left(\right)\right), \left(\operatorname{Full}\left(t\right) \land \operatorname{leaves}\left(t\right) = \operatorname{univ}\left(\right)\right) \implies \left(\left(\forall \left(choose: \operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \operatorname{Fin}\left(3\right)\right), \operatorname{LegalChoice}\left(choose\right) \implies \frac{1}{125} \le \operatorname{errorRisk}\left(\operatorname{evaluate}\left(\operatorname{scalarImplementation}\left(f, B\right), t\right), u, v, choose\right)\right) \land \left(\frac{1}{250} \le \operatorname{squareRisk}\left(\operatorname{evaluate}\left(\operatorname{scalarImplementation}\left(f, B\right), t\right), u, v\right) \land \frac{\operatorname{log}\left(2\right)}{125} \le \operatorname{logRisk}\left(\operatorname{evaluate}\left(\operatorname{scalarImplementation}\left(f, B\right), t\right), u, v\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ScalarSoftmaxTreeObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All tree shapes, leaf functions, bilinear mergers and affine head parameters are quantified. The classification bound holds for every legal fixed choice rule. The two proper-loss bounds do not depend on a choice rule. The constants are uniform lower certificates, without an assertion of optimality or attainability.

Fix any tail. On first-window choices 000 and 001, middle-window choices 100 and 001, and third-window choices 000 and 100, the two middle slices have classes by rows 0,1 and by columns 0,2. The two middle slices are scalar multiples of the same four-value array. Each deterministic three-logit decision set is an interval, possibly a singleton or empty, including coincident logits and all ties. Two different interval classes separate their two pairs strictly. The row and column separations contradict each other, so some actual word is misclassified on every tail. Its conditional mass is 1/125. On an error a competing class has probability at least that of the true class; the latter is at most one half. The full square loss is at least one half and the log loss at least log(2). Averaging over every tail gives the three bounds.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ScalarSoftmaxTreeObstruction.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity](FirstRejectionCutCapacity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TreeMessageRealization](TreeMessageRealization.md)
