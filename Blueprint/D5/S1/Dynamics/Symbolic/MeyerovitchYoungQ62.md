# An Aperiodic Payoff Shift on Primitive Graphs

## Abstract

Two finite primitive multigraphs give a nonempty aperiodic and nonsofic Equation (19) payoff shift.

Tom Meyerovitch and Aidan Young ask whether the shift in Equation (19) is always sofic and whether it always has a periodic point for primitive graphs and real payoffs. Question 6.2 is at https://arxiv.org/html/2603.21449v1#S6.Thmlemma2 and Equation (19) is at https://arxiv.org/html/2603.21449v1#S5.E19.

Write B for Bool and A for the paired edge alphabet B × (B × B). The H graph has one vertex and two distinct loop edges indexed by B. The G graph has vertices B and one edge (s,t) from s to t for each ordered pair. With α = √2 − 1 and signs −1 for false and +1 for true, the payoff on ((s,t),b) is the source sign times (b − α), with b read as zero or one, plus a cost of two if s and t differ. This payoff is real-valued.

**Theorem 1.1 (Attained minima at prescribed vertices).**

$$\forall (n: \mathbb{N}), (0 < n) \Rightarrow (\forall (w: Fin\left(n\right) \to B), \forall (s: B), \forall (t: B), \forall (c: \mathbb{R}), IsEdgeMinimum\left(n, w, s, t, c\right) \Leftrightarrow c = endpointMinimum\left(\alpha, n, w, s, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.edgeMinimum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive length and every binary H word, the minimum at each ordered pair of G vertices is attained among all legal G edge walks with those vertices as endpoints. The endpoint equivalence converts between these edge walks and the corresponding Boolean vertex sequences of length one greater.

**Definition 1.2 (Nonimprovability and optimal response on a finite block).**

$$\forall (n: \mathbb{N}), (0 < n) \Rightarrow (\forall (w: Fin\left(n\right) \to A), equationWindow\left(w\right) \Leftrightarrow \left(\left(\neg (\exists (v: Fin\left(n\right) \to B), HBetween\left(Hpart\left(w\right), v\right) \land (\forall (s: B), \forall (t: B), \exists (c: \mathbb{R}), \exists (d: \mathbb{R}), IsEdgeMinimum\left(n, Hpart\left(w\right), s, t, c\right) \land \left(IsEdgeMinimum\left(n, v, s, t, d\right) \land c < d\right)))\right) \land (\exists (s: B), \exists (t: B), GBetween\left(Gpart\left(w\right), s, t\right) \land IsEdgeMinimum\left(n, Hpart\left(w\right), s, t, edgeCost\left(Hpart\left(w\right), Gpart\left(w\right)\right)\right))\right))$$

*Formalization.* `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.equation19Window` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Hpart and Gpart are the edge projections of w. HBetween requires the competitor to run between the initial and final H vertices of Hpart(w). GBetween tests the actual initial and final vertices of Gpart(w) and every internal adjacency. In the two minima of the improvement test, c is the original minimum and d is the competing minimum. Both are attained. The response clause compares the actual cost of Gpart(w) with all legal walks at that same vertex pair.

**Definition 1.3 (The two-sided shift of Equation (19)).**

$$\forall (x: \mathbb{Z} \to A), x \in Y_{paper} \Leftrightarrow \left(LegalH\left(x\right) \land \left(LegalG\left(x\right) \land \forall (m: \mathbb{Z}), \forall (n: \mathbb{Z}), (m < n) \Rightarrow (equationWindow\left(W\left(x, m, n - m + 1\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.equation19` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subscript paper denotes this shift. LegalH and LegalG impose the H and G adjacency equalities at every integer coordinate. The interval block W starts at m and has n − m + 1 letters, including both endpoints. The finite-window condition requires that no H walk of the same length and with the original H vertex endpoints strictly increases the attained minima at every ordered pair of G vertices. It also requires that the given G walk attain the minimum at its own vertex endpoints. This is the union over all ordered G vertex pairs in the definition of the response set.

**Theorem 1.4 (Window equivalence at the actual vertex endpoints).**

$$\forall (n: \mathbb{N}), (0 < n) \Rightarrow (\forall (w: Fin\left(n\right) \to A), windowCondition\left(w\right) \Leftrightarrow equationWindow\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.windowCondition_iff_equation19Window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The optimized window condition computes both minima using vertex responses. The walk formulation uses attained minima over the actual edge paths. The comparison of H walks takes one competitor for all G endpoint pairs.

**Theorem 1.5 (The length-indexed shift equals the shift of Equation (19)).**

$$\forall (x: \mathbb{Z} \to A), x \in Y \Leftrightarrow x \in Y_{paper}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.shift_iff_equation19` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Y is the shift using optimized window conditions on W(x,i,n), the block of length n starting at i. Every inclusive interval with distinct endpoints gives a window of length at least two. Conversely the length-n window beginning at i occupies the inclusive interval from i through i + n − 1. The two window conditions agree by the attained-minimum identification.

**Theorem 1.6 (A nonempty shift with no periodic point and no finite edge presentation).**

$$\begin{aligned}AllPositiveLengths\left(hVertex, hVertex\right) \land AllPositiveLengths\left(fst, snd\right)\\\land (\forall (x: \mathbb{Z} \to A), \forall (k: \mathbb{Z}), x \in Y \Leftrightarrow (\lambda i, x\left(k + i\right)) \in Y)\\\land (\forall (x: \mathbb{Z} \to A), (\forall (i: \mathbb{Z}), \forall (n: \mathbb{N}), (2 \le n) \Rightarrow (\exists (y: \mathbb{Z} \to A), y \in Y \land W\left(x, i, n\right) = W\left(y, i, n\right))) \Rightarrow (x \in Y))\\\land (\exists (x: \mathbb{Z} \to A), x \in Y)\\\land (\neg (\exists (x: \mathbb{Z} \to A), x \in Y \land \exists (p: \mathbb{Z}), 0 < p \land Periodic\left(x, p\right)))\\\land (\forall (V: Type), \forall (E: Type), [Finite\left(V\right)] [Finite\left(E\right)], \forall (s: E \to V), \forall (t: E \to V), \forall (l: E \to A), \neg (\forall (x: \mathbb{Z} \to A), x \in Y \Leftrightarrow \exists (q: \mathbb{Z} \to E), (\forall (i: \mathbb{Z}), t\left(q\left(i\right)\right) = s\left(q\left(i + 1\right)\right)) \land (\forall (i: \mathbb{Z}), l\left(q\left(i\right)\right) = x\left(i\right))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AllPositiveLengths gives a walk at every positive length between any ordered vertex pair. For H both endpoint maps are hVertex, and for G they are the first and second projections. The cylinder condition is closedness in the product of the discrete paired edge alphabet. In the last clause V and E range over types in arbitrary universes with the displayed finiteness instances. The maps s and t are source and target, and l labels each edge by A.

A two-sided mechanical H word with the constant positive G loop satisfies all windows. Nonimprovability bounds the H discrepancy by seven on every allowed window. A positive period would multiply a nonzero irrational-slope discrepancy without bound. A nonempty finite presenting graph would supply a closed walk that repeats in both directions and gives a periodic point.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.edgeMinimum_iff`
- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.equation19`
- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.equation19Window`
- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.result`
- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.shift_iff_equation19`
- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.windowCondition_iff_equation19Window`
- Dependency: [D5/S1/Dynamics/Symbolic/BiInfinitePayoffPeriodicity](BiInfinitePayoffPeriodicity.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PrimitivePayoffSwitching](PrimitivePayoffSwitching.md)
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs](../../Words/Mechanical/SilverSlopeAbelianPeriodDefs.md)
