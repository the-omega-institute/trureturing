# Opposite errors and smaller denominators

## Abstract

A unimodular pair with opposite approximation errors excludes smaller denominators.

**Theorem 1.1 (The opposite error is a uniform lower bound).**

$$\forall q \in \mathbb{Z},\; \forall p \in \mathbb{Z},\; \forall s \in \mathbb{Z},\; \forall r \in \mathbb{Z},\; \forall m \in \mathbb{Z},\; \forall z \in \mathbb{Z},\; \forall alpha \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall e \in \mathbb{R},\; \left(0 < q \land \left(0 < s \land \left(0 < m \land \left(m < q \land \left(q \cdot r - p \cdot s = 1 \land \left(0 < d \land \left(0 < e \land \left(\operatorname{real}(q) \cdot alpha - \operatorname{real}(p) = d \land \operatorname{real}(s) \cdot alpha - \operatorname{real}(r) = -e\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow e \le \left|\operatorname{real}(m) \cdot alpha - \operatorname{real}(z)\right|$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/UnimodularApproximationBound.unimodular_opposite_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q,p and s,r be integer pairs with determinant qr-ps=1 and positive denominators. If their errors at a real slope alpha are d and -e, with d,e positive, every positive integer denominator m below q has error at least e against every integer numerator z. Integer quantities in the two error equations and conclusion are coerced to real numbers.

The determinant gives integer coordinates a,b with m=aq+bs and z=ap+br. The inequalities 0<m<q force either a positive and b negative, or a nonpositive and b positive. In both cases the absolute error ad-be is at least e.

**Theorem 1.2 (Every other denominator in the gap has larger error).**

$$\forall q \in \mathbb{Z},\; \forall p \in \mathbb{Z},\; \forall s \in \mathbb{Z},\; \forall r \in \mathbb{Z},\; \forall m \in \mathbb{Z},\; \forall z \in \mathbb{Z},\; \forall alpha \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall e \in \mathbb{R},\; \left(0 < q \land \left(0 < s \land \left(s < q \land \left(q \le m \land \left(m < 2 \cdot q + s \land \left(m \ne q \land \left(m \ne 2 \cdot q \land \left(m \ne q + s \land \left(q \cdot r - p \cdot s = 1 \land \left(0 < d \land \left(2 \cdot d \le e \land \left(\operatorname{real}(q) \cdot alpha - \operatorname{real}(p) = d \land \operatorname{real}(s) \cdot alpha - \operatorname{real}(r) = -e\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow d + e \le \left|\operatorname{real}(m) \cdot alpha - \operatorname{real}(z)\right|$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/UnimodularApproximationBound.unimodular_gap_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume in addition that 0<s<q and e is at least twice d. For q≤m<2q+s, excluding q, 2q and q+s raises the lower bound to d+e. Integer quantities in real error equations are coerced to real numbers. The integer coordinate b is either negative, at least two, zero or one. The first two cases give the error estimate; the last two force one of the three excluded denominators.

## References

- Truth anchor: `D5/S1/Words/Mechanical/UnimodularApproximationBound.unimodular_gap_error_bound`
- Truth anchor: `D5/S1/Words/Mechanical/UnimodularApproximationBound.unimodular_opposite_error_bound`
