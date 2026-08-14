# Exact Diameter and Optimal Supports for Green Classes

## Abstract

A Green class has exact prefix-metric diameter set by its first unpinned coordinate.

**Theorem 1.1 (The first hole determines the exact Green-class diameter).**

$$\operatorname{diam}(G(S, t)) = \frac{1}{2}^{\operatorname{firstHole}(S)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/GreenClassDiameter.green_class_diameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let O be a nontrivial alphabet with the discrete topology, and equip infinite strings N -> O with Mathlib's PiNat prefix metric. For a finite support S and target t, the Green class G(S,t) consists of all strings agreeing with t on S. Its diameter is exactly (1/2)^firstHole(S), where firstHole(S) is the least coordinate outside S.

For the upper bound, two members of the class cannot first differ below the first hole: every smaller coordinate lies in S and is pinned to t. The PiNat distance formula and the strict decrease of (1/2)^n then bound every pairwise distance by (1/2)^firstHole(S).

For the lower bound, nontriviality supplies a symbol distinct from t at the first hole. Updating t only at that coordinate gives another member of G(S,t), and the two witnesses first differ exactly there. Their distance attains the upper bound, so the diameter equality is sharp; this is why nontriviality is load-bearing.

**Theorem 1.2 (Prefix supports uniquely minimize diameter at fixed budget).**

$$\frac{1}{2}^{\operatorname{card}(S)} \le \operatorname{diam}(G(S, t)) \land (\operatorname{diam}(G(S, t)) = \frac{1}{2}^{\operatorname{card}(S)} \iff S = \operatorname{range}(\operatorname{card}(S)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/GreenClassDiameter.prefix_support_minimizes_diameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every support S, firstHole(S) is at most card(S). Since powers of one half strictly decrease with their natural exponent, the exact diameter formula turns this combinatorial inequality into the lower bound (1/2)^card(S) <= diam G(S,t).

Equality of the diameters forces equality of the exponents. The frozen first-hole characterization says firstHole(S) = card(S) exactly when S is the initial segment range(card(S)); conversely that prefix support has its first hole at card(S). Thus prefix supports are the unique diameter minimizers at a fixed support budget.

## References

- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/GreenClassDiameter.green_class_diameter`
- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/GreenClassDiameter.prefix_support_minimizes_diameter`
- Dependency: [D5/S0/Naming/FirstHoleBound](../../Naming/FirstHoleBound.md)
- Dependency: [D5/S0/Naming/GreenClassMeasure](../../Naming/GreenClassMeasure.md)
