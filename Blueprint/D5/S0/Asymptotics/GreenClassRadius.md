# Sharp Radius of a Finite-Support Agreement Class

## Abstract

The first unpinned coordinate determines the sharp prefix-metric radius.

**Theorem 1.1 (The first unpinned coordinate gives the sharp radius).**

$$\forall O, S, t,\ (\exists y, y \neq t(\gamma(S))) \Rightarrow ((\forall x\in\operatorname{G}(S,t), \operatorname{dist}(x,t)\le\frac{1}{2}^{\gamma(S)}) \land (\exists x\in\operatorname{G}(S,t), \operatorname{dist}(x,t)=\frac{1}{2}^{\gamma(S)})).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/GreenClassRadius.green_class_radius_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a finite set of coordinates and let G(S,t) contain the sequences that agree with t on S. Mathlib's prefix metric assigns distance (1/2)^k when k is the first coordinate at which two sequences differ. Agreement on S therefore prevents a difference before the least coordinate outside S, giving the stated upper bound.

When the alphabet contains a symbol different from t at that first unpinned coordinate, updating t only there produces a member of G(S,t) whose first difference occurs at exactly that coordinate. This witness attains the upper bound, so the radius is sharp.

This deposit partially closes only the metric column of source theorem 7.4. Its information, measure, layer-spectrum, statistical-independence, and receipt-composition clauses remain unresolved.

## References

- Truth anchor: `D5/S0/Asymptotics/GreenClassRadius.green_class_radius_sharp`
- Dependency: [D5/S0/Naming/FirstHoleBound](../Naming/FirstHoleBound.md)
