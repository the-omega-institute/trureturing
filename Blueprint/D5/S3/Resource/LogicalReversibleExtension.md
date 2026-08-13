# Logical Reversibility by Retaining the Input

## Abstract

Every function into an additive group has a reversible work-register extension.

**Theorem 1.1 (A retained input makes the computation reversible).**

$$\forall X,A,\ [\operatorname{AddGroup}(A)],\ \forall f:X\to A,\ \exists e:\operatorname{Equiv}(X\times A,X\times A),\ \forall x,a,\ e(x,a)=(x,f(x)+a) \land \ \forall x,\ e(x,0)=(x,f(x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogicalReversibleExtension.logical_reversible_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected source clause says that logically reversible computation exists. For a function f into an additive group, retain the input x and add f(x) to an auxiliary register. Mathlib's Equiv.prodShear and Equiv.addLeft make this transformation an equivalence, while a zero auxiliary register produces the pair (x,f(x)).

The additive register models the reversible accumulator used by finite bit computations, with exclusive-or as its group operation. The theorem is more general than that intended specialization and uses no physical cost model.

This is a partial closure of proposition 3.9. The claim that the heat column can vanish, the reversible-simulation time-space upper-bound family, optimality within reversible pebble games, lower bounds outside that model, and the five-column synthesis remain unresolved.

## References

- Truth anchor: `D5/S3/Resource/LogicalReversibleExtension.logical_reversible_extension`
