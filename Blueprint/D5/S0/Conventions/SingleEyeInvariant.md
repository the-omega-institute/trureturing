# Single-Eyed Invariants

## Abstract

An observer is single-eyed at a coordinate when every admitted invariant depends only on that coordinate.

**Definition 1.1 (Single-eyed observer predicate).**

$$\forall invariant admitted, \operatorname{dependency}(invariant) \subset \{coordinate\}$$

*Formalization.* `D5/S0/Conventions/SingleEyeInvariant.IsSingleEyed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary coordinate and invariant types, admitted is the set of invariants an observer accepts and dependency assigns each invariant its coordinate set. IsSingleEyed says every admitted dependency set is a subset of the singleton containing the selected coordinate.

The strict definition represents sets by membership predicates. For each admitted invariant and each input in its dependency set, it requires equality of that input with the selected coordinate.

This deposit is an honest partial closure of the leading definition clause of interface-philosophy-v4 corollary 4.5. Its later existence and visibility claims remain unresolved and are not asserted here.

## References

- Truth anchor: `D5/S0/Conventions/SingleEyeInvariant.IsSingleEyed`
