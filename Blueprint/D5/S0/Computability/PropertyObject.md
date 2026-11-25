# Internal Property Objects

## Abstract

Property objects are losslessly equivalent to their seven typed components.

**Theorem 1.1 (Property objects have seven lossless components).**

$$\operatorname{Bijective}(\operatorname{encodePropertyComponents})$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PropertyObject.property_object_components_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An internal property object stores exactly seven typed components: its generation history, encoding, finite reading, ledger, self-code, dynamic update, and certificate. The formal equivalence forgets only the field names, sending the object to the nested product of those components. Its inverse rebuilds every field, and both round trips are proved. Bijectivity therefore certifies that internalization neither drops information nor adds an untracked component.

The strict product stores each component in the same position as the standard tuple. Rebuilding the object gives the left inverse used for injectivity. Rebuilding the tuple gives the right inverse used for surjectivity.

## References

- Truth anchor: `D5/S0/Computability/PropertyObject.property_object_components_bijective`
