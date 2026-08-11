# Internal Property Objects

## Abstract

Property objects are losslessly equivalent to their seven typed components.

**Theorem 1.1 (Property objects have seven lossless components).**

$$\operatorname{Bijective}(\operatorname{propertyObjectEquivComponents})$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PropertyObject.property_object_components_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An internal property object stores exactly seven typed components: its generation history, encoding, finite reading, ledger, self-code, dynamic update, and certificate. The formal equivalence forgets only the field names, sending the object to the nested product of those components. Its inverse rebuilds every field, and both round trips are proved. Bijectivity therefore certifies that internalization neither drops information nor adds an untracked component.

The pinned library was searched before implementation. It provides standard product equivalences such as Equiv.prodAssoc and Equiv.prodCongr, together with bundled bijectivity through Equiv.bijective, but it has no declaration for this source-specific seven-component property object. The Lean module consequently constructs only that local structure equivalence and delegates the final theorem to the library's bijectivity API. The source atom is a structural definition and carries no numerical certificate.

## References

- Truth anchor: `D5/S0/Computability/PropertyObject.property_object_components_bijective`
