# Exact native terms and finite presentations

## Abstract

Exact native terms and finite presentations.

The finite-map primitives and original Strata monotype representation are licensed reuse from strata-org/Strata at a74043b69b98d4197dfd7d59df1b4427dcfc3f37. The native codec establishes the new exact inverse and constructor/support laws. The explicit presentation covers every original variable; it is not restricted to variables occurring in equations.

**Definition 1.1 (Effective complete variable presentations).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.Presentation`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.Presentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A presentation enumerates every member of the original type X and supplies a computable String code and Option decoder. Decoding an encoded variable returns that variable, and every successful name decode re-encodes to the original identifier. Empty variable types are included.

**Definition 1.2 (Two distinct nullary leaves).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.leaf`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.leaf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

False and true have distinct nullary constructor names. They represent the two generators of FreeMagma Bool.

**Definition 1.3 (Ordered binary pairing).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.pair`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.pair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pair constructor has exactly two ordered children. Other names and other arities are outside the native fragment.

**Definition 1.4 (Literal term encoding).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.encode`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Term X is exactly FreeMagma (Bool sum X). Encoding preserves both Boolean leaves, every original variable and every binary branch.

**Definition 1.5 (Ground source encoding).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.encodeGround`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.encodeGround` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ground sources are actual FreeMagma Bool trees, with their original Boolean labels and ordered binary branches.

**Definition 1.6 (Native term evaluation).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.evaluate`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.evaluate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing free-magma lift evaluates Boolean generators as leaves and variables by one supplied assignment.

**Definition 1.7 (Exact constructor fragment).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.Shape`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.Shape` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Shape contains arbitrary variables, exactly two distinct nullary Boolean constructors, and exactly one binary pair constructor. It does not contain bit vectors, foreign names or malformed arities.

**Definition 1.8 (Checked structural decoding).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.nativeDecode`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.nativeDecode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total Option decoder checks the exact native constructor names and arities and the original-variable name decoder. It fails outside that domain.

**Definition 1.9 (Original-variable support).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.Supported`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.Supported` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every free identifier must be the code of an original variable; this support condition is separate from constructor shape.

**Theorem 1.10 (Left inverse).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.decode_encode`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeUnificationCore.decode_encode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every presentation and every original native term t, decoding its encoding is some t.

**Theorem 1.11 (Faithful native encoding).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.encode_injective`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeUnificationCore.encode_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The checked inverse makes the term encoding injective, including the distinct Boolean leaves and repeated variables.

**Theorem 1.12 (Encoding preserves native constructors).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.encode_shape`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeUnificationCore.encode_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every encoded term has the exact native constructor shape.

**Theorem 1.13 (Encoding uses original variables).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.encode_supported`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeUnificationCore.encode_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every free identifier of an encoded term is the code of an original member of X.

**Theorem 1.14 (Decoding the complete fragment).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.decode_exact`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeUnificationCore.decode_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every presentation p and type tree t with exact Shape and original-variable Supported, there is a native term whose successful decoding and re-encoding recover exactly t.

**Definition 1.15 (Computable ordinal identifiers).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.finName`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.finName` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unary word of length n gives a computable finite-ordinal identifier.

**Definition 1.16 (Effective ordinal presentation).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.finPresentation`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.finPresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n has an explicit complete enumeration, unary-word encoding and checked decoder for all n, including zero.

**Definition 1.17 (Presentation transport).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.transport`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.transport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A supplied equivalence transports the complete enumeration and both naming laws to the original type.

**Definition 1.18 (All finite original variable types).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.finitePresentation`

*Formalization.* `D5/S0/Rewriting/NativeUnificationCore.finitePresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every finite type X admits the full presentation data. Algorithm execution uses an explicitly supplied presentation, while the mathematical scope includes every finite X.

**Theorem 1.19 (Right inverse and rejection).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.encode_decode`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeUnificationCore.encode_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every successful structural decode re-encodes to exactly the input type tree. Thus a bit vector, foreign constructor or malformed arity cannot decode into a native term.

**Theorem 1.20 (Exact decoding domain).**

Lean statement: `D5/S0/Rewriting/NativeUnificationCore.decode_domain`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeUnificationCore.decode_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every p and t, existence of a successful decoded term is equivalent to exact native constructor shape together with original-variable support.

## References

- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.Presentation`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.Shape`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.Supported`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.decode_domain`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.decode_encode`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.decode_exact`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.encode`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.encodeGround`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.encode_decode`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.encode_injective`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.encode_shape`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.encode_supported`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.evaluate`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.finName`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.finPresentation`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.finitePresentation`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.leaf`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.nativeDecode`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.pair`
- Truth anchor: `D5/S0/Rewriting/NativeUnificationCore.transport`
