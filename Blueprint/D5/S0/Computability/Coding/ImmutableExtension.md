# Immutable Prefix-Code Extension

## Abstract

A frozen prefix code admits exactly the extensions certified by its depth-sensitive residual capacity profile.

Residual capacity remembers where frozen words sit in the prefix tree, not only their lengths or total Kraft mass. The first theorem computes that capacity exactly, and the second characterizes every feasible finite request multiset.

**Theorem 1.1 (Exact residual-capacity shadow identity).**

$$\forall q, n, C, \operatorname{IsPrefixFree}\left(C\right) \Rightarrow \Vert\operatorname{freeAt}\left(C, n\right)\Vert + \sum_{u \in C, \operatorname{length}\left(u\right) \leq n} q^{{n - \operatorname{length}\left(u\right)}} + \Vert\operatorname{longPrefixes}\left(C, n\right)\Vert = q^{n}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/ImmutableExtension.freeAt_shadow_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At depth n, all q^n words split into three classes: slots compatible with the frozen code, descendants of frozen words of length at most n, and depth-n prefixes of longer frozen words.

The last term is the cardinality of the image finset longPrefixes. Thus different long frozen words sharing the same depth-n prefix consume that slot once, which is the exact correction missing from a union bound.

**Theorem 1.2 (Depth capacity exactly characterizes immutable extension).**

$$\forall q, C, L, 2 \leq q, \operatorname{IsPrefixFree}\left(C\right) \Rightarrow (\exists xs, \operatorname{Extends}\left(C, L, xs\right)) \Leftrightarrow \forall n \in L, \operatorname{demand}\left(q, L, n\right) \leq \Vert\operatorname{freeAt}\left(C, n\right)\Vert.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/ImmutableExtension.extension_iff_depth_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a prefix-free code over q symbols, with q at least two, and let L be a multiset of requested new lengths. An exact extension exists if and only if the multiplicity-sensitive demand at every requested depth does not exceed the number of slots compatible with C.

Necessity counts disjoint cylinders of the requested words inside freeAt. For sufficiency, sort the requests and add a word at each new maximum depth; exact cylinder accounting supplies a free slot. Requests may be shorter than frozen words, and no frozen word is replaced.

## References

- Truth anchor: `D5/S0/Computability/Coding/ImmutableExtension.extension_iff_depth_capacity`
- Truth anchor: `D5/S0/Computability/Coding/ImmutableExtension.freeAt_shadow_identity`
- Dependency: [D5/S0/Computability/Coding/KraftConverse](KraftConverse.md)
- Dependency: [D5/S0/Computability/Coding/PrefixFreeCode](PrefixFreeCode.md)
