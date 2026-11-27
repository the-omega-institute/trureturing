# Two-sided recovery over arbitrary alphabets

## Abstract

Full output and literal-prefix coordinates over arbitrary alphabets.

Let A be any type and let h map blocks of length k+2 to A. Bipermutativity means that fixing all but the right endpoint gives a bijection A to A, and fixing all but the left endpoint also gives a bijection. For an integer configuration x, the output at i is h applied to the block x(i), through x(i+k+1). The prefix coordinate consists of the actual entries x(0), through x(k).

**Theorem 1.1 (Every output and prefix have exactly one source).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/ArbitraryBipermutative.coordinates_bijective`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/ArbitraryBipermutative.coordinates_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Z. Kang; T. Jäger (2026). *On lifts of strictly ergodic subshifts by permutative sliding block codes*. DOI: [10.48550/arXiv.2609.01140](https://doi.org/10.48550/arXiv.2609.01140). URL: <https://arxiv.org/abs/2609.01140v1>.

*Commentary.*

The map sending x to its entire coded output together with its literal length k+1 prefix is bijective. Equivalently, for every output y indexed by the integers and every prefix p indexed by Fin(k+1), there is exactly one integer configuration x with code h x = y and sourcePrefix x = p. The alphabet may be empty or infinite, and k may be zero. No nonemptiness, finite enumeration, decidable equality, topology, or preassigned trajectory is required.

For a prescribed output letter a and a proposed next prefix v, solve the left-end equation h(cons(b,v)) = a. The preceding prefix is cons(b,init(v)). Appending the last letter of v produces the same block cons(b,v); right-end uniqueness therefore makes the native prefix step send this preceding prefix to v. The existing left-end argument also makes that step injective. Thus every output letter acts by a genuine permutation on the prefix set, even for an infinite alphabet.

The shared reconstruction iterates the skew product of output shift and prefix permutation at every signed integer. Neighboring prefixes overlap. Reading their first entries gives a single physical source configuration, whose windows yield the prescribed output and whose prefix is p. Applying the same orbit identities to an existing source proves uniqueness. The finite-alphabet equivalence uses this same reconstruction.

Theorem 1.3 of the cited finite-alphabet source supplies the finite context for output and prefix coordinates. The arbitrary-alphabet statement here is a set-theoretic extension; it is not attributed to that theorem, and no priority claim is made. The conclusion gives neither continuity nor a one-sided causal inverse, a complexity bound, or a classification of local rules. The equivalences use classical choice to select local inverse letters.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/ArbitraryBipermutative.coordinates_bijective`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift](BipermutativeLift.md)
