# The Code Fixed-Point Theorem

## Abstract

Every computable transformation of partial recursive codes fixes some code's behavior.

**Theorem 1.1 (Computable code transformations fix a behavior).**

$$F:\operatorname{Code}\to \operatorname{Code}\ \text{computable}\Rightarrow \exists e, \operatorname{eval}(e) = \operatorname{eval}(F(e)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/CodeFixedPoint.code_fixed_point` (`✓ std3`). ∎

*Citation.* Stephen Cole Kleene (1938). *On notation for ordinal numbers*. DOI: [10.2307/2267778](https://doi.org/10.2307/2267778).

*Commentary.*

For every computable total transformation of partial recursive codes there is a code whose described program behaves exactly as the program described by the transformed code. The transformation may rewrite programs arbitrarily - permute them, pad them, or replace them wholesale - yet as long as it is itself computable, it cannot change every behavior: some program is semantically indistinguishable from its own image. This is the recursion-theoretic fixed point that powers self-referential program constructions, and it is deposited here as the kernel form of the fixed-point principle for computable code transformations.

The library was searched before proving: the pinned Mathlib already holds this statement as its fixed-point theorem on partial recursive codes, next to the second recursion theorem derived from it. The Lean declaration is therefore a declared thin honest wrapper: it applies the upstream theorem and restates the equality with the fixed code on the left. The classical construction behind the upstream proof is the diagonal self-application of a substitution code recorded in the attested note.

**Theorem 1.2 (Consecutive code numerals share a behavior).**

$$\exists e, \operatorname{eval}(e) = \operatorname{eval}(\operatorname{ofNat}(\operatorname{encode}(e)+1)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/CodeFixedPoint.exists_consecutive_codes_equal_behavior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed point is instantiated at a concrete nontrivial transformation: decode a code to its numeral, add one, and re-encode. That successor transformation is computable, so some pair of consecutive code numerals describes one and the same partial function - the standard numbering of programs repeats a behavior at adjacent addresses. The instantiation keeps the wrapper honest: the wrapped theorem is quantified over all computable transformations, and this witness exercises it on one that moves every code. The application is classical folklore; its formal statement here is derived in the repository from the wrapped theorem, so it is conservatively recorded as repository-derived.

## References

- Truth anchor: `D5/S0/Computability/CodeFixedPoint.code_fixed_point`
- Truth anchor: `D5/S0/Computability/CodeFixedPoint.exists_consecutive_codes_equal_behavior`
