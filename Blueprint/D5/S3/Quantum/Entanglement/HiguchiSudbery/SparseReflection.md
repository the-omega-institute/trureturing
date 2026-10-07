# SparseReflection

## Abstract

Sparse monomials are lists of variable indices with integer coefficients. The fuelled sorting laws ref_mergeFuel_perm and ref_sortFuel_perm preserve permutations. The laws ref_eval_termMul and ref_eval_mul show that evaluation respects products. The variables ref_vars pair each amplitude with its conjugate; ref_eval_swap and ref_eval_swap_vars identify index swapping with complex conjugation. The norm polynomial ref_normPoly, cubic forms ref_q0 through ref_q271, and minor polynomials ref_m0 through ref_m47 give the exact certificate data.

**Definition 1.1 (Merging with bounded fuel).**

$$\forall (\alpha : \operatorname{Type}*), (\forall (le : \alpha \to \left(\alpha \to \operatorname{Bool}\right)), ((\forall (p : \operatorname{List}\left(\alpha\right)), (\forall (q : \operatorname{List}\left(\alpha\right)), (\operatorname{ref_{mergeFuel}}\left(le, 0, p, q\right) = p++q))) \land ((\forall (n : \operatorname{Nat}), (\forall (q : \operatorname{List}\left(\alpha\right)), (\operatorname{ref_{mergeFuel}}\left(le, n+1, [], q\right) = q))) \land ((\forall (n : \operatorname{Nat}), (\forall (p : \operatorname{List}\left(\alpha\right)), (\operatorname{ref_{mergeFuel}}\left(le, n+1, p, []\right) = p))) \land (\forall (n : \operatorname{Nat}), (\forall (x : \alpha), (\forall (xs : \operatorname{List}\left(\alpha\right)), (\forall (y : \alpha), (\forall (ys : \operatorname{List}\left(\alpha\right)), (\operatorname{ref_{mergeFuel}}\left(le, n+1, x::xs, y::ys\right) = \operatorname{if} (le\left(x, y\right)) \operatorname{then} (x::\operatorname{ref_{mergeFuel}}\left(le, n, xs, y::ys\right)) \operatorname{else} (y::\operatorname{ref_{mergeFuel}}\left(le, n, x::xs, ys\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/HiguchiSudbery/SparseReflection.ref_mergeFuel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four equations are the defining clauses, in order. Type* permits any universe. The comparator returns Bool; the conditional tests that Boolean value. At zero fuel the lists are appended, and at successor fuel one head is selected whenever both lists are nonempty.

**Theorem 1.2 (Merging preserves the input permutation).**

$$\forall (\alpha : \operatorname{Type}*), (\forall (le : \alpha \to \left(\alpha \to \operatorname{Bool}\right)), (\forall (n : \operatorname{Nat}), (\forall (p : \operatorname{List}\left(\alpha\right)), (\forall (q : \operatorname{List}\left(\alpha\right)), (\operatorname{List.Perm}\left(\operatorname{ref_{mergeFuel}}\left(le, n, p, q\right), p++q\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/HiguchiSudbery/SparseReflection.ref_mergeFuel_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every comparator, fuel and pair of lists, ref_mergeFuel produces a List.Perm of their concatenation. No ordering or comparator laws are assumed. Induction on the fuel treats the two selected-head branches and the exhausted-fuel clause.

Sparse monomials are lists of variable indices with integer coefficients. The fuelled sorting laws ref_mergeFuel_perm and ref_sortFuel_perm preserve permutations. The laws ref_eval_termMul and ref_eval_mul show that evaluation respects products. The variables ref_vars pair each amplitude with its conjugate; ref_eval_swap and ref_eval_swap_vars identify index swapping with complex conjugation. The norm polynomial ref_normPoly, cubic forms ref_q0 through ref_q271, and minor polynomials ref_m0 through ref_m47 give the exact certificate data.

The prime encoding represents monomial keys by products of primes. The function prime_decodeTable reads blocks of sixteen base-2^60 words, with signed coefficients in their lowest 21 bits. This module holds the shared encoding definitions and the data and kernel checks for chunks 4 through 11, 18, and 48 through 55. PrimeReflection proves the prime evaluation laws, and PrimeHierarchyCertificate consumes the checked chunks in prime_eval_combined.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/SparseReflection.ref_mergeFuel`
- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/SparseReflection.ref_mergeFuel_perm`
