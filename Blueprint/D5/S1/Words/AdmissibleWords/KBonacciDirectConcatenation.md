# Direct concatenation without a separator

## Abstract

Direct concatenation of actual Boolean words has an exact run boundary condition and nested one-page neighborhoods.

A word of width m is a function from Fin m to Bool, read in increasing coordinate order. L(k,m,w) denotes DBonacciAdmissible k m w, the original scanner condition forbidding k consecutive true bits. The concatenation x ++ y is Fin.append x y and retains every bit. The natural widths may be zero. An all-true word contributes its entire width to its initial and terminal runs.

In the theorem, p(w) is (List.ofFn w).findIdx Bool.not, and t(w) is p applied to i mapped to w(Fin.rev i). B(k,n,s) is the finite set of legal true-starting width-n words with p(w) < k-s. These are local definitions; natural subtraction is truncated at zero and head(w) is the optional first bit.

**Theorem 1.1 (The exact interface law and all neighborhood clauses).**

$$(\forall (k,m,n:\mathbb{N}), (((2 \leq k) \implies ((((\forall (x:(\operatorname{Fin}\left(m\right) \to \operatorname{Bool})), ((\forall (y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (((((L\left(k, m, x\right)) \land (L\left(k, n, y\right)))) \implies (((t\left(x\right) < k) \land (p\left(y\right) < k) \land (L\left(k, m+n, x++y\right) \iff t\left(x\right)+p\left(y\right) < k))))))))) \land ((\forall (s,u:\mathbb{N}), (((s \leq u) \implies (B\left(k, n, u\right) \subseteq B\left(k, n, s\right)))))) \land (B\left(k, n, k-1\right) = \emptyset) \land ((\forall (x:(\operatorname{Fin}\left(m\right) \to \operatorname{Bool})), ((\forall (y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (((((L\left(k, m, x\right)) \land (L\left(k, n, y\right)))) \implies (((\operatorname{head}\left(y\right) = \operatorname{some}\left(\operatorname{false}\right)) \implies (L\left(k, m+n, x++y\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciDirectConcatenation.actual_direct_concatenation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A forbidden block inside either component is excluded by that component's scanner. A forbidden block crossing the interface requires k true bits drawn from the final run of x and the initial run of y. Conversely, when their sum reaches k, those actual positions supply a forbidden crossing block. This argument also covers words shorter than k and all-true words. A true-starting word has an initial run of at least one, so the neighborhood at k-1 is empty. A false-starting word has initial run zero and therefore connects to every legal x.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciDirectConcatenation.actual_direct_concatenation`
- Dependency: [D5/S1/Words/ClosedRunStarts](../ClosedRunStarts.md)
