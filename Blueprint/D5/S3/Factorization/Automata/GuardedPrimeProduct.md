# The Minimal Guarded Prime-Product DFAO

## Abstract

Every divisor is a distinct predictive state for actual prime-product capacity checks.

Fix a positive natural N with at least one prime divisor. Inputs are the actual prime divisors of N. A finite input word is evaluated as their integer product. The requested Boolean output is whether that product divides N, so an exponent overflow is rejected rather than silently clipped. These are multiplication instructions, not binary or Zeckendorf digits of the final integer.

Alphabet(N) is the subtype of Nat.primeFactors(N), Live(N) is the subtype of Nat.divisors(N), value is the mapped List product, and target is the Boolean divisibility test. The actual machine starts at the divisor 1. From d on input p it moves to d*p if d*p divides N, otherwise to the absorbing state none. Every live state outputs true and none outputs false.

**Theorem 1.1 (Correctness and the exact total-state minimum).**

$$\forall N \in \mathbb{N}, \forall hN: N \neq 0, \forall p: \operatorname{Alphabet}(N), (\forall w: \operatorname{List}(\operatorname{Alphabet}(N)), \operatorname{evalOutput}(\operatorname{machine}(hN), w) = \operatorname{target}(N, w)) \land \operatorname{card}(\operatorname{Option}(\operatorname{Live}(N))) = \operatorname{card}(\operatorname{divisors}(N)) + 1 \land (\forall S: Type, \operatorname{Fintype}(S) \Rightarrow \forall M: \operatorname{DFAO}(\operatorname{Alphabet}(N), Bool, S), (\forall w: \operatorname{List}(\operatorname{Alphabet}(N)), \operatorname{evalOutput}(M, w) = \operatorname{target}(N, w)) \Rightarrow \operatorname{card}(\operatorname{divisors}(N)) + 1 \leq \operatorname{card}(S))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/GuardedPrimeProduct.arithmetic_dfao_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public theorem states all-word correctness of the constructed DFAO, the cardinality of its explicit Option(Live(N)) state carrier, and the matching lower bound for every finite DFAO correct on the same entire prime-word domain. The supplied prime input witnesses the nonempty alphabet; N=1 is not incorrectly assigned a reachable reject state over an empty alphabet.

Each divisor d has an actual prime-factor word. For live d and e, the continuation encoding N/d is accepted from e exactly when e divides d: cancel the positive common factor N/d. If d and e differ, one of the two complements separates them. The word encoding N followed by any alphabet prime reaches rejection, which differs from every live state already on the empty continuation. These witnesses instantiate the existing DFAOStateLowerBound owner.

For N=5040 this yields 60 live states and one rejecting state, hence 61 total states, all encodable in six bits. The theorem does not assert a universally optimal computer, a runtime bound, or that Zeckendorf storage creates the state lower bound. The 60-state partial machine and its 61-state totalization have different carriers.

## References

- Truth anchor: `D5/S3/Factorization/Automata/GuardedPrimeProduct.arithmetic_dfao_minimality`
- Dependency: [D5/S0/Automata/DFAOStateLowerBound](../../../S0/Automata/DFAOStateLowerBound.md)
