# Signed Bounds for Chronological Fibonacci Words

## Abstract

Every literal Fibonacci and swap word has a two-sided signed coefficient bound.

False is M with rows (0,1),(1,1); true is J with rows (0,1),(1,0). E(w) evaluates a finite chronological Boolean list. E(empty)=I and E(p followed by q)=E(q)E(p). n is the literal list length.

D=E(w)22-E(w)11. For n>=0 let L(n)=(n-1)/2 with natural truncated subtraction and integer division, and H(n)=(n+1)/2. e is either offdiagonal entry separately, not their sum or minimum.

**Theorem 1.1 (Both signs, both denominators, and integral chronology).**

$$\forall w, -\operatorname{L}\left(n\right)e \leq D \leq \operatorname{H}\left(n\right)e \land \operatorname{IntegralChronology}\left(w\right) \land \operatorname{AlternatingFormulas}\left(w\right) \land \operatorname{ShortestShearPrefix}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SelfCalibratingRawWords.raw_word_signed_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bound holds for every raw list, including adjacent JJ, MM, and empty lists. IntegralChronology means every entry is nonnegative, det(E(w))=(-1)^n, and E(w followed by q)=E(q)E(w) for every q. A zero chosen offdiagonal forces D=0; no division is used.

For alternating words of length 2j, starting with M gives rows (1,j),(0,1), and starting with J gives rows (1,0),(j,1). At length 2j+1 the corresponding rows are (0,1),(1,j+1) and (j,1),(1,0). These formulas include j=0.

An equal JJ pair removes two letters without changing its matrix. An MM pair uses M squared = M+I, giving a sum of two strictly shorter generated words. Their signed inequalities widen to the original length and add separately for each denominator. An exhaustive adjacent-pair decomposition leaves the alternating cases. Algebraic rewrites do not refund actions already executed.

For either shear U^k or V^k, with k>0, every literal representation has length at least 2k. Remove JJ pairs. A remaining MM pair gives a strictly positive matrix: each surrounding nonnegative invertible word has a nonzero row and column, and M squared is strictly positive. This contradicts the shear zero. The exhaustive alternating forms then force even length 2k.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SelfCalibratingRawWords.raw_word_signed_bound`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](GraftAffineClosure.md)
