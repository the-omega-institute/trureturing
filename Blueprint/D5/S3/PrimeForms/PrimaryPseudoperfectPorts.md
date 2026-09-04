# Primary Pseudoperfect Ports

## Abstract

Primary pseudoperfect numbers admit equivalent reciprocal and integral forms, a coprime Leibniz rule, a compositional port residual, and explicit companions.

For a natural number n, squarefreeDeriv(n) is the sum of n/p over its prime factors, IsPPN(n) means that n is squarefree, exceeds one, and equals 1 + squarefreeDeriv(n), and portDelta(R,c,B) is the natural-number difference cB - R squarefreeDeriv(B).

**Theorem 1.1 (Reciprocal and integral characterizations).**

$$\forall n \in \mathbb{N}, {n \neq 0 \Rightarrow (\frac{1}{n} + \sum_{p \in \operatorname{primeFactors}\left(n\right)} \frac{1}{p} = 1 \iff n = 1 + \operatorname{squarefreeDeriv}\left(n\right))} \land {(\operatorname{IsPPN}\left(n\right) \iff \operatorname{Squarefree}\left(n\right) \land 1 < n \land \frac{1}{n} + \sum_{p \in \operatorname{primeFactors}\left(n\right)} \frac{1}{p} = 1)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.reciprocal_eq_one_and_isPPN_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero n, multiplication by n converts the prime-factor reciprocal sum into squarefreeDeriv(n). The same equivalence, combined with squarefreeness and n > 1, characterizes IsPPN.

**Theorem 1.2 (Coprime Leibniz rule).**

$$\forall A, B \in \mathbb{N}, \operatorname{Coprime}\left(A, B\right) \Rightarrow \operatorname{squarefreeDeriv}\left(A \cdot B\right) = A \cdot \operatorname{squarefreeDeriv}\left(B\right) + B \cdot \operatorname{squarefreeDeriv}\left(A\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coprimality partitions the prime factors of AB into disjoint factors from A and B. Transporting complementary divisors across that partition gives the two Leibniz terms.

**Theorem 1.3 (Port composition law).**

$$\forall A, B, R, c \in \mathbb{N}, \operatorname{Coprime}\left(A, B\right) \Rightarrow \operatorname{portDelta}\left(R, c, A \cdot B\right) = \operatorname{portDelta}\left(R \cdot A, \operatorname{portDelta}\left(R, c, A\right), B\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.portDelta_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On coprime factors, the Leibniz rule makes the residual through AB equal to the residual obtained by substituting the output at A as the input coefficient at B.

**Theorem 1.4 (Coprime extension criterion).**

$$\forall K, C \in \mathbb{N}, \operatorname{IsPPN}\left(K\right) \land \operatorname{Squarefree}\left(C\right) \land 1 < C \land \operatorname{Coprime}\left(K, C\right) \Rightarrow (\operatorname{IsPPN}\left(K \cdot C\right) \iff C - K \cdot \operatorname{squarefreeDeriv}\left(C\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.isPPN_mul_iff_port` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If K is primary pseudoperfect and C is a nontrivial squarefree factor coprime to K, then KC is primary pseudoperfect exactly when the natural residual C - K squarefreeDeriv(C) equals one.

**Theorem 1.5 (One-prime and two-prime companions and the numeric chain).**

$${\forall K \in \mathbb{N}, \operatorname{IsPPN}\left(K\right) \land \operatorname{Prime}\left(K + 1\right) \Rightarrow \operatorname{IsPPN}\left(K \cdot \left(K + 1\right)\right)} \land {\forall K, p, q \in \mathbb{N}, \operatorname{IsPPN}\left(K\right) \land \operatorname{Prime}\left(p\right) \land \operatorname{Prime}\left(q\right) \land p \neq q \land \neg {p \mid K} \land \neg {q \mid K} \land K < p \land K < q \Rightarrow (\operatorname{IsPPN}\left(K \cdot p \cdot q\right) \iff \left(p - K\right) \cdot \left(q - K\right) = {K}^2 + 1)} \land {\operatorname{IsPPN}\left(2\right) \land \operatorname{IsPPN}\left(6\right) \land \operatorname{IsPPN}\left(42\right) \land \operatorname{IsPPN}\left(1806\right) \land \operatorname{IsPPN}\left(47058\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.isPPN_companions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bundled statement records the Euclid-style K(K+1) step, the two-prime factored port criterion in the K < p,q natural-number domain, and the checked chain 2, 6, 42, 1806, 47058.

## References

- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.isPPN_companions`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.isPPN_mul_iff_port`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.portDelta_mul`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.reciprocal_eq_one_and_isPPN_iff`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv_mul`
