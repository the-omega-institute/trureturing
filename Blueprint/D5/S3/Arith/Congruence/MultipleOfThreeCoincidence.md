# Multiple-of-Three Residue Coincidences

## Abstract

The modulo-three coincidence occurs exactly for composites other than 4, 8, 10, and 25.

**Definition 1.1 (The coincidence predicate).**

$$\forall k: \mathbb{N}, \operatorname{Coincides}\left(k\right) \iff (\exists m: \mathbb{N}, 6 \le m \land m \le k \land 3 \mid m \land 3\cdot\operatorname{mod}\left(2\cdot k, m\right) = m\cdot\operatorname{mod}\left(2\cdot k, 3\right))$$

*Formalization.* `D5/S3/Arith/Congruence/MultipleOfThreeCoincidence.Coincides` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A387319*. URL: <https://oeis.org/A387319>.

*Commentary.*

For every natural k, compare the fractions (2k mod m)/m at m=3 and another positive multiple of three no larger than k. The latter modulus is at least six. Cross multiplication is valid because both denominators are positive. Zero-valued coincidences are included, for example at k=6 and m=6.

**Theorem 1.2 (The complete classification).**

$$\forall k: \mathbb{N}, \operatorname{Coincides}\left(k\right) \iff (1 < k \land \neg\operatorname{Prime}\left(k\right) \land \neg(k \in \{4,8,10,25\}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/MultipleOfThreeCoincidence.classify` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a387319-multiple-of-three-coincidence` (proved) by `D5/S3/Arith/Congruence/MultipleOfThreeCoincidence.classify`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a387319-multiple-of-three-coincidence","declaration_gid":"D5/S3/Arith/Congruence/MultipleOfThreeCoincidence.classify","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A387319*. URL: <https://oeis.org/A387319>.

*Commentary.*

Write m=3t. Coincidence is equivalent to t dividing 2k and the quotient having the same residue modulo three as 2k, with 2<=t and 3t<=k. A divisor congruent to one modulo three satisfies the residue condition. Multiples of three use t=2; remaining even composites use t=4. For odd composites write k=pq with p the least prime factor. Then q>=p>=5, and take t=p or t=2p according to p modulo three. The latter bound fails only at p=q=5. For prime k the divisor criterion forces t=2 and 3|k, contradicting the modulus bound. The four exceptional composites are excluded directly. The theorem includes k=0 and k=1, for which both sides are false.

## References

- Truth anchor: `D5/S3/Arith/Congruence/MultipleOfThreeCoincidence.Coincides`
- Truth anchor: `D5/S3/Arith/Congruence/MultipleOfThreeCoincidence.classify`
