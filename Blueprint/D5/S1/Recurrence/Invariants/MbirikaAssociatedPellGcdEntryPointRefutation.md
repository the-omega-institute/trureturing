# The Associated Pell GCD Entry-Point Conjecture

## Abstract

The value k = 12 refutes the printed associated Pell gcd-entry-point biconditional.

**Definition 1.1 (Mbirika-Schrader-Spilker Conjecture 32).**

$$(claim) \Leftrightarrow (\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow ((1 < \operatorname{gcd}\left(\operatorname{Q}\left(k\right), k\right)) \Leftrightarrow (\exists p \in \mathrm{Nat},\; (\operatorname{Prime}\left(p\right)) \land \left((p \mid k) \land (\exists r \in \mathrm{Nat},\; (0 < r) \land \left((p \mid \operatorname{Q}\left(r\right)) \land \left((\forall s \in \mathrm{Nat},\; (0 < s) \Rightarrow ((s < r) \Rightarrow (\neg (p \mid \operatorname{Q}\left(s\right))))) \land (r \mid k)\right)\right))\right))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation.claim` (`✓ std3`).

*Citation.* aBa Mbirika; Janee Schrader; Jürgen Spilker (2023). *Pell and Associated Pell Braid Sequences as GCDs of Sums of k Consecutive Pell, Balancing, and Related Numbers*. DOI: [10.48550/arXiv.2301.05758](https://doi.org/10.48550/arXiv.2301.05758). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL26/Mbirika/mbir5.pdf>.

*Commentary.*

Conjecture 32 states verbatim: "We claim that gcd(Q_k, k) > 1 if and only if there exists a prime p such that p divides k and the rank of apparition (or entry point), e_Q(p) divides k. For example, gcd(Q_21, 21) = 7 and for the prime p = 7, we have p divides 21 and e_Q(p) = 3 divides 21." The symbol Q is the associated Pell sequence already defined in D5/S1/Recurrence/PellCompanionGcd, with initial values one and one. The existential r expresses that the least positive index where p divides Q exists, and that this index divides k.

**Theorem 1.2 (The conjecture fails at k = 12).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika; Janee Schrader; Jürgen Spilker (2023). *Pell and Associated Pell Braid Sequences as GCDs of Sums of k Consecutive Pell, Balancing, and Related Numbers*. DOI: [10.48550/arXiv.2301.05758](https://doi.org/10.48550/arXiv.2301.05758). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL26/Mbirika/mbir5.pdf>.

*Commentary.*

At k = 12, Q(12) = 19601 and gcd(Q(12),12) = 1, so the left side is false. The prime p = 3 divides 12, its least positive entry point is r = 2 because Q(1) = 1 and Q(2) = 3, and 2 divides 12. Thus the right side is true and the biconditional is false.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation.result`
- Dependency: [D5/S1/Recurrence/PellCompanionGcd](../PellCompanionGcd.md)
