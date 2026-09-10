# Pell and Companion Pell Gcd

## Abstract

Coprimality and oddness of companion Pell numbers prove the gcd formula in OEIS A084068.

All indices and sequence values are natural numbers. The companion convention is Q(0)=Q(1)=1. OEIS A084068 records Joseph A. Stocke's July 28, 2025 conjecture that its n-th term equals gcd(A001108(n), A001109(n)), for n at least one.

**Definition 1.1 (Pell numbers).**

$$\begin{aligned}\operatorname{P}\left(0\right) = 0, \operatorname{P}\left(1\right) = 1,\\\forall n \in \mathbb{N}, \operatorname{P}\left(n + 2\right) = 2 \cdot \operatorname{P}\left(n + 1\right) + \operatorname{P}\left(n\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/PellCompanionGcd.P` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Joseph A. Stocke (2025). *OEIS A084068 gcd conjecture*. URL: <https://oeis.org/A084068>.

*Commentary.*

These are the Pell numbers A000129, beginning 0, 1, 2, 5, 12.

**Definition 1.2 (Companion Pell numbers).**

$$\begin{aligned}\operatorname{Q}\left(0\right) = 1, \operatorname{Q}\left(1\right) = 1,\\\forall n \in \mathbb{N}, \operatorname{Q}\left(n + 2\right) = 2 \cdot \operatorname{Q}\left(n + 1\right) + \operatorname{Q}\left(n\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/PellCompanionGcd.Q` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Joseph A. Stocke (2025). *OEIS A084068 gcd conjecture*. URL: <https://oeis.org/A084068>.

*Commentary.*

These are the companion Pell numbers A001333, beginning 1, 1, 3, 7, 17.

**Lemma 1.3 (The coupled recurrence).**

$$\forall n \in \mathbb{N}, \operatorname{P}\left(n + 1\right) = \operatorname{P}\left(n\right) + \operatorname{Q}\left(n\right) \land \operatorname{Q}\left(n + 1\right) = 2 \cdot \operatorname{P}\left(n\right) + \operatorname{Q}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PellCompanionGcd.pell_companion_step` (`✓ std3`). ∎

*Citation.* OEIS Foundation Inc.; Joseph A. Stocke (2025). *OEIS A084068 gcd conjecture*. URL: <https://oeis.org/A084068>.

*Commentary.*

Induct on n. The initial pair gives the base case. Substitute the two second-order recurrences at n+2 and the two induction identities; both equalities follow by addition. The same coupled recurrence is recorded in the Stephenson and Koch comment on A001108.

**Lemma 1.4 (Coprimality at every index).**

$$\forall n \in \mathbb{N}, \operatorname{gcd}\left(\operatorname{P}\left(n\right), \operatorname{Q}\left(n\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PellCompanionGcd.pell_companion_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Joseph A. Stocke (2025). *OEIS A084068 gcd conjecture*. URL: <https://oeis.org/A084068>.

*Commentary.*

The initial pair (0,1) is coprime. The coupled step sends (p,q) to (p+q,2p+q). Subtracting the first coordinate from the second, and then p from p+q, shows gcd(p+q,2p+q)=gcd(q,p). Induction gives coprimality for every index.

**Lemma 1.5 (Oddness at every index).**

$$\forall n \in \mathbb{N}, \exists k \in \mathbb{N}, \operatorname{Q}\left(n\right) = 2 \cdot k+1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PellCompanionGcd.companion_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Joseph A. Stocke (2025). *OEIS A084068 gcd conjecture*. URL: <https://oeis.org/A084068>.

*Commentary.*

Q(0)=1 is odd. If Q(n)=2k+1, then Q(n+1)=2P(n)+Q(n) equals 2(P(n)+k)+1, so the next value is odd too.

**Theorem 1.6 (The A084068 gcd formula).**

$$\begin{aligned}\forall n \in \mathbb{N}, \\\operatorname{gcd}\left(\operatorname{if} 2 \mid n \operatorname{then} 2 \cdot \operatorname{P}\left(n\right)^{2} \operatorname{else} \operatorname{Q}\left(n\right)^{2}, \operatorname{P}\left(n\right) \cdot \operatorname{Q}\left(n\right)\right) = \operatorname{if} 2 \mid n \operatorname{then} \operatorname{P}\left(n\right) \operatorname{else} \operatorname{Q}\left(n\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PellCompanionGcd.pell_companion_gcd` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a084068-pell-companion-gcd` (proved) by `D5/S1/Recurrence/PellCompanionGcd.pell_companion_gcd`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a084068-pell-companion-gcd","declaration_gid":"D5/S1/Recurrence/PellCompanionGcd.pell_companion_gcd","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Joseph A. Stocke (2025). *OEIS A084068 gcd conjecture*. URL: <https://oeis.org/A084068>.

*Commentary.*

For even n, extract P(n) from both gcd arguments. Since Q(n) is odd, it is coprime to 2; since it is coprime to P(n), it is coprime to 2P(n). The remaining gcd is therefore 1. For odd n, extract Q(n); the remaining gcd is gcd(Q(n),P(n))=1. A001108 gives the first gcd argument by parity, A001109 gives the product P(n)Q(n), and A084068 gives P(n) at even indices and Q(n) at odd indices. Thus this proves the conjecture at every positive index; the displayed equality also holds at zero.

## References

- Truth anchor: `D5/S1/Recurrence/PellCompanionGcd.P`
- Truth anchor: `D5/S1/Recurrence/PellCompanionGcd.Q`
- Truth anchor: `D5/S1/Recurrence/PellCompanionGcd.companion_odd`
- Truth anchor: `D5/S1/Recurrence/PellCompanionGcd.pell_companion_coprime`
- Truth anchor: `D5/S1/Recurrence/PellCompanionGcd.pell_companion_gcd`
- Truth anchor: `D5/S1/Recurrence/PellCompanionGcd.pell_companion_step`
