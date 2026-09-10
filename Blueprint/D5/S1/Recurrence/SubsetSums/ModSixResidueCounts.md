# The Residue Table and Corneth's Correction Recurrence

## Abstract

The complete residue table proves Corneth's second recurrence for OEIS A068012.

C and a are the definitions from the frozen module D5/S1/Recurrence/Parity/SubsetSumModSixDoubling: C(m,r) counts subsets of the interval from one to m with sum r in ZMod 6, and a(m)=C(m,0). That module already proves the doubling recurrence. Here the full residue table proves the second recurrence in Corneth's September 13, 2025 FORMULA contribution to OEIS A068012.

Indices m and k, counts, and powers are natural numbers. The residue r lies in ZMod 6; constants compared with r belong to that ring. The operator div is integer division, mod is remainder, and subtraction in an exponent is truncated natural subtraction. The conditional expressions below have propositions as branches.

**Theorem 1.1 (The complete residue table).**

$$\forall m: \mathbb{N}, 3 \le m \implies \forall r \in \operatorname{ZMod}\left(6\right), \operatorname{if} (m \bmod 3 = 1) \operatorname{then} (\operatorname{if} (r = 2 \lor r = 5) \operatorname{then} (6 \cdot \operatorname{C}\left(m, r\right) + 2 \cdot 2^{\operatorname{div}\left(m, 3\right)} = 2^{m}) \operatorname{else} (6 \cdot \operatorname{C}\left(m, r\right) = 2^{m} + 2^{\operatorname{div}\left(m, 3\right)})) \operatorname{else} (\operatorname{if} (r = 0 \lor r = 3) \operatorname{then} (6 \cdot \operatorname{C}\left(m, r\right) = 2^{m} + 2 \cdot 2^{\operatorname{div}\left(m, 3\right)}) \operatorname{else} (6 \cdot \operatorname{C}\left(m, r\right) + 2^{\operatorname{div}\left(m, 3\right)} = 2^{m}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/SubsetSums/ModSixResidueCounts.count_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At m=3 the six counts are 2,1,1,2,1,1. Natural-number induction propagates the table using the frozen count_succ recurrence. The quotient m div 3 increases exactly when m mod 3 is two, doubling the correction power. Splitting m modulo six and the six residues evaluates the shift in ZMod 6 and closes every inductive branch. The interval size has no upper bound.

**Theorem 1.2 (Corneth's second recurrence).**

$$\forall k: \mathbb{N}, 1 \le k \implies \operatorname{a}\left(3 \cdot k + 1\right) + 2^{k - 1} = 2 \cdot \operatorname{a}\left(3 \cdot k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/SubsetSums/ModSixResidueCounts.corneth_step` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a068012-correction-recurrence` (proved) by `D5/S1/Recurrence/SubsetSums/ModSixResidueCounts.corneth_step`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a068012-correction-recurrence","declaration_gid":"D5/S1/Recurrence/SubsetSums/ModSixResidueCounts.corneth_step","resolution_kind":"proved"} -->

*Citation.* OEIS Foundation Inc.; Antti Karttunen; David A. Corneth (2025). *OEIS A068012 subset sum doubling conjecture*. URL: <https://oeis.org/A068012>.

*Commentary.*

Apply the table at residue zero for 3k and 3k+1, then use 2^k=2*2^(k-1). Multiplying the desired identity by six makes the two table equations cancel. The correction is moved left, so the equality also establishes the nonnegativity required by the source's subtraction form.

## References

- Truth anchor: `D5/S1/Recurrence/SubsetSums/ModSixResidueCounts.corneth_step`
- Truth anchor: `D5/S1/Recurrence/SubsetSums/ModSixResidueCounts.count_closed_form`
- Dependency: [D5/S1/Recurrence/Parity/SubsetSumModSixDoubling](../Parity/SubsetSumModSixDoubling.md)
