# Residual Permutation Sign Cancellation

## Abstract

Interlaced prefix intervals have signed permutation sum supported only at identity.

Let a and b permute the positive integers from 1 to n. Write A and B for their prefix sums, starting at zero. The Lean permutations act on Fin n, so each value is increased by one when forming a prefix sum. The empty permutation is included. All sums of parity signs below take values in the integers.

**Definition 1.1 (Positive prefix sums).**

$$\operatorname {prefixSum}\left(p, k\right) = \sum _ {0 \le j < n , j < k} ( \operatorname {p}\left(j\right) + 1 )$$

*Formalization.* `D5/S1/Words/Compositions/ResidualPermutationSign.prefixSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *A392714 round two — the residual signed sum S(a)*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The argument k is a prefix length. The summation includes exactly the indices j in Fin n with j less than k.

**Definition 1.2 (Upper bounds).**

$$\operatorname {Upper}\left(a, b\right) \iff \forall i , 0 \le i \le n \implies B _ {i} \le A _ {i}$$

*Formalization.* `D5/S1/Words/Compositions/ResidualPermutationSign.Upper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *A392714 round two — the residual signed sum S(a)*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Upper compares all prefix sums up to length n.

**Definition 1.3 (Remaining lower bounds).**

$$\operatorname {LowerFrom}\left(a, b, r\right) \iff \forall i , r < i \le n \implies A _ {i - 1} < B _ {i}$$

*Formalization.* `D5/S1/Words/Compositions/ResidualPermutationSign.LowerFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *A392714 round two — the residual signed sum S(a)*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Here i is the one-based prefix length. LowerFrom r retains the strict lower cuts at lengths r+1 through n.

**Definition 1.4 (Integer parity sign).**

$$\operatorname {signInt}\left(b\right) = \operatorname {sign}\left(b\right)$$

*Formalization.* `D5/S1/Words/Compositions/ResidualPermutationSign.signInt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *A392714 round two — the residual signed sum S(a)*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The usual permutation sign is coerced to the integers.

**Definition 1.5 (Signed sum with initial lower cuts removed).**

$$R _ {r} ( a ) = \sum _ {b \in S _ {n} : \operatorname {Upper}\left(a, b\right) \land \operatorname {LowerFrom}\left(a, b, r\right)} \operatorname {sign}\left(b\right)$$

*Formalization.* `D5/S1/Words/Compositions/ResidualPermutationSign.rowSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *A392714 round two — the residual signed sum S(a)*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

R at r sums over all b with every upper bound and the lower bounds remaining from r onward.

**Theorem 1.6 (Removing one lower cut).**

$$\forall r \in \mathbb {N} , R _ {r} ( a ) = R _ {r + 1} ( a )$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ResidualPermutationSign.lower_cut_removal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *A392714 round two — the residual signed sum S(a)*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For r=0 positivity makes the first cut automatic. For 0<r<n the newly admitted terms have B at r+1 at most A at r. Swap positions r and r+1, using one-based positions. Only the prefix of length r changes, and it remains at most B at r+1. Later lower bounds are unchanged. This fixed transposition pairs the new terms with opposite signs. For r at least n there is no remaining cut.

**Theorem 1.7 (Cancelling the upper-bound class).**

$$a \neq id \implies \sum _ {b \in S _ {n} : \operatorname {Upper}\left(a, b\right)} \operatorname {sign}\left(b\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ResidualPermutationSign.upper_sum_vanish` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *A392714 round two — the residual signed sum S(a)*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Choose the least moved index k of a, and let j>k be the position of value k. Every upper-admissible b fixes the indices before k. The entries at positions j-1 and j are therefore at least k. Swapping these positions preserves the only affected upper bound, since B at j is at most A at j-1 plus k. This transposition is independent of b and reverses its sign.

**Definition 1.8 (The interlaced intervals).**

$$\operatorname {InResidual}\left(a, b\right) \iff \forall i , 1 \le i \le n \implies A _ {i - 1} < B _ {i} \le A _ {i}$$

*Formalization.* `D5/S1/Words/Compositions/ResidualPermutationSign.InResidual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *A392714 round two — the residual signed sum S(a)*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

This is precisely membership in L(a). The left inequality is strict and the right inequality is weak.

**Theorem 1.9 (The residual sign identity).**

$$\sum _ {b \in S _ {n} : \operatorname {InResidual}\left(a, b\right)} \operatorname {sign}\left(b\right) = [ a = id ]$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ResidualPermutationSign.signed_residual_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *A392714 round two — the residual signed sum S(a)*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The brackets denote 1 when a is the identity and 0 otherwise. Iterate lower-cut removal to reduce the sum to Upper. For the identity, the smallest unused positive value at each position forces b to be the identity. For any other a the upper sum vanishes by the fixed transposition just constructed. This proves the identity for every n and every a, without additional hypotheses.

## References

- Truth anchor: `D5/S1/Words/Compositions/ResidualPermutationSign.InResidual`
- Truth anchor: `D5/S1/Words/Compositions/ResidualPermutationSign.LowerFrom`
- Truth anchor: `D5/S1/Words/Compositions/ResidualPermutationSign.Upper`
- Truth anchor: `D5/S1/Words/Compositions/ResidualPermutationSign.lower_cut_removal`
- Truth anchor: `D5/S1/Words/Compositions/ResidualPermutationSign.prefixSum`
- Truth anchor: `D5/S1/Words/Compositions/ResidualPermutationSign.rowSum`
- Truth anchor: `D5/S1/Words/Compositions/ResidualPermutationSign.signInt`
- Truth anchor: `D5/S1/Words/Compositions/ResidualPermutationSign.signed_residual_sum`
- Truth anchor: `D5/S1/Words/Compositions/ResidualPermutationSign.upper_sum_vanish`
