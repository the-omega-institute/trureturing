# Complete Palindrome Cut Bit Relation

## Abstract

Every nonempty literal palindrome cut has an accepting run in the bit relation.

**Definition 1.1 (The relation before adding arithmetic memories).**

$$\left((\operatorname{start}\left(cutBitAutomaton\right) = \operatorname{univ}\left(\mathbb{Z}\right)) \land (\forall s \in \mathbb{Z},\; \forall a \in \mathbb{N} \times \mathbb{N},\; \operatorname{step}\left(cutBitAutomaton, s, a\right) = \{t:\mathbb{Z} | t \in \operatorname{relNext}\left(s, \operatorname{cast}\left(\operatorname{fst}\left(a\right), \mathbb{Z}\right), \operatorname{cast}\left(\operatorname{snd}\left(a\right), \mathbb{Z}\right)\right)\})\right) \land (\operatorname{accept}\left(cutBitAutomaton\right) = \{0\})$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/CutBitRelation.cutBitAutomaton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state is an integer relation label; an input is a pair of natural binary digits. Every state is allowed as a starting state in this auxiliary automaton, and only state zero accepts. The cut theorem specifies the actual source choices after consuming the lowest endpoint bits. relNext is the original nine-state transition table.

**Theorem 1.2 (All actual palindrome cuts are represented).**

$$\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \left(j < n \land \operatorname{Palindrome}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(\operatorname{NatSub}\left(n, j\right)\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(j + \operatorname{val}\left(i\right)\right)\right)\right)\right) \Rightarrow \left(\exists r \in \mathbb{Z},\; \exists xs \in \operatorname{List}\left(\mathbb{N} \times \mathbb{N}\right),\; \left(\left(\left(r \in \operatorname{ite}\left(\operatorname{mod}\left(n, 2\right) = \operatorname{mod}\left(j, 2\right), [6], \operatorname{ite}\left(\operatorname{mod}\left(j, 2\right) < \operatorname{mod}\left(n, 2\right), [1, 2, 0], [1, 2]\right)\right) \land \operatorname{Nonempty}\left(\operatorname{Path}\left(cutBitAutomaton, r, 0, xs\right)\right)\right) \land \operatorname{foldr}\left(\lambda a:\mathbb{N} \times \mathbb{N} x:\mathbb{N} \mapsto \operatorname{fst}\left(a\right) + 2 \cdot x, 0, xs\right) = \operatorname{div}\left(n, 2\right)\right) \land \operatorname{foldr}\left(\lambda a:\mathbb{N} \times \mathbb{N} x:\mathbb{N} \mapsto \operatorname{snd}\left(a\right) + 2 \cdot x, 0, xs\right) = \operatorname{div}\left(j, 2\right)\right) \land \left(\forall a \in \mathbb{N} \times \mathbb{N},\; a \in xs \Rightarrow \left(\operatorname{fst}\left(a\right) \le 1 \land \operatorname{snd}\left(a\right) \le 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/CutBitRelation.cut_bit_relation_completeness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonempty palindromic suffix from prefix j to prefix n, the remaining bit pairs have an accepting path to zero and encode div(n,2) and div(j,2). Equal endpoint parities choose the even-cut source 6; the pair (1,0) additionally permits the already-flushed source 0. Other odd cuts start in source 1 or 2. Every emitted input is zero or one. The proof uses the exact dyadic palindrome radius to construct the complementary A runs and the skipped-bit B runs, and the valuation parity to construct the even-00 runs. No bound is imposed on the length of these runs. div and mod denote natural integer quotient and remainder, and NatSub denotes truncated natural subtraction. This theorem concerns the bit relation; adjoining the signed-digit memories is a separate obligation.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/CutBitRelation.cutBitAutomaton`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/CutBitRelation.cut_bit_relation_completeness`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates](BaseCertificates.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/EvenPalindrome](EvenPalindrome.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/OddPalindromeRadius](OddPalindromeRadius.md)
