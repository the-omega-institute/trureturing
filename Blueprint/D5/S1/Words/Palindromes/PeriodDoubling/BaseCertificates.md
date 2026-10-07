# Concrete Period-Doubling Transducer Potentials

## Abstract

The fully reconstructed finite graph has exact integer bounds on every accepted run.

**Definition 1.1 (The nine relation-state transitions).**

$$\forall r \in \mathbb{Z},\; \forall n \in \mathbb{Z},\; \forall j \in \mathbb{Z},\; \operatorname{relNext}\left(r, n, j\right) = \operatorname{ite}\left(r = 0, \operatorname{ite}\left(n = j, [0], []\right), \operatorname{ite}\left(r = 1, \operatorname{ite}\left(n = j, [], \operatorname{ite}\left(n = 1 \land j = 0, [1, 0], [1]\right)\right), \operatorname{ite}\left(r = 2, \operatorname{ite}\left(n = j, [3], [2]\right), \operatorname{ite}\left(r = 3, \operatorname{ite}\left(n = 0 \land j = 1, [4], []\right), \operatorname{ite}\left(r = 4, \operatorname{ite}\left(n = 1 \land j = 0, [0], \operatorname{ite}\left(n = 0 \land j = 1, [5], []\right)\right), \operatorname{ite}\left(r = 5, \operatorname{ite}\left(n = 0 \land j = 1, [4], []\right), \operatorname{ite}\left(r = 6, \operatorname{ite}\left(n = 0 \land j = 1, [7], []\right), \operatorname{ite}\left(r = 7, \operatorname{ite}\left(n = 1 \land j = 0, [0], \operatorname{ite}\left(n = 0 \land j = 1, [8], []\right)\right), \operatorname{ite}\left(r = 8, \operatorname{ite}\left(n = 0 \land j = 1, [7], []\right), []\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.relNext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

State 0 reads equal higher bits. State 1 reads complementary bits and may stop at (1,0). State 2 reads complementary lower bits, then one equal skipped bit to state 3. States 3,4,5 require a positive odd run of (0,1) before (1,0). States 6,7,8 impose the corresponding even-cut parity restriction. Inputs outside these nine relation states have no successors.

**Definition 1.2 (The literal arithmetic update).**

$$\forall s \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall n \in \mathbb{Z},\; \forall j \in \mathbb{Z},\; \forall r \in \mathbb{Z},\; \operatorname{baseNext}\left(s, n, j, r\right) = (\lambda nv:\mathbb{Z} \mapsto (\lambda jv:\mathbb{Z} \mapsto (\lambda xn:\mathbb{Z} \mapsto (\lambda xj:\mathbb{Z} \mapsto (\lambda nt:\mathbb{Z} \mapsto (\lambda jt:\mathbb{Z} \mapsto (\lambda nd:\mathbb{Z} \mapsto (\lambda jd:\mathbb{Z} \mapsto \operatorname{ite}\left(nd \cdot \operatorname{getD}\left(\operatorname{ite}\left(11 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 11\right)\right), \operatorname{none}\left(\right)\right), 0\right) = \operatorname{neg}\left(1\right), \operatorname{none}, \operatorname{some}\left(([r, 1 - \operatorname{getD}\left(\operatorname{ite}\left(1 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 1\right)\right), \operatorname{none}\left(\right)\right), 0\right), \operatorname{getD}\left(\operatorname{ite}\left(2 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 2\right)\right), \operatorname{none}\left(\right)\right), 0\right), \operatorname{getD}\left(\operatorname{ite}\left(3 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 3\right)\right), \operatorname{none}\left(\right)\right), 0\right), \operatorname{div}\left(nv, 2\right), \operatorname{div}\left(jv, 2\right), xn, xj, \operatorname{div}\left(nt, 2\right), \operatorname{div}\left(jt, 2\right), nd, \operatorname{getD}\left(\operatorname{ite}\left(10 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 10\right)\right), \operatorname{none}\left(\right)\right), 0\right), jd, \operatorname{getD}\left(\operatorname{ite}\left(12 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 12\right)\right), \operatorname{none}\left(\right)\right), 0\right), \operatorname{ite}\left(\operatorname{getD}\left(\operatorname{ite}\left(14 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 14\right)\right), \operatorname{none}\left(\right)\right), 0\right) = 0, nd, \operatorname{getD}\left(\operatorname{ite}\left(14 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 14\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right), \operatorname{ite}\left(\operatorname{getD}\left(\operatorname{ite}\left(15 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 15\right)\right), \operatorname{none}\left(\right)\right), 0\right) = 0, jd, \operatorname{getD}\left(\operatorname{ite}\left(15 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 15\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right), \operatorname{ite}\left(nd = 0, \operatorname{getD}\left(\operatorname{ite}\left(16 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 16\right)\right), \operatorname{none}\left(\right)\right), 0\right), nd\right), \operatorname{ite}\left(jd = 0, \operatorname{getD}\left(\operatorname{ite}\left(17 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 17\right)\right), \operatorname{none}\left(\right)\right), 0\right), jd\right), \operatorname{cast}\left(\operatorname{toNat}\left(\operatorname{Bool.or}\left((\operatorname{getD}\left(\operatorname{ite}\left(18 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 18\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0), (jd \cdot \operatorname{getD}\left(\operatorname{ite}\left(13 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 13\right)\right), \operatorname{none}\left(\right)\right), 0\right) == \operatorname{neg}\left(1\right))\right)\right), \mathbb{Z}\right)], \operatorname{cast}\left(\operatorname{toNat}\left((nd != 0)\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{toNat}\left((jd != 0)\right), \mathbb{Z}\right), \operatorname{ite}\left(jd = 0, 0, 1 + 2 \cdot \operatorname{getD}\left(\operatorname{ite}\left(1 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 1\right)\right), \operatorname{none}\left(\right)\right), 0\right) + \operatorname{cast}\left(\operatorname{toNat}\left(\operatorname{Bool.and}\left((\operatorname{getD}\left(\operatorname{ite}\left(17 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 17\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0), (\operatorname{getD}\left(\operatorname{ite}\left(17 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 17\right)\right), \operatorname{none}\left(\right)\right), 0\right) != jd)\right)\right), \mathbb{Z}\right)\right) - \operatorname{ite}\left(nd = 0, 0, 1 + 2 \cdot \operatorname{getD}\left(\operatorname{ite}\left(1 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 1\right)\right), \operatorname{none}\left(\right)\right), 0\right) + \operatorname{cast}\left(\operatorname{toNat}\left(\operatorname{Bool.and}\left((\operatorname{getD}\left(\operatorname{ite}\left(16 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 16\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0), (\operatorname{getD}\left(\operatorname{ite}\left(16 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 16\right)\right), \operatorname{none}\left(\right)\right), 0\right) != nd)\right)\right), \mathbb{Z}\right)\right), n, j)\right)\right))\left(\operatorname{mod}\left(jt, 2\right) - xj\right))\left(\operatorname{mod}\left(nt, 2\right) - xn\right))\left(xj + \operatorname{getD}\left(\operatorname{ite}\left(7 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 7\right)\right), \operatorname{none}\left(\right)\right), 0\right) + \operatorname{getD}\left(\operatorname{ite}\left(9 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 9\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right))\left(xn + \operatorname{getD}\left(\operatorname{ite}\left(6 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 6\right)\right), \operatorname{none}\left(\right)\right), 0\right) + \operatorname{getD}\left(\operatorname{ite}\left(8 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 8\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right))\left(\operatorname{mod}\left(jv, 2\right)\right))\left(\operatorname{mod}\left(nv, 2\right)\right))\left(j + \operatorname{getD}\left(\operatorname{ite}\left(5 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 5\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right))\left(n + \operatorname{getD}\left(\operatorname{ite}\left(4 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 4\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseNext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The update adds the endpoint-parity carries to the next binary bits, divides by two for the new carries, adds each rounded-half bit to its preceding bit and addition carry, and subtracts that bit from the resulting remainder to emit a signed digit. It rejects an input digit opposite to the digit two positions earlier. Otherwise it returns the full 19-component state and the label (f,q,n,j). div and mod here are Euclidean integer quotient and remainder. Boolean tests are embedded in the integers by toNat followed by cast.

**Definition 1.3 (All literal arithmetic successors).**

$$\forall s \in \operatorname{List}\left(\mathbb{Z}\right),\; \operatorname{baseSuccessors}\left(s\right) = \operatorname{flatMap}\left(n:\mathbb{Z} \mapsto \operatorname{flatMap}\left(j:\mathbb{Z} \mapsto \operatorname{filterMap}\left(\operatorname{baseNext}\left(s, n, j\right), \operatorname{relNext}\left(\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right), n, j\right)\right), [0,1]\right), [0,1]\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseSuccessors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each of the four pairs of binary input bits, the relation transition supplies every allowed next relation state. baseNext adds the rounded-half carries, emits signed digits, updates the first and latest nonzero signs, and rejects an opposite input digit two positions later. The remaining components record the output violation flag and the two edge charges.

**Definition 1.4 (The seven arithmetic source states).**

$$initialStates = \operatorname{flatMap}\left(n:\mathbb{Z} \mapsto \operatorname{flatMap}\left(j:\mathbb{Z} \mapsto \operatorname{map}\left(r:\mathbb{Z} \mapsto [r, 1, n, j, n, j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], \operatorname{ite}\left(n = j, [6], \operatorname{ite}\left(j < n, [1, 2, 0], [1, 2]\right)\right)\right), [0,1]\right), [0,1]\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.initialStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two lowest input bits give the fixed endpoint parities and initial rounded-half carries. Equal bits start the even-cut relation; different bits start A and B, with the flushed relation additionally available for the pair (1,0). All sign, previous-bit, addition-carry and violation components start at zero.

**Definition 1.5 (The complete concrete graph and two potentials).**

$$\forall i \in \mathbb{N},\; \operatorname{baseTable}\left(i\right):\operatorname{List}\left(\mathbb{Z}\right) \times \operatorname{List}\left(\mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right) \times \operatorname{Option}\left(\mathbb{Z}\right) \times \operatorname{Option}\left(\mathbb{Z}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For indices 0 through 1491, baseTable selects one of 1492 literal rows through a balanced tree of index comparisons. The initial subtree remains inline; the other 63 subtrees are private baseTableChunk functions taking the original natural index. Each row consists of its 19 integer state components, a complete list of edges (target, f, q, input bit, output bit), and the optional class and charge potentials. Lookup outside that range returns the final row; the automaton uses Fin 1492, so its runs never use that fallback.

**Definition 1.6 (The final parity and lowest-sign correction).**

$$\forall s \in \operatorname{List}\left(\mathbb{Z}\right),\; \operatorname{baseOffset}\left(s\right) = \operatorname{ite}\left(\operatorname{getD}\left(\operatorname{ite}\left(15 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 15\right)\right), \operatorname{none}\left(\right)\right), 0\right) < 0, 1 - \operatorname{getD}\left(\operatorname{ite}\left(3 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 3\right)\right), \operatorname{none}\left(\right)\right), 0\right), \operatorname{getD}\left(\operatorname{ite}\left(3 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 3\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right) - \operatorname{ite}\left(\operatorname{getD}\left(\operatorname{ite}\left(14 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 14\right)\right), \operatorname{none}\left(\right)\right), 0\right) < 0, 1 - \operatorname{getD}\left(\operatorname{ite}\left(2 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 2\right)\right), \operatorname{none}\left(\right)\right), 0\right), \operatorname{getD}\left(\operatorname{ite}\left(2 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 2\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Optional lookup reads a state component with default zero. Components 2 and 3 contain the two fixed endpoint parities; 14 and 15 contain their lowest nonzero signs. The formula is precisely the difference of the two final corrections.

**Definition 1.7 (Flushed relation and arithmetic state).**

$$\forall s \in \operatorname{List}\left(\mathbb{Z}\right),\; \operatorname{baseTerminal}\left(s\right) = \operatorname{Bool.and}\left((\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 0), \operatorname{all}\left(k:\mathbb{N} \mapsto (\operatorname{getD}\left(\operatorname{ite}\left(k < \operatorname{List.length}\left(s\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(s, k\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 0), [4,5,6,7,8,9]\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTerminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A state is terminal precisely when its relation component is zero and all six arithmetic carry and previous-bit components at indices 4 through 9 are zero.

**Definition 1.8 (The graph with selected terminal states).**

$$\forall charge \in \operatorname{Bool},\; \operatorname{baseAutomaton}\left(charge\right) = \operatorname{NFA.mk}\left(i:\operatorname{Fin}\left(1492\right) \mapsto a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \{j:\operatorname{Fin}\left(1492\right) \mid (\operatorname{val}\left(j\right), a) \in \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{baseTable}\left(\operatorname{val}\left(i\right)\right)\right)\right)\}, \{i:\operatorname{Fin}\left(1492\right) \mid \operatorname{contains}\left(List.range\left(7\right), \operatorname{val}\left(i\right)\right)\}, \{i:\operatorname{Fin}\left(1492\right) \mid \operatorname{baseTerminal}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(i\right)\right)\right)\right) \land \operatorname{getD}\left(\operatorname{ite}\left(18 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(i\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(i\right)\right)\right), 18\right)\right), \operatorname{none}\left(\right)\right), 0\right) = \operatorname{ite}\left(charge, 0, 1\right)\}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseAutomaton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are seven source indices, 0 through 6. Every edge is the literal row entry. A terminal state has relation component zero and vanishing arithmetic components 4 through 9. The last component selects valid outputs for the charge bound and invalid outputs for the class bound. The four input coordinates are f, q, n-bit, j-bit.

**Theorem 1.9 (The concrete zero and three bounds).**

$$\forall charge \in \operatorname{Bool},\; \forall s \in \operatorname{Fin}\left(1492\right),\; \forall t \in \operatorname{Fin}\left(1492\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \left(s \in \operatorname{start}\left(\operatorname{baseAutomaton}\left(charge\right)\right) \land t \in \operatorname{accept}\left(\operatorname{baseAutomaton}\left(charge\right)\right)\right) \Rightarrow \left(\forall p \in \operatorname{Path}\left(\operatorname{baseAutomaton}\left(charge\right), s, t, xs\right),\; \operatorname{pathCharge}\left(\lambda [\operatorname{Fin}\left(1492\right)] a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} [\operatorname{Fin}\left(1492\right)] \mapsto \operatorname{ite}\left(charge, 3, 1\right) \cdot \operatorname{fst}\left(a\right) + \operatorname{ite}\left(charge, \operatorname{fst}\left(\operatorname{snd}\left(a\right)\right), 0\right), p\right) + \operatorname{ite}\left(charge, \operatorname{baseOffset}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(t\right)\right)\right)\right), 0\right) \le \operatorname{ite}\left(charge, 3, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.base_accepted_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete row checks reconstruct every possible transition, enforce in-range successor indices, verify the source and goal conditions, and check reverse-closed integer potential inequalities. Kernel reduction checks 24 blocks of at most 64 rows in both modes. The partial-potential path theorem then applies to arbitrary finite accepted runs. This statement concerns graph paths; identifying such paths with actual integer palindrome cuts requires a separate arithmetic bridge.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseAutomaton`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseNext`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseOffset`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseSuccessors`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTable`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTerminal`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.base_accepted_bound`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.initialStates`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.relNext`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/AutomatonPotential](AutomatonPotential.md)
