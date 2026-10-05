# Marked-Prefix Potential Certificates

## Abstract

Every accepted marked-prefix path satisfies its shape or charge bound.

**Definition 1.1 (The complete marked-prefix product graph).**

$$\forall i \in \mathbb{N},\; \operatorname{prefixTable}\left(i\right):\operatorname{List}\left(\mathbb{Z}\right) \times \operatorname{List}\left(\mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right) \times \operatorname{Option}\left(\mathbb{Z}\right) \times \operatorname{Option}\left(\mathbb{Z}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Indices zero through 4261 list the eight-component marker state, every labelled product edge, and the two optional potentials. The components are the base-state index, marker phase, flip flag, marker parity, retained flag, input phase, output phase and bad flag. Outside this range the final row is returned; all paths use Fin 4262.

**Definition 1.2 (The literal marker-state update).**

$$\forall full \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall e \in \mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z},\; \operatorname{nextMarker}\left(full, e\right) = (\lambda old:\operatorname{List}\left(\mathbb{Z}\right) \mapsto (\lambda next:\operatorname{List}\left(\mathbb{Z}\right) \mapsto (\lambda nd:\mathbb{Z} \mapsto (\lambda jd:\mathbb{Z} \mapsto (\lambda m:\mathbb{Z} \mapsto (\lambda flip:\operatorname{Bool} \mapsto (\lambda parity:\mathbb{Z} \mapsto (\lambda keep:\mathbb{Z} \mapsto (\lambda ni:\mathbb{Z} \mapsto (\lambda nj:\mathbb{Z} \mapsto (\lambda bad:\operatorname{Bool} \mapsto (\lambda finish:\operatorname{List}\left(\mathbb{Z}\right) \to \operatorname{List}\left(\mathbb{Z}\right) \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \operatorname{ite}\left((\operatorname{getD}\left(\operatorname{ite}\left(18 < \operatorname{List.length}\left(next\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(next, 18\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0), [], \operatorname{ite}\left(m = 0, (\lambda unmarked:\operatorname{List}\left(\mathbb{Z}\right) \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \operatorname{ite}\left(\left(nd = 1 \land \operatorname{getD}\left(\operatorname{ite}\left(10 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 10\right)\right), \operatorname{none}\left(\right)\right), 0\right) = 0\right) \land \operatorname{getD}\left(\operatorname{ite}\left(11 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 11\right)\right), \operatorname{none}\left(\right)\right), 0\right) = 0, [unmarked, (\lambda an:\operatorname{Bool} \mapsto (\lambda aj:\operatorname{Bool} \mapsto (\lambda kp:\operatorname{Bool} \mapsto (\lambda bd:\operatorname{Bool} \mapsto finish\left([\operatorname{cast}\left(\operatorname{fst}\left(e\right), \mathbb{Z}\right), 1, \operatorname{cast}\left(\operatorname{toNat}\left(flip\right), \mathbb{Z}\right), \operatorname{getD}\left(\operatorname{ite}\left(1 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 1\right)\right), \operatorname{none}\left(\right)\right), 0\right), \operatorname{cast}\left(\operatorname{toNat}\left(kp\right), \mathbb{Z}\right), \operatorname{cast}\left(\operatorname{toNat}\left(an\right), \mathbb{Z}\right), \operatorname{cast}\left(\operatorname{toNat}\left(aj\right), \mathbb{Z}\right), \operatorname{cast}\left(\operatorname{toNat}\left(bd\right), \mathbb{Z}\right)]\right))\left(\operatorname{Bool.or}\left(\operatorname{Bool.or}\left(\operatorname{Bool.or}\left((\operatorname{getD}\left(\operatorname{ite}\left(12 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 12\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0), (\operatorname{getD}\left(\operatorname{ite}\left(13 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 13\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0)\right), \operatorname{Bool.and}\left((jd != 0), (jd != 1)\right)\right), \operatorname{Bool.and}\left(\operatorname{Bool.not}\left(kp\right), \operatorname{Bool.or}\left(\operatorname{Bool.or}\left(\operatorname{Bool.not}\left(an\right), aj\right), \operatorname{Bool.not}\left(flip\right)\right)\right)\right)\right))\left((jd == 1)\right))\left(\operatorname{Bool.or}\left(\operatorname{decide}\left(\operatorname{getD}\left(\operatorname{ite}\left(17 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 17\right)\right), \operatorname{none}\left(\right)\right), 0\right) < 0\right), \operatorname{Bool.and}\left((\operatorname{getD}\left(\operatorname{ite}\left(17 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 17\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 0), (\operatorname{getD}\left(\operatorname{ite}\left(3 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 3\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 1)\right)\right)\right))\left(\operatorname{Bool.or}\left(\operatorname{decide}\left(\operatorname{getD}\left(\operatorname{ite}\left(16 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 16\right)\right), \operatorname{none}\left(\right)\right), 0\right) < 0\right), \operatorname{Bool.and}\left((\operatorname{getD}\left(\operatorname{ite}\left(16 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 16\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 0), (\operatorname{getD}\left(\operatorname{ite}\left(2 < \operatorname{List.length}\left(old\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(old, 2\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 1)\right)\right)\right)], [unmarked]\right))\left(finish\left([\operatorname{cast}\left(\operatorname{fst}\left(e\right), \mathbb{Z}\right), 0, \operatorname{cast}\left(\operatorname{toNat}\left(\operatorname{Bool.and}\left(flip, (nd + jd == 0)\right)\right), \mathbb{Z}\right), 0, 0, 0, 0, 0]\right)\right), \operatorname{ite}\left(m = 1 \lor m = 2, \operatorname{ite}\left((nd != 0), [], [finish\left([\operatorname{cast}\left(\operatorname{fst}\left(e\right), \mathbb{Z}\right), m + 1, \operatorname{cast}\left(\operatorname{toNat}\left(flip\right), \mathbb{Z}\right), parity, keep, ni, nj, \operatorname{cast}\left(\operatorname{toNat}\left(\operatorname{Bool.or}\left(bad, (nd != jd)\right)\right), \mathbb{Z}\right)]\right)]\right), \operatorname{ite}\left(m = 3, \operatorname{ite}\left(\operatorname{Bool.and}\left((nd != 0), (nd != 1)\right), [], [finish\left([\operatorname{cast}\left(\operatorname{fst}\left(e\right), \mathbb{Z}\right), \operatorname{ite}\left(nd = 1, 1, 4\right), \operatorname{cast}\left(\operatorname{toNat}\left(flip\right), \mathbb{Z}\right), parity, keep, ni, nj, \operatorname{cast}\left(\operatorname{toNat}\left(\operatorname{Bool.or}\left(bad, (nd != jd)\right)\right), \mathbb{Z}\right)]\right)]\right), \operatorname{ite}\left((nd != 0), [], [finish\left([\operatorname{cast}\left(\operatorname{fst}\left(e\right), \mathbb{Z}\right), 4, \operatorname{cast}\left(\operatorname{toNat}\left(flip\right), \mathbb{Z}\right), parity, keep, ni, nj, \operatorname{cast}\left(\operatorname{toNat}\left(\operatorname{Bool.or}\left(bad, (nd != jd)\right)\right), \mathbb{Z}\right)]\right)]\right)\right)\right)\right)\right))\left(\lambda state:\operatorname{List}\left(\mathbb{Z}\right) \mapsto (state, \operatorname{fst}\left(\operatorname{snd}\left(e\right)\right), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{snd}\left(e\right)\right)\right), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{snd}\left(\operatorname{snd}\left(e\right)\right)\right)\right), \operatorname{snd}\left(\operatorname{snd}\left(\operatorname{snd}\left(\operatorname{snd}\left(e\right)\right)\right)\right))\right))\left((\operatorname{getD}\left(\operatorname{ite}\left(7 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 7\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0)\right))\left(\operatorname{getD}\left(\operatorname{ite}\left(6 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 6\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right))\left(\operatorname{getD}\left(\operatorname{ite}\left(5 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 5\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right))\left(\operatorname{getD}\left(\operatorname{ite}\left(4 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 4\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right))\left(\operatorname{getD}\left(\operatorname{ite}\left(3 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 3\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right))\left((\operatorname{getD}\left(\operatorname{ite}\left(2 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 2\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0)\right))\left(\operatorname{getD}\left(\operatorname{ite}\left(1 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 1\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right))\left(\operatorname{getD}\left(\operatorname{ite}\left(12 < \operatorname{List.length}\left(next\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(next, 12\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right))\left(\operatorname{getD}\left(\operatorname{ite}\left(10 < \operatorname{List.length}\left(next\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(next, 10\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right))\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right)\right))\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.nextMarker` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The marker modes are zero before selection, one and two while reading the two separating zeros, three before the next positive coefficient, and four during the final zeros. The formula displays the complete branch update. Each Boolean flag is converted to a natural number and then to an integer for storage.

**Definition 1.3 (Literal marker transitions).**

$$\forall full \in \operatorname{List}\left(\mathbb{Z}\right),\; \operatorname{successors}\left(full\right) = \operatorname{flatMap}\left(e:\mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \operatorname{nextMarker}\left(full, e\right), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.successors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every base edge is passed to the marker-state transition nextMarker. The unmarked phase may remain unmarked or select a positive digit with two preceding zeros; marked phases read two zeros and the next positive digit, and phase four flushes leading zeros. Output-class violations are excluded and the flip, phase, parity, retention and bad flags follow the literal marker update.

**Definition 1.4 (The successor-completeness checker).**

$$\forall i \in \mathbb{N},\; \operatorname{prefixRealizationRowCheck}\left(i\right) = \operatorname{Bool.and}\left(\operatorname{all}\left(a:\operatorname{List}\left(\mathbb{Z}\right) \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \operatorname{contains}\left(\operatorname{map}\left(e:\mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto (\operatorname{fst}\left(\operatorname{prefixTable}\left(\operatorname{fst}\left(e\right)\right)\right), \operatorname{snd}\left(e\right)), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{prefixTable}\left(i\right)\right)\right)\right), a\right), \operatorname{successors}\left(\operatorname{fst}\left(\operatorname{prefixTable}\left(i\right)\right)\right)\right), \operatorname{all}\left(e:\mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \operatorname{decide}\left(\operatorname{fst}\left(e\right) < 4262\right), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{prefixTable}\left(i\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixRealizationRowCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The checker compares every literal marker successor against the decoded indexed edge list, then verifies every target index is below 4262. It checks transition completeness independently of the potential inequalities.

**Definition 1.5 (Bounded reconstruction windows).**

$$\forall start \in \mathbb{N},\; \forall count \in \mathbb{N},\; \operatorname{prefixRealizationBlockCheck}\left(start, count\right) = \operatorname{all}\left(k:\mathbb{N} \mapsto \operatorname{prefixRealizationRowCheck}\left(start + k\right), \operatorname{range}\left(count\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixRealizationBlockCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each window checks count consecutive rows starting at start. Separate kernel certificates cover all windows, and their union covers every marker state.

**Definition 1.6 (Completed marker and terminal base state).**

$$\forall full \in \operatorname{List}\left(\mathbb{Z}\right),\; \operatorname{terminal}\left(full\right) = \operatorname{Bool.and}\left((\operatorname{getD}\left(\operatorname{ite}\left(1 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 1\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 4), \operatorname{baseTerminal}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The terminal test requires marker phase four and a terminal underlying base state. The bad flag is tested separately by each automaton's acceptance predicate. Option lookups use default zero and toNat converts the stored integer index to a natural number.

**Definition 1.7 (The terminal marked-prefix charge correction).**

$$\forall full \in \operatorname{List}\left(\mathbb{Z}\right),\; \operatorname{prefixOffset}\left(full\right) = \operatorname{baseOffset}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 0\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)\right)\right)\right) + \operatorname{ite}\left((\operatorname{getD}\left(\operatorname{ite}\left(4 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 4\right)\right), \operatorname{none}\left(\right)\right), 0\right) != 0), (1 + 2 \cdot \operatorname{getD}\left(\operatorname{ite}\left(3 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 3\right)\right), \operatorname{none}\left(\right)\right), 0\right) - 1) \cdot (\operatorname{getD}\left(\operatorname{ite}\left(6 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 6\right)\right), \operatorname{none}\left(\right)\right), 0\right) - \operatorname{getD}\left(\operatorname{ite}\left(5 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 5\right)\right), \operatorname{none}\left(\right)\right), 0\right)), 1 + 2 \cdot \operatorname{getD}\left(\operatorname{ite}\left(3 < \operatorname{List.length}\left(full\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(full, 3\right)\right), \operatorname{none}\left(\right)\right), 0\right) + 1\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The terminal correction adds the base charge offset to the contribution of the retained or removed lowest marked digit. The marker parity assigns weight one or three. The operator getD reads an optional list entry with default zero, toNat converts an integer index to a natural number, and bne is Boolean inequality.

**Definition 1.8 (The marked-prefix automata).**

$$\forall charge \in \operatorname{Bool},\; \operatorname{prefixAutomaton}\left(charge\right) = \operatorname{NFA.mk}\left(i:\operatorname{Fin}\left(4262\right) \mapsto a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \{j:\operatorname{Fin}\left(4262\right) \mid (\operatorname{val}\left(j\right), a) \in \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{prefixTable}\left(\operatorname{val}\left(i\right)\right)\right)\right)\}, \{i:\operatorname{Fin}\left(4262\right) \mid \operatorname{val}\left(i\right) < 5\}, \{i:\operatorname{Fin}\left(4262\right) \mid \operatorname{Bool.and}\left(\operatorname{Bool.and}\left((\operatorname{getD}\left(\operatorname{ite}\left(1 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{prefixTable}\left(\operatorname{val}\left(i\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{prefixTable}\left(\operatorname{val}\left(i\right)\right)\right), 1\right)\right), \operatorname{none}\left(\right)\right), 0\right) == 4), \operatorname{baseTerminal}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{toNat}\left(\operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{prefixTable}\left(\operatorname{val}\left(i\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{prefixTable}\left(\operatorname{val}\left(i\right)\right)\right), 0\right)\right), \operatorname{none}\left(\right)\right), 0\right)\right)\right)\right)\right)\right), (\operatorname{getD}\left(\operatorname{ite}\left(7 < \operatorname{List.length}\left(\operatorname{fst}\left(\operatorname{prefixTable}\left(\operatorname{val}\left(i\right)\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{fst}\left(\operatorname{prefixTable}\left(\operatorname{val}\left(i\right)\right)\right), 7\right)\right), \operatorname{none}\left(\right)\right), 0\right) == \operatorname{ite}\left(charge, 0, 1\right))\right)\}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixAutomaton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both modes start at indices zero through four and use every listed product edge. Acceptance requires the marker phase to be four, a terminal base state, and bad flag zero for the charge mode or one for the shape mode. The Boolean parameter chooses the mode.

**Theorem 1.9 (Bounds on every accepted marked-prefix path).**

$$\forall charge \in \operatorname{Bool},\; \forall s \in \operatorname{Fin}\left(4262\right),\; \forall t \in \operatorname{Fin}\left(4262\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \left(s \in \operatorname{start}\left(\operatorname{prefixAutomaton}\left(charge\right)\right) \land t \in \operatorname{accept}\left(\operatorname{prefixAutomaton}\left(charge\right)\right)\right) \Rightarrow \left(\forall p \in \operatorname{Path}\left(\operatorname{prefixAutomaton}\left(charge\right), s, t, xs\right),\; \operatorname{pathCharge}\left(\lambda [\operatorname{Fin}\left(4262\right)] a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} [\operatorname{Fin}\left(4262\right)] \mapsto \operatorname{ite}\left(charge, 5, 1\right) \cdot \operatorname{fst}\left(a\right) + \operatorname{ite}\left(charge, \operatorname{fst}\left(\operatorname{snd}\left(a\right)\right), 0\right), p\right) + \operatorname{ite}\left(charge, \operatorname{prefixOffset}\left(\operatorname{fst}\left(\operatorname{prefixTable}\left(\operatorname{val}\left(t\right)\right)\right)\right), 0\right) \le \operatorname{ite}\left(charge, 5, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefix_accepted_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shape mode bounds total f charge by zero. The charge mode bounds five times f charge plus q charge and the terminal marked-prefix correction by five. The potentials telescope along paths of arbitrary length. Identifying these graph labels with integer cuts and signed-digit charges is a separate arithmetic obligation.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.nextMarker`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixAutomaton`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixOffset`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixRealizationBlockCheck`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixRealizationRowCheck`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixTable`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefix_accepted_bound`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.successors`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.terminal`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates](BaseCertificates.md)
