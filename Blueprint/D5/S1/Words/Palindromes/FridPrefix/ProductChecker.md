# Closure and potential tests for paired finite-state runs

## Abstract

Closure and potential tests for paired finite-state runs

**Definition 1.1 (rawMember).**

$$\forall raw \in Array\left(Array\left(List\left(\mathbb{N}\right)\right)\right),\; \forall q \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall s \in \mathbb{N},\; rawMember\left(raw, q, p, s\right) = contains\left(getD\left(getD\left(raw, q, emptyArray\right), p, nil\right), s\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.rawMember` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Membership uses exactly the grouped lists, with an empty array and empty list as defaults.

**Definition 1.2 (coreMember).**

$$\forall core \in Array\left(Array\left(\mathbb{N}\right)\right),\; \forall q \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall s \in \mathbb{N},\; coreMember\left(core, q, p, s\right) = testBit\left(getD\left(getD\left(core, q, emptyArray\right), p, 0\right), s\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.coreMember` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bit at second rank state s is tested in the mask for endpoint q and first rank state p.

**Definition 1.3 (potential).**

$$\forall digits \in Array\left(Array\left(\mathbb{N}\right)\right),\; \forall q \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall s \in \mathbb{N},\; potential\left(digits, q, p, s\right) = int\left(mod\left(shiftRight\left(getD\left(getD\left(digits, q, emptyArray\right), p, 0\right), 3 \cdot s\right), 8\right)\right) - 2$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.potential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

mod is natural remainder; shiftRight is the natural bit shift. The remainder is cast to Int before subtracting 2. All missing arrays use the zero default.

**Definition 1.4 (movesCheck).**

$$\forall width \in \mathbb{N},\; \forall moves \in Array\left(Array\left(tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{N}\right)\right)\right),\; movesCheck\left(width, moves\right) = boolAnd\left(eqBool\left(size\left(moves\right), 17\right), all\left(range\left(17\right), \lambda (q:\mathbb{N}) \mapsto boolAnd\left(all\left(movesFrom\left(q, width\right), \lambda (t:tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{N}\right)) \mapsto contains\left(getElemBang\left(moves, q\right), t\right)\right), all\left(getElemBang\left(moves, q\right), \lambda (t:tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{N}\right)) \mapsto contains\left(movesFrom\left(q, width\right), t\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.movesCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The expression is the Boolean conjunction of moves.size=17 and, for every q in range(17), both list-inclusion tests between moves[q]! and movesFrom(q,width). Inclusion tests use all and contains, so order and multiplicity are ignored.

**Definition 1.5 (isAccept).**

$$\forall q \in \mathbb{N},\; isAccept\left(q\right) = decide\left(mem\left(q, list\left(3, 9, 11\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.isAccept` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The endpoint accept states are exactly 3, 9 and 11.

**Definition 1.6 (rowCheck).**

$$\forall rank \in ChunkRank,\; \forall moves \in Array\left(Array\left(tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{N}\right)\right)\right),\; \forall raw \in Array\left(Array\left(List\left(\mathbb{N}\right)\right)\right),\; \forall core \in Array\left(Array\left(\mathbb{N}\right)\right),\; \forall digits \in Array\left(Array\left(\mathbb{N}\right)\right),\; \forall q \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall s \in \mathbb{N},\; rowCheck\left(rank, moves, raw, core, digits, q, p, s\right) = boolAnd\left(if\left(isAccept\left(q\right), boolAnd\left(coreMember\left(core, q, p, s\right), decide\left(potential\left(digits, q, p, s\right) \le 1\right)\right), true\right), all\left(getElemBang\left(moves, q\right), \lambda (t:tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{N}\right)) \mapsto boolAnd\left(rawMember\left(raw, third\left(t\right), getD\left(getD\left(transitions\left(rank\right), p, emptyArray\right), first\left(t\right), 0\right), getD\left(getD\left(transitions\left(rank\right), s, emptyArray\right), second\left(t\right), 0\right)\right), if\left(coreMember\left(core, third\left(t\right), getD\left(getD\left(transitions\left(rank\right), p, emptyArray\right), first\left(t\right), 0\right), getD\left(getD\left(transitions\left(rank\right), s, emptyArray\right), second\left(t\right), 0\right)\right), boolAnd\left(coreMember\left(core, q, p, s\right), decide\left(potential\left(digits, q, p, s\right) + getD\left(getD\left(weights\left(rank\right), s, emptyArray\right), second\left(t\right), 0\right) - getD\left(getD\left(weights\left(rank\right), p, emptyArray\right), first\left(t\right), 0\right) \le potential\left(digits, third\left(t\right), getD\left(getD\left(transitions\left(rank\right), p, emptyArray\right), first\left(t\right), 0\right), getD\left(getD\left(transitions\left(rank\right), s, emptyArray\right), second\left(t\right), 0\right)\right)\right)\right), true\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.rowCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The expression is the literal Boolean test in Lean. If q accepts, it requires coreMember(q,p,s) and U(q,p,s)<=1. For every (x,y,t) in moves[q]!, let p1=transitions[p][x], s1=transitions[s][y], and gain=weights[s][y]-weights[p][x], using getD defaults 0. It requires rawMember(t,p1,s1). If coreMember(t,p1,s1), it additionally requires coreMember(q,p,s) and U(q,p,s)+gain<=U(t,p1,s1). Otherwise that last test is true.

**Definition 1.7 (groupCheck).**

$$\forall rank \in ChunkRank,\; \forall moves \in Array\left(Array\left(tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{N}\right)\right)\right),\; \forall raw \in Array\left(Array\left(List\left(\mathbb{N}\right)\right)\right),\; \forall core \in Array\left(Array\left(\mathbb{N}\right)\right),\; \forall digits \in Array\left(Array\left(\mathbb{N}\right)\right),\; \forall q \in \mathbb{N},\; groupCheck\left(rank, moves, raw, core, digits, q\right) = all\left(range\left(size\left(transitions\left(rank\right)\right)\right), \lambda (p:\mathbb{N}) \mapsto all\left(getD\left(getD\left(raw, q, emptyArray\right), p, nil\right), \lambda (s:\mathbb{N}) \mapsto rowCheck\left(rank, moves, raw, core, digits, q, p, s\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.groupCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each endpoint-state block checks every listed reachable pair of rank states. all returns a Boolean conjunction over a list. The seventeen blocks are proved by kernel reduction.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.coreMember`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.groupCheck`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.isAccept`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.movesCheck`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.potential`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.rawMember`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ProductChecker.rowCheck`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton](EndpointAutomaton.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/RankAutomata](RankAutomata.md)
