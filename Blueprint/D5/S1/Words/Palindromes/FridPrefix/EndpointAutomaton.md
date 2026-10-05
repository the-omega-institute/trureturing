# A paired-digit endpoint automaton

## Abstract

A paired-digit endpoint automaton

**Definition 1.1 (endpointRows).**

$$endpointRows:List\left(List\left(tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{N}\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.endpointRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal seventeen rows list triples (first bit, second bit, destination). All entries of the transition relation are the triples printed in the Lean table; empty rows have no transitions.

**Definition 1.2 (endpoint).**

$$endpoint:NFA\left(tuple\left(Fin\left(2\right), Fin\left(2\right)\right), Fin\left(17\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.endpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The start set consists only of state 0. The accept set is {3,9,11}. For paired bits d, t is in step(q,d) exactly when (val(d.fst),val(d.snd),val(t)) occurs in endpointRows[val(q)], using the empty list for a missing row.

**Definition 1.3 (movesFrom).**

$$\forall q \in \mathbb{N},\; movesFrom\left(q, 0\right) = singleton\left(tuple\left(0, 0, q\right)\right) \land \left(\forall width \in \mathbb{N},\; movesFrom\left(q, width + 1\right) = flatMap\left(\lambda (t:tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{N}\right)) \mapsto map\left(\lambda (s:tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{N}\right)) \mapsto tuple\left(first\left(t\right) \cdot pow\left(2, width\right) + first\left(s\right), second\left(t\right) \cdot pow\left(2, width\right) + second\left(s\right), third\left(s\right)\right), movesFrom\left(third\left(t\right), width\right)\right), getD\left(endpointRows, q, nil\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.movesFrom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equations give the literal recursion: movesFrom(q,0)=[(0,0,q)]; for width+1, concatenate over (x,y,t) in endpointRows.getD(q,[]) the mapped list [(x*2^width+a,y*2^width+b,s) | (a,b,s) in movesFrom(t,width)]. It is a recursion over the bit width, with both chunk values read most significant first.

**Definition 1.4 (chunkEndpoint).**

$$\forall width \in \mathbb{N},\; chunkEndpoint\left(width\right) = nfa\left(start\left(endpoint\right), accept\left(endpoint\right), \lambda (q:Fin\left(17\right)) \mapsto \lambda (d:tuple\left(\mathbb{N}, \mathbb{N}\right)) \mapsto setOf\left(\lambda (t:Fin\left(17\right)) \mapsto mem\left(tuple\left(fst\left(d\right), snd\left(d\right), val\left(t\right)\right), movesFrom\left(val\left(q\right), width\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.chunkEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

nfa(start,accept,step) is the NFA record constructor. setOf forms the set of states satisfying its predicate. The start and accept sets are exactly those of endpoint; only the alphabet and transition relation are regrouped.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.chunkEndpoint`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.endpoint`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.endpointRows`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.movesFrom`
