# The Ordered Zeckendorf Long Game Strategy

## Abstract

Complete ordered Long Game Strategy optimality with every permitted switch choice.

The source is Definition 1.6 and Conjecture 1.7 of Bortnovskyi et al., The Ordered Zeckendorf Game, arXiv:2508.20222v2. Raw index zero represents F1=1 and raw index one represents F2=2; decode maps successor. The original Move, Preferred, LGSPath, Terminal and Conjecture17 definitions are used unchanged. All adjacent inversion switches remain permitted, and the strategy restarts priority after every move.

**Theorem 1.1 (Every ordered strategy path erases to a raw greedy path).**

Lean statement: `D5/S1/Digit/Carry/OrderedGame/Completion.lgs_path_raw_erasure`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Completion.lgs_path_raw_erasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every LGSPath s t length weight, its raw multiplicities form a RawGreedyPath with the same weight. An available switch outranks every carry, so a selected carry starts sorted. In a sorted list each duplicate has an adjacent occurrence, and strict value order forces strict position order. Thus rightmost split selection excludes every higher duplicate. Absence of preferred splits makes a selected merge binary, and every lower enabled consecutive pair occurs to its left. Switches preserve counts and contribute zero reward; induction erases them without imposing an order on their choices.

**Theorem 1.2 (Finite complete LGS continuations exist from every ordered state).**

Lean statement: `D5/S1/Digit/Carry/OrderedGame/Completion.complete_lgs_exists`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Completion.complete_lgs_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every list has an actual finite LGS path ending at an ordered terminal state. At a nonterminal list, minimizing a natural rank over legal moves gives a move satisfying the exact relational priority. The rank uses priority first and the prescribed positional tie rule; all switches share the same rank. Carries strictly decrease the existing lexicographic token-count and index-weight measure, while switches preserve that measure and decrease inversions. Well-founded recursion on their combined measure gives completion. The empty and singleton states are included; in particular the source start n=1 is covered.

**Theorem 1.3 (Conjecture 1.7).**

Lean statement: `D5/S1/Digit/Carry/OrderedGame/Completion.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Completion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conclusion is exactly Conjecture17. For every positive n there exists a complete LGS path from n ones. For every such complete LGS path, with every permitted switch choice retained, every arbitrary legal terminal competing path has at most its actual move count. The competitor's weight is at most G by raw_terminal_bound; the strategy's weight equals G by priority-preserving erasure and complete_greedy_reward. The exact strategy potential and the competitor potential bound turn these weight statements into the length comparison. Terminal inversion zero follows from the actual absence of switches, not from raw counts. No Bellman premise, deterministic-switch restriction or finite cutoff is added.

Source-fidelity and first-freeze admission remain subject to independent review. Attribution remains with Bortnovskyi et al., Cusenza et al., and the suppliers contributed in PRs 7495, 7575, 7643 and 7651. The structured problem-resolution claim requires the future frozen declaration and is deferred until that admission. This formal result makes no worldwide-priority claim.

## References

- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Completion.complete_lgs_exists`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Completion.lgs_path_raw_erasure`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Completion.result`
- Dependency: [D5/S1/Digit/Carry/OrderedGame/Attainment](Attainment.md)
- Dependency: [D5/S1/Digit/Carry/OrderedGame/Optimality](Optimality.md)
