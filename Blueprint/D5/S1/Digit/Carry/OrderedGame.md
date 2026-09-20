# Ordered Zeckendorf Paths and the Inversion Potential

## Abstract

Concrete raw greedy continuation, shared-input repairs, and ordered reward erasure.

A state is one list of natural-number raw W indices. Decode maps each index through successor to the positive paper indices; n zeros thus represent n ones. Multiplicities are obtained through Multiset.toFinsupp. Move records the position of its adjacent window and one of five actions: an inversion switch, combining ones, splitting twos, a general split, or a consecutive merge. No predecessor map is used.

**Theorem 1.1 (Concrete greedy continuation attains its reward).**

$$\forall c, \exists d, RawGreedyPath\left(c, d, G\left(c\right)\right) \land CanonicalRaw\left(d\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame.greedy_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite raw multiplicity state, the concrete continuation G is attained by a finite RawGreedyPath to binary nonadjacent digits. Each decision combines ones first, otherwise splits the highest duplicate, otherwise merges the least occupied consecutive pair. Priority is recomputed after every move. G recurses on the existing strict carry measure and is not defined as a maximum over paths. Labels remain data. This establishes raw attainment, not the comparison with competitors or ordered LGS completion.

**Theorem 1.2 (All five shared-input merge repairs).**

Lean statement: `D5/S1/Digit/Carry/OrderedGame.shared_input_merge_repair`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame.shared_input_merge_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With unrestricted spectators, a legal merge sharing an input with an enabled split has a split-first legal path to the exact merge endpoint. If the lower input is duplicated it is split first; otherwise the upper input is split. In positive paper indices the lower-input detours are S1;S2, S2;S3;S1, and Sa;S(a+1);C(a-2), with gains c1-1, 2c2+c1-2, and 2c(a-1)+2ca-2. The upper-input detours are S2;S1 at a=1, gaining zero, and S(a+1);C(a-1) at a>=2, gaining one. The theorem gives exact reward equality with a natural-number gain. Replacement tails are legal; no greedy-tail assertion is made.

**Theorem 1.3 (Ones first against arbitrary interleaved terminal paths).**

$$RawPath\left(c, e, w\right) \land CanonicalRaw\left(e\right) \land SplitStep\left(0, c, cPrime\right) \Rightarrow \exists v, RawPath\left(cPrime, e, v\right) \land w \le splitReward\left(c, 0\right) + v$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame.ones_terminal_promotion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If combining ones is enabled, every raw path to binary nonadjacent digits can be replaced by one beginning with that split, retaining its endpoint and at least its full reward. The competing path may interleave merges and splits arbitrarily. The proof promotes ones through split steps, repairs a merge consuming a one, and commutes past higher merges. This closes the ones-first promotion branch; highest nonzero splits and least binary merges still require their own proofs.

**Theorem 1.4 (Erasure preserves the complete reward).**

$$Path\left(s, t, length, weight\right) \Rightarrow RawPath\left(rawCounts\left(s\right), rawCounts\left(t\right), weight\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame.path_raw_erasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite legal ordered path erases to a labelled raw path with exactly the same accumulated reward. Switches preserve multiplicities and contribute zero reward. Each remaining label retains its actual CarryStep and its consumed and produced digits in the same spectator context. Labels are explicit and are not reconstructed from an unlabelled proposition. The theorem neither assumes terminality nor asserts optimality.

**Theorem 1.5 (The path potential bound).**

$$Path\left(s, t, length, weight\right) \Rightarrow length + inv\left(decode\left(t\right)\right) \le inv\left(decode\left(s\right)\right) + weight$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame.path_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite legal path, actual move count plus final inversions is at most initial inversions plus summed carry reward. Switch reward is zero. In positive indices the other rewards are c1-1, c2-1, c(i-1)+ci-1 for a split at i greater than two, and c(a+1) for a merge at a. Thus rewards include the carry itself. The proof telescopes the existing four local inversion bounds; a switch removes exactly one inversion. There is no terminality or strategy assumption.

LGSPath keeps every permitted inversion-switch choice. Its priority restarts after every move: switches, leftmost ones, rightmost split, then leftmost consecutive merge. Conjecture17 records nonvacuous complete LGS existence for every positive n and the comparison of every complete LGS run with every legal terminal competitor. That proposition is defined but not proved. The path bound alone does not establish attainment or weighted greedy optimality.

## References

- Truth anchor: `D5/S1/Digit/Carry/OrderedGame.greedy_attainment`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame.ones_terminal_promotion`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame.path_potential`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame.path_raw_erasure`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame.shared_input_merge_repair`
- Dependency: [D5/S1/Digit/Carry/ListInversions](ListInversions.md)
- Dependency: [D5/S1/Digit/Carry/SplitStabilization](SplitStabilization.md)
- Dependency: [D5/S1/Digit/Raw](../Raw.md)
