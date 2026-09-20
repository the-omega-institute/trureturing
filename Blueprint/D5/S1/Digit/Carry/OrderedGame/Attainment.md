# Ordered Attainment

## Abstract

Exact ordered strategy accounting and arbitrary-order switch normalization.

This component concerns the Long Game Strategy of Definition 1.6 and Conjecture 1.7 in The Ordered Zeckendorf Game, arXiv:2508.20222v2. It uses the existing raw-index Move, Preferred, Path and LGSPath without changing their priorities or selecting a particular switching algorithm. Positive source indices are obtained by mapping successor.

**Theorem 1.1 (Zero inversions characterize sorted states).**

$$inv\left(decode\left(s\right)\right) = 0 \iff Pairwise\left(le, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Attainment.inversions_zero_iff_sorted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every raw state, the existing positive-index inversion counter is zero exactly when the raw list is nondecreasing. The proof inducts on the actual list and its smaller-tail count.

**Theorem 1.2 (Selected moves attain the full reward).**

$$LGSMove\left(p, a, s, t\right) \Rightarrow 1 + inv\left(decode\left(t\right)\right) = inv\left(decode\left(s\right)\right) + reward\left(s, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Attainment.lgs_move_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every selected carry starts sorted because any adjacent inversion would have higher priority. Leftmost selection of ones forces their prefix to be empty, which is essential to equality. The remaining cases compute the exact spectator counts on both sides of the selected window. Every permitted switch removes exactly one inversion.

**Theorem 1.3 (Every strategy path telescopes exactly).**

$$LGSPath\left(s, t, length, weight\right) \Rightarrow length + inv\left(decode\left(t\right)\right) = inv\left(decode\left(s\right)\right) + weight$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Attainment.lgs_path_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No assumption on initial sortedness or terminality is needed. For sorted initial and terminal final states, actual move count equals accumulated carry reward. This equality does not compare that reward with a competing raw carry strategy.

**Theorem 1.4 (Switch completion and order independence).**

$$\forall s \exists t LGSPath\left(s, t, inv\left(decode\left(s\right)\right), 0\right) \land Pairwise\left(le, t\right) \land Perm\left(s, t\right) \land \forall u length Path\left(s, u, length, 0\right) \Rightarrow {\forall p v \neg Move\left(p, switch, u, v\right)} \Rightarrow u = t \land length = inv\left(decode\left(s\right)\right) \land rawCounts\left(u\right) = rawCounts\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame/Attainment.switch_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every start there exists a sorted permutation reached by an LGS path of zero reward and exactly the initial inversion count moves. Every legal zero-reward path with no remaining switch has that same endpoint and length and preserves all raw multiplicities. Every carry has positive reward, so zero-reward paths are precisely switch phases. Strong induction on inversions constructs completion; the proof retains all allowed switch orders.

These attainment components feed the full Conjecture 1.7 proof in OrderedGame/Completion.result. Raw weighted domination is supplied by OrderedGame/Optimality, and Completion supplies priority correspondence and finite ordered completion. Independent pre-Freeze source-fidelity and declaration-admission review passed. Final new-head CI, ordinary merge and independent completion audit remain pending; no worldwide priority is claimed.

## References

- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Attainment.inversions_zero_iff_sorted`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Attainment.lgs_move_potential`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Attainment.lgs_path_potential`
- Truth anchor: `D5/S1/Digit/Carry/OrderedGame/Attainment.switch_normalization`
- Dependency: [D5/S1/Digit/Carry/OrderedGame](../OrderedGame.md)
