# Prefix-Constrained Greedy Optimality

## Abstract

Antitone gains on finite depth chains admit a prefix-closed maximizer under a unit-cost budget.

**Theorem 1.1 (Top-gain cells can be repaired to a prefix optimum).**

$$\begin{gathered}\forall P: \operatorname{Type}, \operatorname{Finite}(P),\\{}d, B \in \mathbb{N}, g: P \to \operatorname{Fin}(d) \to \mathbb{R},\\{}Top: \operatorname{Finset}(P \times \operatorname{Fin}(d)),\\{}(\forall p: P, \forall i, j \in \operatorname{Fin}(d), i\leq j \Rightarrow g(p, j)\leq g(p, i)) \land \Vert Top \Vert= B \land\\{}(\forall a \in Top, \forall b: P \times \operatorname{Fin}(d), \neg(b \in Top) \Rightarrow g(\operatorname{fst}(b), \operatorname{snd}(b))\leq g(\operatorname{fst}(a), \operatorname{snd}(a))) \Rightarrow\\{}\exists A: \operatorname{Finset}(P \times \operatorname{Fin}(d)),\\{}\Vert A \Vert= B \land (\forall p: P, \forall j \in \operatorname{Fin}(d), (p, j)\in A \Rightarrow \forall i \in \operatorname{Fin}(d), i< j \Rightarrow (p, i)\in A) \land\\{}\sum_{c\in Top} g(\operatorname{fst}(c), \operatorname{snd}(c))\leq \sum_{c\in A} g(\operatorname{fst}(c), \operatorname{snd}(c)) \land\\{}(\forall C: \operatorname{Finset}(P \times \operatorname{Fin}(d)), \Vert C \Vert= B \Rightarrow \sum_{c\in C} g(\operatorname{fst}(c), \operatorname{snd}(c))\leq \sum_{c\in A} g(\operatorname{fst}(c), \operatorname{snd}(c))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/PrefixConstrainedGreedyOptimality.prefix_constrained_greedy_optimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The channel type is finite and the available levels form Fin(d), so the candidate cell region is finite. Selecting B cells is exactly the budget constraint when every cell has unit cost.

Gain is publicly antitone along each channel. The selected set Top also satisfies the top-budget premise: every selected cell has gain at least that of every omitted cell.

Replacing a selected level whose predecessor is missing strictly lowers the sum of selected depth indices and cannot lower total gain. The process therefore terminates at a prefix-closed selection. Pairing the cells outside Top with the cells omitted from Top proves global optimality among all B-cell selections.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PrefixConstrainedGreedyOptimality.prefix_constrained_greedy_optimality`
