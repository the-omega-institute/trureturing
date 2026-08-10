# The Markov Spectrum Tree

## Abstract

Integer Markov triples are preserved by the Vieta-jump edge that generates the Markov tree.

**Theorem 1.1 (The Vieta jump preserves the Markov equation).**

$$a^{2}+b^{2}+c^{2}=3abc \Rightarrow a^{2}+b^{2}+(3ab-c)^{2}=3ab(3ab-c), c\mapsto 3ab-c$$

*Proof.* Machine-checked in Lean as `D5/S1/Markov/MarkovSpectrumTree.markov_vieta_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Markov triple is an integer solution of the equation a^2 + b^2 + c^2 = 3abc. Holding a and b fixed, the theorem proves that replacing c by 3ab - c gives another solution. This is the Vieta-jump edge: the original c and its replacement are the two roots of the corresponding quadratic equation, whose sum is 3ab.

The checked seed triples (1,1,1), (1,1,2), and (1,2,5) exhibit the base Markov numbers 1, 2, and 5. Applying the same edge to (1,2,1) produces (1,2,5), and applying it to (1,5,2) produces (1,5,13). Thus the formal statement supplies the algebraic tree step and the examples verify its first two generated branches.

## References

- Truth anchor: `D5/S1/Markov/MarkovSpectrumTree.markov_vieta_step`
