# Terminal and Initial Objects Under Opposites

## Abstract

Terminal objects become initial objects in the opposite category.

**Theorem 1.1 (Terminal objects and opposite initial objects coincide).**

$$\forall X\in C,\ \operatorname{Nonempty}(\operatorname{IsTerminal}(X)) \Leftrightarrow \operatorname{Nonempty}(\operatorname{IsInitial}(\operatorname{op}(X)))$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/OppositeTerminalInitial.terminal_iff_initial_op` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be an object of an arbitrary category C. The existence of the terminal-object structure on X, expressed propositionally by Nonempty, is equivalent after reversing all arrows to the existence of the initial-object structure on the opposite of X. The two structures record the same unique-morphism property with every arrow reversed.

The pinned Mathlib source was searched before proving. Its declarations IsTerminal.op and IsInitial.unop are exactly the two directions, so the Lean theorem only composes those library results and does not reconstruct the universal-property proof.

The formal scope is the first categorical clause of source remark 27.17: terminal and initial objects exchange under passage to the opposite category. It does not formalize the later final-coalgebra, temporal, or interpretive claims in that atom.

## References

- Truth anchor: `D5/S1/FixedPoints/OppositeTerminalInitial.terminal_iff_initial_op`
