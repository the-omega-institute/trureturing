# Promise Colorings and Total Output Automata

## Abstract

Consistent conflict colorings characterize total output automata on promise domains.

**Theorem 1.1 (Exact state budget on an arbitrary nonempty promise domain).**

$$\operatorname{Realizable}(D, f, s) \iff \operatorname{ConsistentlyColorable}(D, f, s).$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/PromiseColoringTotalization.promise_coloring_iff_total_dfao` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Sigma and Y be arbitrary types, D a nonempty set of finite words over Sigma, f a function from D to Y, and s a positive integer. Neither Sigma, Y, nor D is assumed finite. The prefix set P consists of exactly those words u for which u followed by some suffix belongs to D. Two distinct prefixes conflict when one common suffix makes both words legal and their prescribed outputs unequal.

A coloring c from P to Fin s is proper when conflicting prefixes receive different colors. It is transition consistent when equal colors at u and v imply equal colors at ua and va whenever both extended prefixes belong to P. Fin s represents at most s colors; every color need not occur. Its zero-based indices correspond to the labels 1 through s by adding one.

Realizable(D,f,s) means that some finite state carrier Q of cardinality at most s supports a complete deterministic output automaton, with an initial state, a transition Q times Sigma to Q, and an output Q to Y, whose output is f on every word of D. The carrier is the existing DFAO extension of Mathlib DFA. Its acceptance set plays no role in output correctness. No rejection label or other prescribed output is attached to a word outside D.

Given a coloring, choose one legal word d. Its existence supplies both the root prefix and the default output f(d). The initial state is c of the empty word. For each color i and letter a, choose a prefix u of color i whose a-successor is still in P if one exists, and set the next state to c(ua). Transition consistency makes this independent of the chosen prefix. When none exists, set the next state to the root color. This defines transitions on every color and every letter, including unused colors.

At a color containing a legal terminal word u, use f(u) as output. Two such words with different outputs would conflict under the empty continuation, so properness makes the output unique. At a color containing no legal terminal word, use f(d). Thus no additional Nonempty Y or decidable equality assumption on Y is needed.

Induction by appending one letter proves that the actual DFA evaluation of every u in P is c(u). In the induction step, a legal continuation of ua also shows that u belongs to P, and the constructed transition agrees with c(ua). Applying this identity to each legal terminal word and the output construction proves correctness on all of D, including an infinite domain.

Conversely, color each prefix by the state actually reached by a correct total machine. Equal reached states remain equal after every common suffix, which excludes a conflict; determinism gives the one-letter consistency law. To express an arbitrary state carrier of size at most s on Fin s, embed Q using its finite enumeration and a capacity inclusion, choose a retraction sending each embedded state back to itself, and transport transitions and outputs through this pair. Induction on words proves preservation of all outputs. Extra states may be unreachable. A universe lift and Mathlib DFA reindexing give the reverse carrier correspondence in any chosen state universe.

The admissible positive budgets are therefore identical for machines and transition-consistent proper colorings. Whenever a finite admissible budget exists, the two least budgets are equal; if no finite budget exists, neither side has a finite minimum. Ordinary graph properness follows from a realization, but it does not provide the successor consistency used in the converse construction.

The construction includes an empty alphabet, a promise containing the empty word, singleton promises, and colors unused by any prefix or terminal word. It uses classical choices over possibly infinite sets. It asserts neither computability of a coloring nor an algorithm to decide colorability, and imposes no word-length bound.

## References

- Truth anchor: `D5/S0/Automata/PromiseColoringTotalization.promise_coloring_iff_total_dfao`
- Dependency: [D5/S0/Automata/FiniteSampleRestriction](FiniteSampleRestriction.md)
