# Coordinate-Deletion Frequency Transport

## Abstract

Transport finite-family coordinate frequencies and union closure through coordinate deletion.

**Theorem 1.1 (Quantitative and half-frequency transport).**

$$\begin{aligned}\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)],\\F \in \operatorname{Finset}\left(\operatorname{Finset}\left(\alpha\right)\right), D \in \operatorname{Finset}\left(\alpha\right), j \in \alpha, r \in \mathbb{N},\\(\lvert D \rvert = r) \land \neg (j \in D) \Rightarrow \\\text{where} G = \operatorname{image}\left(A \mapsto (A \setminus D), F\right), N = \lvert F \rvert, M = \lvert G \rvert,\\x = \lvert \{A \mid A \in F \land j \in A\} \rvert, b = \lvert \{B \mid B \in G \land j \in B\} \rvert,\\((b + 2^{r} \cdot (M - b)) \cdot x \geq b \cdot N) \land (2 \cdot b \geq M \Rightarrow (2^{r} + 1) \cdot x \geq N).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/CoordinateDeletionFrequencyTransport.quantitative_and_half_frequency_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be the image of F after deleting D, and let N, M, x, and b be the displayed family and coordinate-frequency counts. The first inequality holds without assuming that F is union-closed.

The proof injects each non-j deletion fibre into the powerset of D by sending A to its deleted trace A intersect D. Reconstruction from A minus D and A intersect D gives the fibre bound, while deletion outside j also gives b at most x.

If j occurs in at least half of G, the same two live counting bounds give the stated (2^r+1) frequency bound in F. This is a transport theorem and does not resolve the Frankl union-closed sets conjecture.

**Theorem 1.2 (Coordinate deletion preserves union closure).**

$$\begin{aligned}\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)],\\F \in \operatorname{Finset}\left(\operatorname{Finset}\left(\alpha\right)\right), D \in \operatorname{Finset}\left(\alpha\right),\\(\forall A \in F, \forall B \in F, \operatorname{union}\left(A, B\right) \in F) \Rightarrow \\\forall A \in \operatorname{image}\left(S \mapsto (S \setminus D), F\right), \forall B \in \operatorname{image}\left(S \mapsto (S \setminus D), F\right), \operatorname{union}\left(A, B\right) \in \operatorname{image}\left(S \mapsto (S \setminus D), F\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/CoordinateDeletionFrequencyTransport.union_closed_after_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two members represented as A0 minus D and B0 minus D, their union is the deletion image of A0 union B0. This is the bind-only companion for the Frankl coordinate-deletion induction interface.

## References

- Truth anchor: `D5/S1/Phase/CoordinateDeletionFrequencyTransport.quantitative_and_half_frequency_transport`
- Truth anchor: `D5/S1/Phase/CoordinateDeletionFrequencyTransport.union_closed_after_deletion`
