# Constant error with a fourth-root sample count

## Abstract

Adaptive sampling of the whole Robin window

**Theorem 1.1 (Whole-window sampling bound).**

$$\forall A \in \mathbb{R},\; \forall B \in \mathbb{R},\; \operatorname{exp}\left(1\right) \le A \Rightarrow \left(A \le B \Rightarrow \left(\left|\operatorname{M}\left(A, B\right) - \operatorname{P}\left(A, B\right)\right| \le 9 \cdot C \land \left(\operatorname{N}\left(A, B\right) \le C \cdot B^{\frac{1}{4}} + \operatorname{m}\left(A, B\right) + 1 \land \operatorname{N}\left(A, B\right) \le 2 \cdot C \cdot B^{\frac{1}{4}} + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinAdaptiveWindow.window_sampling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M is the actual weighted negative mass and P sums the weighted positive parts of signed chords in the coordinate u(t)=t log(t). N counts distinct endpoint samples, m counts doubling blocks, and C=1/(1−2^(−1/6)).

Clip the final doubling block at B. In a block starting at a, an equally spaced mesh with step at most (a/B)^(1/12) times a^(3/4) has error at most 9(a/B)^(1/6). The same geometric weight bounds the cell count after division by B^(1/4) and allowance for the ceiling.

Each block contributes its left and interior nodes. Insert B once to obtain exactly one more distinct sample than the total cell count. The equal-endpoint window has one sample and zero chord mass. All signed values can use the same Mangoldt cutoff at the floor of B.

## References

- Truth anchor: `D5/S3/Weil/Mertens/RobinAdaptiveWindow.window_sampling`
- Dependency: [D5/S3/Weil/Mertens/RobinFiniteMesh](RobinFiniteMesh.md)
