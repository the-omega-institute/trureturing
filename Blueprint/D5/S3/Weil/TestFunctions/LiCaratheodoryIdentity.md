# Li-Caratheodory Identity

## Abstract

The normalized Li second-difference series is the completed-zeta logarithmic derivative and extends meromorphically.

**Theorem 1.1 (Li curvature has its exact logarithmic-derivative continuation).**

$$\begin{gathered}\forall lambda: \mathbb{N} \to \mathbb{R},\\{}(\left(lambda\left(0\right) = 0 \land 0 < lambda\left(1\right)\right) \land \operatorname{Eventually}\left((z: \mathbb{C} \mapsto \operatorname{HasSum}\left((n: \mathbb{N} \mapsto \operatorname{complexCast}\left(lambda\left(n + 1\right)\right) \cdot z^{n}), \frac{\operatorname{logDeriv}\left(xiReading, \frac{1}{1 - z}\right)}{\left(1 - z\right)^{2}}\right)), \operatorname{nhds}\left(\operatorname{complex}\left(0\right)\right)\right)) \Rightarrow\\{}\operatorname{let} liCaratheodory: \mathbb{C} \to \mathbb{C} := (z: \mathbb{C} \mapsto 1 + 2 \cdot \sum_{n\in \mathbb{N}} \frac{\operatorname{complexCast}\left(lambda\left(n + 2\right)\right) - 2 \cdot \operatorname{complexCast}\left(lambda\left(n + 1\right)\right) + \operatorname{complexCast}\left(lambda\left(n\right)\right)}{2 \cdot \operatorname{complexCast}\left(lambda\left(1\right)\right)} \cdot \operatorname{pow}\left(z, n + 1\right)),\\{}\operatorname{let} continuation: \mathbb{C} \to \mathbb{C} := (z: \mathbb{C} \mapsto \frac{1}{\operatorname{complexCast}\left(lambda\left(1\right)\right)} \cdot \operatorname{logDeriv}\left(xiReading, \frac{1}{1 - z}\right)),\\{}\operatorname{EventuallyEq}\left(\operatorname{nhds}\left(\operatorname{complex}\left(0\right)\right), liCaratheodory, continuation\right) \land \operatorname{MeromorphicOn}\left(continuation, \mathbb{C} \setminus \{1\}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LiCaratheodoryIdentity.li_caratheodory_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public coefficient carrier is a real sequence with zero initial value, positive first coefficient, and the standard local Keiper-Li generating law for the canonical xi reading.

The Caratheodory function is constructed in the statement from the normalized second differences. Shifted HasSum identities give the exact local equality without a Riemann-hypothesis premise.

The same public conclusion identifies the right side as a meromorphic continuation on the complex plane punctured at the Mobius pole. It uses the repository's entire xi reading and Mathlib's logarithmic derivative rather than a parallel carrier.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/LiCaratheodoryIdentity.li_caratheodory_identity`
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)
