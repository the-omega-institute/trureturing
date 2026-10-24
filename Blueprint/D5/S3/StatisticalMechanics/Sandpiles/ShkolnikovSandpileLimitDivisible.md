# Divisibility of the rectangular sandpile limit

## Abstract

The direct limit of the rectangular sandpile groups with Shkolnikov's signed reflected tiling maps is divisible: every element has a multiple-root at a later rectangular stage.

Mikhail Shkolnikov, Algebraic Limits of Sandpiles, arXiv:2506.09912v3 (2 September 2025), Section 3, p. 8. The paper states verbatim: “Let Γ(p, q) be the portion of the square lattice given by the intersection with an open rectangle (0, p) × (0, q), where p and q are positive integers.” It defines the rectangular monomorphism by the signed reflected formula and, after Proposition 5, states verbatim: “For instance, one may expect that it is a rational subtorus or a divisible group.”

**Definition 1.1 (The circle-valued carrier).**

$$T = \operatorname{AddCircle}\left((1: \mathbb{R})\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.T` (`✓ std3`).

*Citation.* Mikhail Shkolnikov (2025). *Algebraic Limits of Sandpiles*. DOI: [10.48550/arXiv.2506.09912](https://doi.org/10.48550/arXiv.2506.09912). URL: <https://arxiv.org/abs/2506.09912v3>.

*Commentary.*

The carrier is the additive circle ℝ/ℤ.

**Definition 1.2 (The open rectangular domain).**

$$\forall p \in \mathbb{N},\; (\forall q \in \mathbb{N},\; (\forall z \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; (InRect\left(p, q, z\right) = \left((0 < \operatorname{Prod.fst}\left(z\right)) \land ((\operatorname{Prod.fst}\left(z\right) < \operatorname{Int.ofNat}\left(p\right)) \land ((0 < \operatorname{Prod.snd}\left(z\right)) \land (\operatorname{Prod.snd}\left(z\right) < \operatorname{Int.ofNat}\left(q\right))))\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.InRect` (`✓ std3`).

*Citation.* Mikhail Shkolnikov (2025). *Algebraic Limits of Sandpiles*. DOI: [10.48550/arXiv.2506.09912](https://doi.org/10.48550/arXiv.2506.09912). URL: <https://arxiv.org/abs/2506.09912v3>.

*Commentary.*

InRect p q z means that both integer coordinates of z lie strictly between the corresponding rectangle boundaries.

**Definition 1.3 (Rectangular sandpile functions).**

$$\forall p \in \mathbb{N},\; (\forall q \in \mathbb{N},\; (\forall f \in (\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \to T),\; (IsSandpile\left(p, q, f\right) = \left((\forall z \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; ((\neg(InRect\left(p, q, z\right))) \Rightarrow (f\left(z\right) = 0))) \land (\forall z \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; ((InRect\left(p, q, z\right)) \Rightarrow (\operatorname{HSMul.hSMul}\left((4: \mathbb{Z}), f\left(z\right)\right) = f\left((\operatorname{Prod.fst}\left(z\right) - 1, \operatorname{Prod.snd}\left(z\right))\right) + f\left((\operatorname{Prod.fst}\left(z\right) + 1, \operatorname{Prod.snd}\left(z\right))\right) + f\left((\operatorname{Prod.fst}\left(z\right), \operatorname{Prod.snd}\left(z\right) - 1)\right) + f\left((\operatorname{Prod.fst}\left(z\right), \operatorname{Prod.snd}\left(z\right) + 1)\right))))\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.IsSandpile` (`✓ std3`).

*Citation.* Mikhail Shkolnikov (2025). *Algebraic Limits of Sandpiles*. DOI: [10.48550/arXiv.2506.09912](https://doi.org/10.48550/arXiv.2506.09912). URL: <https://arxiv.org/abs/2506.09912v3>.

*Commentary.*

A rectangular sandpile function vanishes outside the open rectangle and satisfies the four-neighbour harmonic equation at every point inside it.

**Definition 1.4 (The reflected one-dimensional coordinate).**

$$\forall p \in \mathbb{N},\; (\forall x \in \mathbb{Z},\; (unfold\left(p, x\right) = \operatorname{ite}\left(\operatorname{Int.emod}\left(\operatorname{Int.ediv}\left(x, \operatorname{Int.ofNat}\left(p\right)\right), 2\right) = 0, x - \operatorname{Int.ediv}\left(x, \operatorname{Int.ofNat}\left(p\right)\right) \cdot \operatorname{Int.ofNat}\left(p\right), \left(\operatorname{Int.ediv}\left(x, \operatorname{Int.ofNat}\left(p\right)\right) + 1\right) \cdot \operatorname{Int.ofNat}\left(p\right) - x\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.unfold` (`✓ std3`).

*Citation.* Mikhail Shkolnikov (2025). *Algebraic Limits of Sandpiles*. DOI: [10.48550/arXiv.2506.09912](https://doi.org/10.48550/arXiv.2506.09912). URL: <https://arxiv.org/abs/2506.09912v3>.

*Commentary.*

The unfolded coordinate subtracts an even tile index and reflects an odd tile index, using integer division and remainder.

**Definition 1.5 (The signed reflected embedding).**

$$\forall p \in \mathbb{N},\; (\forall q \in \mathbb{N},\; (\forall m \in \mathbb{N},\; (\forall n \in \mathbb{N},\; (\forall phi \in (\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \to T),\; (\forall z \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; (embed\left(p, q, m, n, phi, z\right) = \operatorname{ite}\left(InRect\left(m \cdot p, n \cdot q, z\right), \operatorname{HSMul.hSMul}\left((-1: \mathbb{Z})^{\operatorname{Int.toNat}\left(\operatorname{Int.ediv}\left(\operatorname{Prod.fst}\left(z\right), \operatorname{Int.ofNat}\left(p\right)\right) + \operatorname{Int.ediv}\left(\operatorname{Prod.snd}\left(z\right), \operatorname{Int.ofNat}\left(q\right)\right)\right)}, phi\left((unfold\left(p, \operatorname{Prod.fst}\left(z\right)\right), unfold\left(q, \operatorname{Prod.snd}\left(z\right)\right))\right)\right), 0\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.embed` (`✓ std3`).

*Citation.* Mikhail Shkolnikov (2025). *Algebraic Limits of Sandpiles*. DOI: [10.48550/arXiv.2506.09912](https://doi.org/10.48550/arXiv.2506.09912). URL: <https://arxiv.org/abs/2506.09912v3>.

*Commentary.*

The embedding extends a function by zero and evaluates it at the reflected coordinates, multiplied by the sign determined by the two tile indices.

**Definition 1.6 (Divisibility of the direct limit).**

$$\forall p \in \mathbb{N},\; (\forall q \in \mathbb{N},\; ((1 \le p) \Rightarrow ((1 \le q) \Rightarrow (\forall f \in (\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \to T),\; ((IsSandpile\left(p, q, f\right)) \Rightarrow (\forall k \in \mathbb{N},\; ((1 \le k) \Rightarrow (\exists m \in \mathbb{N},\; (\exists n \in \mathbb{N},\; ((1 \le m) \land ((1 \le n) \land (\exists g \in (\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \to T),\; ((IsSandpile\left(m \cdot p, n \cdot q, g\right)) \land (\operatorname{HSMul.hSMul}\left(k, g\right) = embed\left(p, q, m, n, f\right)))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.claim` (`✓ std3`).

*Citation.* Mikhail Shkolnikov (2025). *Algebraic Limits of Sandpiles*. DOI: [10.48550/arXiv.2506.09912](https://doi.org/10.48550/arXiv.2506.09912). URL: <https://arxiv.org/abs/2506.09912v3>.

*Commentary.*

For every positive rectangle, harmonic function, and positive integer k, a later rectangle contains a harmonic function whose k-fold sum is the signed reflected image of the original function.

**Theorem 1.7 (Divisibility theorem).**

$$\forall p \in \mathbb{N},\; (\forall q \in \mathbb{N},\; ((1 \le p) \Rightarrow ((1 \le q) \Rightarrow (\forall f \in (\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \to T),\; ((IsSandpile\left(p, q, f\right)) \Rightarrow (\forall k \in \mathbb{N},\; ((1 \le k) \Rightarrow (\exists m \in \mathbb{N},\; (\exists n \in \mathbb{N},\; ((1 \le m) \land ((1 \le n) \land (\exists g \in (\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \to T),\; ((IsSandpile\left(m \cdot p, n \cdot q, g\right)) \land (\operatorname{HSMul.hSMul}\left(k, g\right) = embed\left(p, q, m, n, f\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Shkolnikov (2025). *Algebraic Limits of Sandpiles*. DOI: [10.48550/arXiv.2506.09912](https://doi.org/10.48550/arXiv.2506.09912). URL: <https://arxiv.org/abs/2506.09912v3>.

*Commentary.*

The reversible row recurrence closes on a finite denominator subgroup. Its period supplies a taller rectangle, and multiplying the lifted rows by k recovers the signed reflected embedding of the original harmonic function.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.InRect`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.IsSandpile`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.embed`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.unfold`
- Dependency: [D5/S1/Recurrence/FiniteCompanionSquareDefect](../../../S1/Recurrence/FiniteCompanionSquareDefect.md)
