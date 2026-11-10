# The entropic Glibichuk–Konyagin conjecture

## Abstract

A zero atom and a uniform component refute the unconditional entropic sum-product assertion for every fixed k.

**Definition 1.1 (delta).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall a \in \operatorname {ZMod}\left(p\right),\; \operatorname {delta}\left(a\right) = \operatorname {ite}\left(a = 0, 1, 0\right))$$

*Formalization.* `D5/S3/Entropy/GohGlibichukKonyagin/Result.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The point mass at zero on the finite field.

**Definition 1.2 (spike).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall t \in \mathbb {R},\; \forall a \in \operatorname {ZMod}\left(p\right),\; \operatorname {spike}\left(t, a\right) = \left(1 - t\right) \cdot \operatorname {ite}\left(a = 0, 1, 0\right) + \frac{t}{p})$$

*Formalization.* `D5/S3/Entropy/GohGlibichukKonyagin/Result.spike` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For prime p and 0≤t≤1 this is (1−t)δ₀+tU_p. The uniform mass is 1/p at every element.

**Definition 1.3 (conv).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall f \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; \forall g \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; \forall z \in \operatorname {ZMod}\left(p\right),\; \operatorname {conv}\left(f, g, z\right) = \sum_{a: \operatorname {ZMod}\left(p\right)} (\operatorname {f}\left(a\right) \cdot \operatorname {g}\left(z - a\right)))$$

*Formalization.* `D5/S3/Entropy/GohGlibichukKonyagin/Result.conv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the pinned Mathlib DiscreteConvolution.addRingConvolution, transported through the finite-field fiber equivalence to the displayed finite sum.

**Theorem 1.4 (conv eq sum).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall f \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; \forall g \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; \forall z \in \operatorname {ZMod}\left(p\right),\; \operatorname {conv}\left(f, g, z\right) = \sum_{a: \operatorname {ZMod}\left(p\right)} (\operatorname {f}\left(a\right) \cdot \operatorname {g}\left(z - a\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.conv_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence a↦(a,z−a) identifies the additive fiber with the field. Reindexing the upstream convolution sum gives the finite sum used by conv_spike and conv_mul.

**Definition 1.5 (mulLaw).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall f \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; \forall z \in \operatorname {ZMod}\left(p\right),\; \operatorname {mulLaw}\left(f, z\right) = \sum_{a: \operatorname {ZMod}\left(p\right)} (\sum_{b: \operatorname {ZMod}\left(p\right)} (\operatorname {ite}\left(a \cdot b = z, \operatorname {f}\left(a\right) \cdot \operatorname {f}\left(b\right), 0\right))))$$

*Formalization.* `D5/S3/Entropy/GohGlibichukKonyagin/Result.mulLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weights f(a)f(b) express independence of the two copies before multiplication.

**Definition 1.6 (iterLaw).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall f \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; (\operatorname {iterLaw}\left(0, f\right) = \operatorname {delta}\left(\right)) \land (\forall n \in \mathbb {N},\; \operatorname {iterLaw}\left(n + 1, f\right) = \operatorname {conv}\left(\operatorname {mulLaw}\left(f\right), \operatorname {iterLaw}\left(n, f\right)\right)))$$

*Formalization.* `D5/S3/Entropy/GohGlibichukKonyagin/Result.iterLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero-fold sum is zero; each further step adds an independent product.

**Definition 1.7 (sumLaw).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall n \in \mathbb {N},\; \forall f \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; \forall z \in \operatorname {ZMod}\left(p\right),\; \operatorname {sumLaw}\left(n, f, z\right) = \sum_{x: \operatorname {Fin}\left(n\right) \to \operatorname {ZMod}\left(p\right)} (\sum_{y: \operatorname {Fin}\left(n\right) \to \operatorname {ZMod}\left(p\right)} (\operatorname {ite}\left(\sum_{i: \operatorname {Fin}\left(n\right)} (\operatorname {x}\left(i\right) \cdot \operatorname {y}\left(i\right)) = z, \prod_{i: \operatorname {Fin}\left(n\right)} (f\left(\operatorname {x}\left(i\right)\right) \cdot f\left(\operatorname {y}\left(i\right)\right)), 0\right))))$$

*Formalization.* `D5/S3/Entropy/GohGlibichukKonyagin/Result.sumLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite pushforward is reused from Entropy.Forgetting.CapacityMonotone. Its domain is a pair of functions Fin n→ZMod p, with product weights for the 2n independent copies. The standard equivalence arrowProdEquivProdArrow sends a tuple of pairs to its two projection functions; sum_spike uses its sum_comp identity to prove equality with the tuple-of-pairs expression in iter_product. The equivalence preserves both the sum of products and every product weight.

**Definition 1.8 (Hbits).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall f \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; \operatorname {Hbits}\left(f\right) = \frac{\operatorname {shannonEntropy}\left(f\right)}{\operatorname {Real.log}\left(2\right)})$$

*Formalization.* `D5/S3/Entropy/GohGlibichukKonyagin/Result.Hbits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reused D5.S3.Entropy.MaxEntropy.shannonEntropy is in nats. Division by log 2 expresses exactly the paper's bits.

**Definition 1.9 (The complete unconditional assertion).**

$$claim = \left(\exists k \in \mathbb {N},\; (3 \le k) \land (\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall mu \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; ((\forall a \in \operatorname {ZMod}\left(p\right),\; 0 \le mu\left(a\right)) \land (\sum_{a: \operatorname {ZMod}\left(p\right)} (mu\left(a\right)) = 1)) \Rightarrow (\operatorname {min}\left(2 \cdot \operatorname {Hbits}\left(mu\right), \operatorname {Real.logb}\left(2, p\right)\right) - 1 \le \operatorname {Hbits}\left(\operatorname {sumLaw}\left(k, mu\right)\right))))\right)$$

*Formalization.* `D5/S3/Entropy/GohGlibichukKonyagin/Result.claim` (`✓ std3`).

*Citation.* M. K. Goh (2026). *On an entropic analogue of additive energy*. DOI: [10.2140/ent.2026.5.243](https://doi.org/10.2140/ent.2026.5.243). URL: <https://arxiv.org/abs/2406.18798v4>.

*Commentary.*

§6, Conjecture 15, equation (89), arXiv:2406.18798v4:

<blockquote><pre>**Conjecture 15 (Entropic Glibichuk–Konyagin lemma).** There is an integer &#36;k\geq 3&#36; such that the following holds. Let &#36;X&#36; be a random variable taking values in &#36;\mathbf F_p&#36; for a prime &#36;p&#36;. Then for independent copies &#36;X_1,\ldots,X_k,X'_1,\ldots,X'_k&#36; of &#36;X&#36;, we have&#10;&#36;&#36;H\{X_1X'_1+\cdots+X_kX'_k\} \geq \min(2H\{X\},\log p)-1. \qquad (89)&#36;&#36;</pre></blockquote>

<blockquote><pre>In the original additive-combinatorial version of this statement, &#36;k&#36; can be taken to be &#36;3&#36;, but any fixed integer is enough for our purposes.</pre></blockquote>

The paper uses binary logarithms and discrete random variables. On a finite field every discrete probability law is a nonnegative normalized real mass function. There is no further restriction on this mass function.

**Theorem 1.10 (card pos).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (0 < p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.card_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A prime has positive real cardinality; all denominators p are nonzero.

**Theorem 1.11 (spike sum).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall t \in \mathbb {R},\; \sum_{a: \operatorname {ZMod}\left(p\right)} (\operatorname {spike}\left(t, a\right)) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.spike_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed affine mixture has total mass one for every real t.

**Theorem 1.12 (spike law).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall t \in \mathbb {R},\; ((0 \le t) \land (t \le 1)) \Rightarrow ((\forall a \in \operatorname {ZMod}\left(p\right),\; 0 \le \operatorname {spike}\left(t\right)\left(a\right)) \land (\sum_{a: \operatorname {ZMod}\left(p\right)} (\operatorname {spike}\left(t\right)\left(a\right)) = 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.spike_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-atom mixture is a probability law, including both endpoints t=0 and t=1.

**Theorem 1.13 (spike entropy).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall t \in \mathbb {R},\; ((0 \le t) \land (t \le 1)) \Rightarrow ((t \cdot \operatorname {Real.log}\left(p\right) \le \operatorname {shannonEntropy}\left(\operatorname {spike}\left(t\right)\right)) \land (\operatorname {shannonEntropy}\left(\operatorname {spike}\left(t\right)\right) \le \operatorname {Real.log}\left(2\right) + t \cdot \operatorname {Real.log}\left(p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.spike_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite mixture entropy bracket gives the lower bound from the uniform component and the upper bound by adding the at-most-log-2 entropy of the Boolean mixing weight. Point-mass and uniform entropy are supplied by the existing equality characterizations.

**Theorem 1.14 (conv spike).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall t \in \mathbb {R},\; \forall u \in \mathbb {R},\; \operatorname {conv}\left(\operatorname {spike}\left(t\right), \operatorname {spike}\left(u\right)\right) = \operatorname {spike}\left(t + u - t \cdot u\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.conv_spike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation preserves U_p, so convolution multiplies the complementary zero-atom weights. The identity is algebraic and holds for all real t,u.

**Theorem 1.15 (mul spike).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall t \in \mathbb {R},\; \operatorname {mulLaw}\left(\operatorname {spike}\left(t\right)\right) = \operatorname {spike}\left(\frac{(t)^{2} \cdot \left(p - 1\right)}{p}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.mul_spike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero first coordinate, multiplication is a permutation of the field. Separating the zero coordinate yields the exact weight t²(p−1)/p of the uniform part of the product law.

**Theorem 1.16 (conv mul).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall f \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; \forall g \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; \forall z \in \operatorname {ZMod}\left(p\right),\; \operatorname {conv}\left(\operatorname {mulLaw}\left(f\right), g, z\right) = \sum_{a: \operatorname {ZMod}\left(p\right)} (\sum_{b: \operatorname {ZMod}\left(p\right)} (\operatorname {f}\left(a\right) \cdot \operatorname {f}\left(b\right) \cdot \operatorname {g}\left(z - a \cdot b\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.conv_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing over the intermediate product value eliminates the product indicator.

**Theorem 1.17 (iter product).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall n \in \mathbb {N},\; \forall f \in \operatorname {ZMod}\left(p\right) \to \mathbb {R},\; \forall z \in \operatorname {ZMod}\left(p\right),\; \operatorname {iterLaw}\left(n, f, z\right) = \sum_{v: \operatorname {Fin}\left(n\right) \to \operatorname {ZMod}\left(p\right)\times\operatorname {ZMod}\left(p\right)} (\operatorname {ite}\left(\sum_{i: \operatorname {Fin}\left(n\right)} ((\operatorname {v}\left(i\right)).1 \cdot (\operatorname {v}\left(i\right)).2) = z, \prod_{i: \operatorname {Fin}\left(n\right)} (f\left((\operatorname {v}\left(i\right)).1\right) \cdot f\left((\operatorname {v}\left(i\right)).2\right)), 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.iter_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction using the bijection between an (n+1)-tuple and its head and tail proves equality with the full independent product-law pushforward. This equality connects the recursive computation to sumLaw.

**Theorem 1.18 (sum spike).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall t \in \mathbb {R},\; \forall n \in \mathbb {N},\; \operatorname {sumLaw}\left(n, \operatorname {spike}\left(t\right)\right) = \operatorname {spike}\left(1 - (1 - \frac{(t)^{2} \cdot \left(p - 1\right)}{p})^{n}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.sum_spike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent sum of n products has uniform weight 1−(1−s)^n, with s=t²(p−1)/p. The product-law identity and the convolution identity prove this for every n.

**Theorem 1.19 (weight bounds).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall k \in \mathbb {N},\; (3 \le k) \Rightarrow ((0 \le \frac{1}{k}) \land ((\frac{1}{k} \le 1) \land ((0 \le \frac{(\frac{1}{k})^{2} \cdot \left(p - 1\right)}{p}) \land ((\frac{(\frac{1}{k})^{2} \cdot \left(p - 1\right)}{p} \le 1) \land ((0 \le 1 - (1 - \frac{(\frac{1}{k})^{2} \cdot \left(p - 1\right)}{p})^{k}) \land ((1 - (1 - \frac{(\frac{1}{k})^{2} \cdot \left(p - 1\right)}{p})^{k} \le k \cdot \frac{(\frac{1}{k})^{2} \cdot \left(p - 1\right)}{p}) \land (k \cdot \frac{(\frac{1}{k})^{2} \cdot \left(p - 1\right)}{p} < \frac{1}{k}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.weight_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At t=1/k, Bernoulli's inequality gives 0≤r≤ks<1/k, while both t and s lie in [0,1].

**Theorem 1.20 (violation).**

$$\forall p \in \mathbb {N},\; (\operatorname {Nat.Prime}\left(p\right)) \Rightarrow (\forall k \in \mathbb {N},\; (3 \le k) \Rightarrow (((2)^{2 \cdot k} < p) \Rightarrow (\operatorname {Hbits}\left(\operatorname {sumLaw}\left(k, \operatorname {spike}\left(\frac{1}{k}\right)\right)\right) < \operatorname {min}\left(2 \cdot \operatorname {Hbits}\left(\operatorname {spike}\left(\frac{1}{k}\right)\right), \operatorname {Real.logb}\left(2, p\right)\right) - 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.violation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing L=log₂ p, the input entropy is at least L/k and the sum entropy at most 1+L/k. Since 2L/k≤L and L>2k, the margin in (89) is strictly greater than zero. This holds for every k≥3 and every prime above the displayed threshold.

**Theorem 1.21 (Refutation for every proposed fixed integer).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GohGlibichukKonyagin/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/goh-2026-entropic-glibichuk-konyagin` (refuted) by `D5/S3/Entropy/GohGlibichukKonyagin/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"goh-2026-entropic-glibichuk-konyagin","declaration_gid":"D5/S3/Entropy/GohGlibichukKonyagin/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. K. Goh (2026). *On an entropic analogue of additive energy*. DOI: [10.2140/ent.2026.5.243](https://doi.org/10.2140/ent.2026.5.243). URL: <https://arxiv.org/abs/2406.18798v4>.

*Commentary.*

For any proposed k, the infinitude of primes supplies a prime p>2^(2k). The nonnegative normalized spike law with t=1/k contradicts the claimed inequality by the strict violation. There are infinitely many primes above every fixed threshold. The conclusion proves that Conjecture 15 cannot supply the paper's route to Conjecture 14; Conjecture 14 itself remains open.

## References

- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.Hbits`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.card_pos`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.claim`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.conv`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.conv_eq_sum`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.conv_mul`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.conv_spike`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.delta`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.iterLaw`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.iter_product`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.mulLaw`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.mul_spike`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.result`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.spike`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.spike_entropy`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.spike_law`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.spike_sum`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.sumLaw`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.sum_spike`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.violation`
- Truth anchor: `D5/S3/Entropy/GohGlibichukKonyagin/Result.weight_bounds`
- Dependency: [D5/S3/Entropy/EntropyEquality](../EntropyEquality.md)
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Entropy/Mixing/MixtureEntropyBracket](../Mixing/MixtureEntropyBracket.md)
