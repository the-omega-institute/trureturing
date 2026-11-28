---
slug: blecher-2025-example-5-5-no-anticommuting-pair
bibkey: blecher2025commutativity
doi: 10.1016/j.exmath.2025.125742
url: https://arxiv.org/html/2509.17673v2#S5.Thmtheorem5
triage: theorem
motivation_gids:
  - D5/S3/HilbertOperators/BlecherNoAnticommutingPair.result
---

# Blecher's question about a nonzero anticommuting product

## Problem

After exhibiting a nonzero anticommuting product, Example 5.5 asks for an example with no such pair. The surrounding discussion requires noncommutativity. An algebra answers the question if it is reversible and every equality $xy=-yx$ in the algebra forces $xy=0$. The finite witness uses the stronger hypothesis of symmetry, where transpose preserves every amplified operator norm. [Blecher, Example 5.5](https://arxiv.org/html/2509.17673v2#S5.Thmtheorem5)

## Result

The witness is the image of the complex-linear representation of $\mathbb C^{1\times 2}\oplus M_2(\mathbb C)$ whose product is $(r,Z)(s,W)=(0,r^Ts)$. Four probes, consisting of the identity, a diagonal sign change, a coordinate swap and a signed coordinate swap, give a faithful representation in $M_{16}(\mathbb C)$. The image is a finite-dimensional closed subalgebra. Every amplification preserves its operator norm under entrywise transpose, which reverses the product. The argument refutes the necessity of a nonzero anticommuting product already among noncommutative symmetric subalgebras of $M_{16}(\mathbb C)$. [Preregistration #35141](https://github.com/the-omega-institute/trureturing/issues/35141)
