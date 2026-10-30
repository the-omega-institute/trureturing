# Quantified finite-prefix convolution correction and higher-arity evil-odious monotonicity

## Abstract

Ordered k-tuple representation counts over the evil and odious supports evolve in arity by discrete convolution against binary-valued indicators satisfying adjacent-pair complementation a(2q) + a(2q + 1) = 1. A general signed forward-difference identity splits the convolution increment above any finite cutoff R into a nonnegative boundary term, a finite prefix whose negative variation is bounded by V_R(f), and a tail bounded below by floor((n - R + 1) / 2), forcing strict increase for all n >= R + 2 V_R(f) + 1 and, under weak-composition binomial bounds on f, for all n >= R + 2 choose(R + k - 1, k) + 1. Propagating from the sixfold thresholds r_6(n) < r_6(n + 1) for n >= 37 and s_6(n) < s_6(n + 1) for n >= 5 yields explicit quantitative strict monotonicity across every arity k >= 6, together with sharp odious strict monotonicity s_k(n) < s_k(n + 1) for all k >= 6 and n >= k - 1 via the shifted odious bijection s_k(n) = q_k(n - k).

**Definition 1.1 (Binary indicator of the evil support).**

$$\forall n \in \mathbb{N},\; \operatorname{evilInd}\left(n\right) = \operatorname{if} \operatorname{thueMorse}\left(n\right) = \operatorname{false} \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.evilInd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

For each natural number n, evilInd n takes value 1 when thueMorse n = false (even binary digit sum) and value 0 when thueMorse n = true.

**Definition 1.2 (Binary indicator of the odious support).**

$$\forall n \in \mathbb{N},\; \operatorname{odiousInd}\left(n\right) = \operatorname{if} \operatorname{thueMorse}\left(n\right) = \operatorname{true} \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.odiousInd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

For each natural number n, odiousInd n takes value 1 when thueMorse n = true (odd binary digit sum) and value 0 when thueMorse n = false.

**Definition 1.3 (Discrete convolution of natural-valued sequences).**

$$\forall a \in \mathbb{N} \to \mathbb{N},\; \forall f \in \mathbb{N} \to \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{natConv}\left(a, f, n\right) = \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} a\left(j\right) \cdot f\left(n - j\right)$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.natConv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Given sequences a, f : N -> N and index n : N, natConv a f n sums a(j) f(n - j) over 0 <= j <= n using Finset.range (n + 1).

**Definition 1.4 (Ordered tuple representation count over the shifted odious support).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{shiftedOdious}\left(k, m\right) = ((\operatorname{Finset}.\operatorname{Nat}.\operatorname{antidiagonalTuple}\left(k, m\right)).\operatorname{filter} (\operatorname{fun} (b : \operatorname{Fin}\left(k\right) \to \mathbb{N}) \mapsto \forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{thueMorse}\left(b\left(i\right) + 1\right) = \operatorname{true})).\operatorname{card}$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.shiftedOdious` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Because 0 is evil and 1 is odious, shifting every positive odious coordinate x_i to b_i = x_i - 1 maps ordered k-tuples of odious numbers summing to n >= k bijectively onto ordered k-tuples b in Finset.Nat.antidiagonalTuple k (n - k) satisfying thueMorse (b_i + 1) = true for all i, counted by shiftedOdious k.

**Definition 1.5 (Ordered tuple representation count over the positive shifted evil support E + 1).**

$$\forall k \in \mathbb{N},\; \forall N \in \mathbb{N},\; \operatorname{positiveEvilCount}\left(k, N\right) = ((\operatorname{Finset}.\operatorname{Nat}.\operatorname{antidiagonalTuple}\left(k, N\right)).\operatorname{filter} (\operatorname{fun} (x : \operatorname{Fin}\left(k\right) \to \mathbb{N}) \mapsto \forall i \in \operatorname{Fin}\left(k\right),\; (1 \le x\left(i\right)) \land (\operatorname{thueMorse}\left(x\left(i\right) - 1\right) = \operatorname{false}))).\operatorname{card}$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.positiveEvilCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

For arity k and sum N, positiveEvilCount k N counts ordered k-tuples x summing to N whose coordinates satisfy x_i >= 1 and thueMorse (x_i - 1) = false, corresponding to ordered representations over E + 1 = {e + 1 : e in E}.

**Definition 1.6 (Ordered tuple representation count over the positive shifted odious support O + 1).**

$$\forall k \in \mathbb{N},\; \forall N \in \mathbb{N},\; \operatorname{positiveOdiousCount}\left(k, N\right) = ((\operatorname{Finset}.\operatorname{Nat}.\operatorname{antidiagonalTuple}\left(k, N\right)).\operatorname{filter} (\operatorname{fun} (x : \operatorname{Fin}\left(k\right) \to \mathbb{N}) \mapsto \forall i \in \operatorname{Fin}\left(k\right),\; (1 \le x\left(i\right)) \land (\operatorname{thueMorse}\left(x\left(i\right) - 1\right) = \operatorname{true}))).\operatorname{card}$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.positiveOdiousCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

For arity k and sum N, positiveOdiousCount k N counts ordered k-tuples x summing to N whose coordinates satisfy x_i >= 1 and thueMorse (x_i - 1) = true, corresponding to ordered representations over O + 1 = {o + 1 : o in O}.

**Definition 1.7 (Signed integer forward difference).**

$$\forall f \in \mathbb{N} \to \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{fwdDiff}\left(f, m\right) = (f\left(m + 1\right) : \mathbb{Z}) - (f\left(m\right) : \mathbb{Z})$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.fwdDiff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

For a natural-valued sequence f : N -> N and index m : N, fwdDiff f m casts f(m + 1) and f(m) to Z before subtracting so negative increments on finite prefixes are preserved without natural-number truncation.

**Definition 1.8 (Nonnegative integer negative part).**

$$\forall u \in \mathbb{Z},\; \operatorname{negPart}\left(u\right) = \operatorname{max}\left((0 : \mathbb{Z}), -u\right)$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.negPart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

For an integer u, negPart u = max(0, -u) isolates the magnitude of negative excursions while assigning 0 to nonnegative values and satisfying -negPart u <= u.

**Definition 1.9 (Integer-valued cumulative negative forward-difference variation).**

$$\forall R \in \mathbb{N},\; \forall f \in \mathbb{N} \to \mathbb{N},\; \operatorname{prefixVarInt}\left(R, f\right) = \sum_{m \in \operatorname{Finset}.\operatorname{range}\left(R\right)} \operatorname{negPart}\left(\operatorname{fwdDiff}\left(f, m\right)\right)$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.prefixVarInt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

On a finite prefix 0 <= m < R, prefixVarInt R f sums negPart (fwdDiff f m) in Z, producing a nonnegative integer upper bound on the total downward variation of f prior to the threshold R.

**Definition 1.10 (Natural-valued cumulative negative forward-difference variation).**

$$\forall R \in \mathbb{N},\; \forall f \in \mathbb{N} \to \mathbb{N},\; \operatorname{prefixVar}\left(R, f\right) = (\operatorname{prefixVarInt}\left(R, f\right)).\operatorname{toNat}$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.prefixVar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Applying Int.toNat to the nonnegative sum prefixVarInt R f produces the natural number prefixVar R f satisfying (prefixVar R f : Z) = prefixVarInt R f.

**Definition 1.11 (Recursive sufficient threshold sequence for higher-arity evil strict monotonicity).**

$$(\operatorname{evilBound}\left(0\right) = 37) \land (\forall k \in \mathbb{N},\; \operatorname{evilBound}\left(k + 1\right) = \operatorname{if} k < 6 \operatorname{then} 37 \operatorname{else} \operatorname{evilBound}\left(k\right) + 2 \cdot \operatorname{Nat}.\operatorname{choose}\left(\operatorname{evilBound}\left(k\right) + k - 1, k\right) + 1)$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.evilBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Seeded at evilBound 6 = 37 (with constant placeholder 37 below arity 6), evilBound evolves for every k >= 6 by evilBound (k + 1) = evilBound k + 2 choose(evilBound k + k - 1, k) + 1.

**Definition 1.12 (Recursive sufficient threshold sequence for higher-arity odious strict monotonicity).**

$$(\operatorname{odiousBound}\left(0\right) = 5) \land (\forall k \in \mathbb{N},\; \operatorname{odiousBound}\left(k + 1\right) = \operatorname{if} k < 6 \operatorname{then} 5 \operatorname{else} \operatorname{odiousBound}\left(k\right) + 2 \cdot \operatorname{Nat}.\operatorname{choose}\left(\operatorname{odiousBound}\left(k\right) + k - 1, k\right) + 1)$$

*Formalization.* `D5/S1/Words/EvilOdious/HigherArityMonotonicity.odiousBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Seeded at odiousBound 6 = 5 (with constant placeholder 5 below arity 6), odiousBound evolves for every k >= 6 by odiousBound (k + 1) = odiousBound k + 2 choose(odiousBound k + k - 1, k) + 1.

**Theorem 1.13 (Adjacent-pair complementation, convolution recurrences, composition bounds, and positive shift).**

$$(\forall q \in \mathbb{N},\; \operatorname{evilInd}\left(2 \cdot q\right) + \operatorname{evilInd}\left(2 \cdot q + 1\right) = 1) \land ((\forall q \in \mathbb{N},\; \operatorname{odiousInd}\left(2 \cdot q\right) + \operatorname{odiousInd}\left(2 \cdot q + 1\right) = 1) \land ((\forall n \in \mathbb{N},\; ((\operatorname{evilInd}\left(n\right) = 0) \lor (\operatorname{evilInd}\left(n\right) = 1)) \land (((\operatorname{odiousInd}\left(n\right) = 0) \lor (\operatorname{odiousInd}\left(n\right) = 1)) \land ((r\left(1, n\right) = \operatorname{evilInd}\left(n\right)) \land (s\left(1, n\right) = \operatorname{odiousInd}\left(n\right))))) \land ((\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; (r\left(k + 1, n\right) = \operatorname{natConv}\left(\operatorname{evilInd}, (r\left(k\right)), n\right)) \land (s\left(k + 1, n\right) = \operatorname{natConv}\left(\operatorname{odiousInd}, (s\left(k\right)), n\right))) \land ((\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; (1 \le k) \Rightarrow ((r\left(k, n\right) \le \operatorname{Nat}.\operatorname{choose}\left(n + k - 1, k - 1\right)) \land (s\left(k, n\right) \le \operatorname{Nat}.\operatorname{choose}\left(n + k - 1, k - 1\right)))) \land (\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; (\operatorname{positiveEvilCount}\left(k, n + k\right) = r\left(k, n\right)) \land (\operatorname{positiveOdiousCount}\left(k, n + k\right) = s\left(k, n\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/HigherArityMonotonicity.evil_odious_pair_convolution_and_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

From thueMorse (2q) = thueMorse q and thueMorse (2q + 1) = !thueMorse q, both evilInd and odiousInd take values in {0, 1}, satisfy adjacent-pair complementation a(2q) + a(2q + 1) = 1, and agree with r_1 and s_1. Partitioning Finset.Nat.antidiagonalTuple (k + 1) n fiberwise by the initial coordinate j and pairing fibers with Finset.Nat.antidiagonalTuple k (n - j) via Fin.cons and Fin.tail establishes r_{k + 1} = natConv evilInd r_k, s_{k + 1} = natConv odiousInd s_k, and weak-composition cardinality choose(n + k - 1, k - 1) for k >= 1, whence r_k(n) and s_k(n) are bounded above by choose(n + k - 1, k - 1). Coordinatewise addition of 1 gives positiveEvilCount k (n + k) = r_k(n) and positiveOdiousCount k (n + k) = s_k(n).

**Theorem 1.14 (Quantified finite-prefix convolution correction and binomial variation bound).**

$$\forall a \in \mathbb{N} \to \mathbb{N},\; \forall f \in \mathbb{N} \to \mathbb{N},\; \forall R \in \mathbb{N},\; (\forall q \in \mathbb{N},\; a\left(2 \cdot q\right) + a\left(2 \cdot q + 1\right) = 1) \Rightarrow ((\forall m \in \mathbb{N},\; (R \le m) \Rightarrow ((1 : \mathbb{Z}) \le \operatorname{fwdDiff}\left(f, m\right))) \Rightarrow ((\forall m \in \mathbb{N},\; (a\left(m\right) = 0) \lor (a\left(m\right) = 1)) \land (((\operatorname{prefixVar}\left(R, f\right) : \mathbb{Z}) = \operatorname{prefixVarInt}\left(R, f\right)) \land ((\forall n \in \mathbb{N},\; (R \le n) \Rightarrow ((\operatorname{fwdDiff}\left(\operatorname{natConv}\left(a, f\right), n\right) = (a\left(n + 1\right) : \mathbb{Z}) \cdot (f\left(0\right) : \mathbb{Z}) + \sum_{m \in \operatorname{Finset}.\operatorname{range}\left(R\right)} (a\left(n - m\right) : \mathbb{Z}) \cdot \operatorname{fwdDiff}\left(f, m\right) + \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(n - R + 1\right)} (a\left(j\right) : \mathbb{Z}) \cdot \operatorname{fwdDiff}\left(f, n - j\right)) \land (((a\left(n + 1\right) : \mathbb{Z}) \cdot (f\left(0\right) : \mathbb{Z}) + (((n - R + 1) / 2) : \mathbb{Z}) - \sum_{m \in \operatorname{Finset}.\operatorname{range}\left(R\right)} (a\left(n - m\right) : \mathbb{Z}) \cdot \operatorname{negPart}\left(\operatorname{fwdDiff}\left(f, m\right)\right) \le \operatorname{fwdDiff}\left(\operatorname{natConv}\left(a, f\right), n\right)) \land (((a\left(n + 1\right) : \mathbb{Z}) \cdot (f\left(0\right) : \mathbb{Z}) + (((n - R + 1) / 2) : \mathbb{Z}) - \operatorname{prefixVarInt}\left(R, f\right) \le (a\left(n + 1\right) : \mathbb{Z}) \cdot (f\left(0\right) : \mathbb{Z}) + (((n - R + 1) / 2) : \mathbb{Z}) - \sum_{m \in \operatorname{Finset}.\operatorname{range}\left(R\right)} (a\left(n - m\right) : \mathbb{Z}) \cdot \operatorname{negPart}\left(\operatorname{fwdDiff}\left(f, m\right)\right)) \land ((a\left(n + 1\right) : \mathbb{Z}) \cdot (f\left(0\right) : \mathbb{Z}) + (((n - R + 1) / 2) : \mathbb{Z}) - \operatorname{prefixVarInt}\left(R, f\right) \le \operatorname{fwdDiff}\left(\operatorname{natConv}\left(a, f\right), n\right)))))) \land ((\forall n \in \mathbb{N},\; (R + 2 \cdot \operatorname{prefixVar}\left(R, f\right) + 1 \le n) \Rightarrow ((1 : \mathbb{Z}) \le \operatorname{fwdDiff}\left(\operatorname{natConv}\left(a, f\right), n\right))) \land ((\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\sum_{m \in \operatorname{Finset}.\operatorname{range}\left(R\right)} \operatorname{Nat}.\operatorname{choose}\left(m + k - 1, k - 1\right) = \operatorname{Nat}.\operatorname{choose}\left(R + k - 1, k\right))) \land (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow ((\forall m \in \mathbb{N},\; f\left(m\right) \le \operatorname{Nat}.\operatorname{choose}\left(m + k - 1, k - 1\right)) \Rightarrow ((\operatorname{prefixVar}\left(R, f\right) \le \operatorname{Nat}.\operatorname{choose}\left(R + k - 1, k\right)) \land (\forall n \in \mathbb{N},\; (R + 2 \cdot \operatorname{Nat}.\operatorname{choose}\left(R + k - 1, k\right) + 1 \le n) \Rightarrow ((1 : \mathbb{Z}) \le \operatorname{fwdDiff}\left(\operatorname{natConv}\left(a, f\right), n\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/HigherArityMonotonicity.quantified_finite_prefix_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Under adjacent-pair complementation a(2q) + a(2q + 1) = 1 in N, every value a(m) lies in {0, 1} and every prefix of length L satisfies sum_{j < L} a(j) >= floor(L / 2). Assuming fwdDiff f m >= 1 for all m >= R, splitting the exact convolution difference fwdDiff (natConv a f) n at n >= R into the boundary term a(n + 1) f(0), the reflected finite prefix 0 <= m < R, and the tail 0 <= j <= n - R yields the three-tier lower bound a(n + 1) f(0) + floor((n - R + 1) / 2) - prefixVarInt R f <= fwdDiff (natConv a f) n, forcing fwdDiff (natConv a f) n >= 1 for all n >= R + 2 prefixVar R f + 1. When f(m) <= choose(m + k - 1, k - 1) with k >= 1, bounding negPart (fwdDiff f m) <= f(m) and summing by the cumulative hockey-stick identity sum_{m < R} choose(m + k - 1, k - 1) = choose(R + k - 1, k) gives prefixVar R f <= choose(R + k - 1, k) and strict positivity of fwdDiff (natConv a f) n for n >= R + 2 choose(R + k - 1, k) + 1.

**Theorem 1.15 (Higher-arity quantitative strict monotonicity and sharp odious threshold).**

$$(\operatorname{evilBound}\left(6\right) = 37) \land ((\operatorname{odiousBound}\left(6\right) = 5) \land ((\forall k \in \mathbb{N},\; (6 \le k) \Rightarrow ((\operatorname{evilBound}\left(k + 1\right) = \operatorname{evilBound}\left(k\right) + 2 \cdot \operatorname{Nat}.\operatorname{choose}\left(\operatorname{evilBound}\left(k\right) + k - 1, k\right) + 1) \land (\operatorname{odiousBound}\left(k + 1\right) = \operatorname{odiousBound}\left(k\right) + 2 \cdot \operatorname{Nat}.\operatorname{choose}\left(\operatorname{odiousBound}\left(k\right) + k - 1, k\right) + 1))) \land ((\operatorname{evilBound}\left(7\right) = 38 + 2 \cdot \operatorname{Nat}.\operatorname{choose}\left(42, 6\right)) \land ((\operatorname{odiousBound}\left(7\right) = 426) \land ((\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow ((\operatorname{shiftedOdious}\left(k, 0\right) = 1) \land ((\forall n \in \mathbb{N},\; (n < k) \Rightarrow (s\left(k, n\right) = 0)) \land (\forall n \in \mathbb{N},\; (k \le n) \Rightarrow (s\left(k, n\right) = \operatorname{shiftedOdious}\left(k, n - k\right)))))) \land ((\forall k \in \mathbb{N},\; (6 \le k) \Rightarrow (\forall m \in \mathbb{N},\; \operatorname{shiftedOdious}\left(k, m\right) < \operatorname{shiftedOdious}\left(k, m + 1\right))) \land ((\forall k \in \mathbb{N},\; (6 \le k) \Rightarrow (\forall n \in \mathbb{N},\; (k - 1 \le n) \Rightarrow (s\left(k, n\right) < s\left(k, n + 1\right)))) \land ((\forall k \in \mathbb{N},\; (6 \le k) \Rightarrow (\forall n \in \mathbb{N},\; (\operatorname{evilBound}\left(k\right) \le n) \Rightarrow (r\left(k, n\right) < r\left(k, n + 1\right)))) \land (\forall k \in \mathbb{N},\; (6 \le k) \Rightarrow (\forall n \in \mathbb{N},\; (\operatorname{odiousBound}\left(k\right) \le n) \Rightarrow (s\left(k, n\right) < s\left(k, n + 1\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

Combining the sixfold strict monotonicity bounds r_6(n) < r_6(n + 1) for n >= 37 and s_6(n) < s_6(n + 1) for n >= 5 with evil_odious_pair_convolution_and_bound and quantified_finite_prefix_correction propagates r_k(n) < r_k(n + 1) for all k >= 6 and n >= evilBound k, with evilBound 7 = 38 + 2 choose(42, 6). On the odious branch, because 0 is not odious and 1 is odious, s_k(n) = 0 for n < k while s_k(n) = shiftedOdious k (n - k) for n >= k with shiftedOdious k 0 = 1. Since s_6 is strictly increasing from n = 5 <= 6, shiftedOdious 6 is strictly increasing on all of N; convolving against the shifted indicator b(j) with b(0) = 1 preserves global strict increase of shiftedOdious k for every k >= 6, giving sharp odious strict monotonicity s_k(n) < s_k(n + 1) for all n >= k - 1 and therefore also above odiousBound k >= k - 1 (with odiousBound 7 = 426).

## References

- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.evilBound`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.evilInd`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.evil_odious_pair_convolution_and_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.fwdDiff`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.higher_arity_evil_odious_strict_monotonicity`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.natConv`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.negPart`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.odiousBound`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.odiousInd`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.positiveEvilCount`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.positiveOdiousCount`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.prefixVar`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.prefixVarInt`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.quantified_finite_prefix_correction`
- Truth anchor: `D5/S1/Words/EvilOdious/HigherArityMonotonicity.shiftedOdious`
- Dependency: [D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd](../Complexity/ThueMorseReducedAbelianOdd.md)
- Dependency: [D5/S1/Words/EvilOdious/SequenceCoefficients](SequenceCoefficients.md)
- Dependency: [D5/S1/Words/EvilOdious/SixfoldMonotonicity](SixfoldMonotonicity.md)
