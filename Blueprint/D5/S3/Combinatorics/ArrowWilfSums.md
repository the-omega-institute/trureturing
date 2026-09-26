# Finite Sums for the Arrow-Wilf Equivalence

## Abstract

Two finite avoidance formulas have the same signed correction term.

**Definition 1.1 (The first finite counting formula).**

$$\forall n \in \mathrm{Nat},\; \operatorname{F1}\left(n\right) = \operatorname{numDerangements}\left(n\right) + \sum _{m\in \operatorname{Icc}\left(1, n\right)} (\sum _{k\in \operatorname{range}\left(n - m + 1\right)} (\operatorname{choose}\left(n - m, k\right) \cdot \operatorname{choose}\left(m + k - 1, n - m\right) \cdot \operatorname{numDerangements}\left(k\right)))$$

*Formalization.* `D5/S3/Combinatorics/ArrowWilfSums.F1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

F1 adds the n-th derangement number to the double sum indexed by 1 at most m at most n and 0 at most k at most n minus m, with factors choose(n minus m,k), choose(m plus k minus one,n minus m), and the k-th derangement number.

**Definition 1.2 (The second finite counting formula).**

$$\forall n \in \mathrm{Nat},\; \operatorname{F2}\left(n\right) = \operatorname{numDerangements}\left(n\right) + \operatorname{numDerangements}\left(n - 1\right) + \sum _{m\in \operatorname{Icc}\left(1, n - 1\right)} (\sum _{r\in \operatorname{range}\left(m\right)} (\operatorname{choose}\left(m - 1, r\right) \cdot \operatorname{choose}\left(n - m + r - 1, r\right) \cdot \operatorname{factorial}\left(r\right) \cdot \operatorname{numDerangements}\left(m - 1 - r\right)))$$

*Formalization.* `D5/S3/Combinatorics/ArrowWilfSums.F2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

F2 adds the n-th and (n minus one)-st derangement numbers to the double sum indexed by 1 at most m less than n and 0 at most r less than m, with factors choose(m minus one,r), choose(n minus m plus r minus one,r), r factorial, and the (m minus one minus r)-th derangement number.

**Theorem 1.3 (The reversed hockey-stick identity).**

$$\forall n \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \left(i \le t \land t + 2 \le n\right) \Rightarrow \sum _{k\in \operatorname{Icc}\left(i, t\right)} (\operatorname{choose}\left(n - k - 2, t - k\right)) = \operatorname{choose}\left(n - i - 1, t - i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfSums.reversed_hockey_stick` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For i at most t and t plus two at most n, summing choose(n minus k minus two,t minus k) over k from i through t gives choose(n minus i minus one,t minus i).

**Theorem 1.4 (Weighted triangular-sum transform).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfSums.weighted_hockey_transform`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfSums.weighted_hockey_transform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Over any commutative semiring, reversing the triangular sums against weights a(i) replaces the inner hockey-stick sum by choose(n minus i minus one,t minus i).

**Definition 1.5 (The common signed sum).**

$$\forall n \in \mathrm{Nat},\; \operatorname{E}\left(n\right) = \sum _{t\in \operatorname{range}\left(n\right)} (\sum _{i\in \operatorname{range}\left(t + 1\right)} (\left(-1\right)^{i} \cdot \operatorname{ascFactorial}\left(i + 1, t - i\right) \cdot \operatorname{choose}\left(n - i - 1, t - i\right)))$$

*Formalization.* `D5/S3/Combinatorics/ArrowWilfSums.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

E(n) is the integer double sum over zero at most t less than n and zero at most i at most t of minus one to the i times the ascending factorial from i plus one of length t minus i times choose(n minus i minus one,t minus i).

**Theorem 1.6 (Reindexing the second correction).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfSums.f2_correction_reindexed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfSums.f2_correction_reindexed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The sum in F2 without its two derangement terms can be reindexed with t equal to m minus one and k equal to t minus r, producing a triangular sum over t and k.

**Theorem 1.7 (Each inner sum becomes a signed inner sum).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfSums.f2_inner_eq_E_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfSums.f2_inner_eq_E_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For t plus two at most n, the reindexed positive inner sum equals the t-th inner integer sum in E(n), after inclusion-exclusion and the weighted hockey-stick transform.

**Theorem 1.8 (The second correction equals E).**

$$\forall n \in \mathrm{Nat},\; 1 \le n \Rightarrow (\operatorname{numDerangements}\left(n - 1\right): \mathbb{Z}) + (\sum _{m\in \operatorname{Icc}\left(1, n - 1\right)} (\sum _{r\in \operatorname{range}\left(m\right)} (\operatorname{choose}\left(m - 1, r\right) \cdot \operatorname{choose}\left(n - m + r - 1, r\right) \cdot \operatorname{factorial}\left(r\right) \cdot \operatorname{numDerangements}\left(m - 1 - r\right))): \mathbb{Z}) = \operatorname{E}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfSums.f2_correction_eq_E` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For positive n, the (n minus one)-st derangement number plus the double-sum correction in F2 equals E(n). The derangement term supplies the missing boundary index t equal to n minus one.

**Theorem 1.9 (Reindexing the first correction).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfSums.f1_correction_reindexed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfSums.f1_correction_reindexed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The double sum in F1 can be reindexed by t equal to n minus m and k in the range zero through t; its coefficients become choose(n minus t plus k minus one,k) times choose(n minus t minus one,t minus k).

**Definition 1.10 (A positive finite transform).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfSums.positiveTransform`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfSums.positiveTransform` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The positive transform at p,t sums choose(p plus k,k) times choose(p,t minus k) times the k-th derangement number over k from zero through t.

**Theorem 1.11 (Recurrence for the positive transform).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfSums.positiveTransform_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfSums.positiveTransform_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Multiplying the transform at p plus one,t plus one by p plus one gives the sum of p plus t plus two times the transform at p,t plus one and t plus one times the transform at p,t.

**Definition 1.12 (A signed finite transform).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfSums.signedTransform`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfSums.signedTransform` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The signed transform at p,t sums minus one to the i times an ascending factorial and choose(p plus t minus i,t minus i) over i from zero through t.

**Theorem 1.13 (Recurrence for the signed transform).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfSums.signedTransform_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfSums.signedTransform_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The signed transform satisfies the same two-variable recurrence as the positive transform, with all terms interpreted as integers.

**Theorem 1.14 (Equality of the two finite transforms).**

$$\forall p \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; (\operatorname{positiveTransform}\left(p, t\right): \mathbb{Z}) = \operatorname{signedTransform}\left(p, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfSums.positiveTransform_eq_signedTransform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For all natural p and t, the integer cast of the positive transform equals the signed transform.

**Theorem 1.15 (The first correction equals E).**

$$\forall n \in \mathrm{Nat},\; (\sum _{m\in \operatorname{Icc}\left(1, n\right)} (\sum _{k\in \operatorname{range}\left(n - m + 1\right)} (\operatorname{choose}\left(n - m, k\right) \cdot \operatorname{choose}\left(m + k - 1, n - m\right) \cdot \operatorname{numDerangements}\left(k\right))): \mathbb{Z}) = \operatorname{E}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfSums.f1_correction_eq_E` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For every natural n, the double-sum correction in F1, cast to the integers, equals E(n) after reindexing and the finite transform identity.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.E`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.F1`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.F2`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.f1_correction_eq_E`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.f1_correction_reindexed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.f2_correction_eq_E`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.f2_correction_reindexed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.f2_inner_eq_E_inner`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.positiveTransform`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.positiveTransform_eq_signedTransform`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.positiveTransform_recurrence`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.reversed_hockey_stick`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.signedTransform`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.signedTransform_recurrence`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfSums.weighted_hockey_transform`
