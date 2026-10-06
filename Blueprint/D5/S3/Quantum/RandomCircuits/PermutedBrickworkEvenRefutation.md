# Even-depth permuted brickwork fails positive semidefiniteness

## Abstract

For four sites, every local dimension q at least two and every even depth at least two give a permuted-brickwork Haar moment with a strictly negative quadratic form.

**Definition 1.1 (The three complete matchings).**

$$\forall m \in \operatorname{Fin}\left(3\right),\; \operatorname{matching}\left(m\right) = \operatorname{ite}\left(m = 0, ![(0, 1), (2, 3)], \operatorname{ite}\left(m = 1, ![(0, 2), (1, 3)], ![(0, 3), (1, 2)]\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.matching` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

Section 5.2 (page 12): "Suppose we draw a random two-sided matching of the sites, then apply a layer of Haar-random 2-site gates to those pairs in parallel." The source sites are numbered 0,1,2,3 here. Matching indices 0,1,2 denote A,B,C, respectively.

**Definition 1.2 (Restricting the replicas to one edge).**

$$\forall q \in \mathbb{N},\; \forall p \in (\operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right)),\; \forall r \in (((\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right))) \times ((\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)))),\; \operatorname{restrictReplica}\left(p, r\right) = (((r.1.1\left(p.1\right), r.1.1\left(p.2\right)), (r.1.2\left(p.1\right), r.1.2\left(p.2\right))), ((r.2.1\left(p.1\right), r.2.1\left(p.2\right)), (r.2.2\left(p.1\right), r.2.2\left(p.2\right))))$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.restrictReplica` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

Each of the four replicas is restricted to the two endpoints in their displayed order. Their order remains barred one, barred two, unbarred one, unbarred two.

**Definition 1.3 (A layer of independent Haar gates).**

$$\forall q \in \mathbb{N},\; \forall m \in \operatorname{Fin}\left(3\right),\; \forall r \in (((\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right))) \times ((\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)))),\; \forall c \in (((\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right))) \times ((\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)))),\; \operatorname{layerMoment}\left(q, m\right)\left(r, c\right) = \prod_{e: \operatorname{Fin}\left(2\right)} (\operatorname{haarAverage}\left((\operatorname{Fin}\left(q\right) \times \operatorname{Fin}\left(q\right))\right)\left(\operatorname{restrictReplica}\left(\operatorname{matching}\left(m\right)\left(e\right), r\right), \operatorname{restrictReplica}\left(\operatorname{matching}\left(m\right)\left(e\right), c\right)\right))$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.layerMoment` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The two disjoint pairs in a matching receive independent normalized Haar gates on Matrix.unitaryGroup (Fin q times Fin q) over the complex numbers. The matrix entry is the product of their literal four-factor expectations.

**Definition 1.4 (A circuit word).**

$$\forall q \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(3\right)),\; \operatorname{wordMoment}\left(q, d, w\right) = \operatorname{List.prod}\left(\operatorname{List.map}\left(\lambda i: \operatorname{Fin}\left(d\right), \operatorname{layerMoment}\left(q, w\left(i\right)\right), \operatorname{List.reverse}\left(\operatorname{List.finRange}\left(d\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.wordMoment` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The circuit product is U_(d-1) ... U_0. The layer-moment matrices therefore multiply in reverse index order, as in the actual circuit.

**Definition 1.5 (The connected-block condition on four sites).**

$$\forall d \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(3\right)),\; \operatorname{NoRepeat}\left(d, w\right) = \left(\forall i \in \mathbb{N},\; (i + 1 < d) \Rightarrow (w\left(\operatorname{Fin.mk}\left(i, \mathord{\cdot}\right)\right) \ne w\left(\operatorname{Fin.mk}\left(i + 1, \mathord{\cdot}\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.NoRepeat` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

Section 5.2 (page 12): "Suppose we draw layers as in the parallel complete-graph architecture, except that we require each adjacent pair of layers to form a connected block." On four sites, two equal matchings have two connected components, while any two distinct matchings have a four-cycle as their union. Thus connected union is exactly the condition that adjacent matching indices differ. The Fin.mk arguments retain the bounds supplied by i+1 < d.

**Definition 1.6 (The admissible words).**

$$\forall d \in \mathbb{N},\; \operatorname{admissibleWords}\left(d\right) = \operatorname{Finset.filter}\left(\operatorname{NoRepeat}\left(d\right), (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(3\right))\right))\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.admissibleWords` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

All matching words of length d are filtered by the connected-block condition. For positive depth their number is 3 times 2 to the power d-1.

**Definition 1.7 (The uniform circuit expectation).**

$$\forall q \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{vecPhi}\left(q, d\right) = (((\operatorname{Finset.card}\left(\operatorname{admissibleWords}\left(d\right)\right): \mathbb{C}))^{-1}) \cdot (\sum_{w \in \operatorname{admissibleWords}\left(d\right)} \operatorname{wordMoment}\left(q, d, w\right))$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.vecPhi` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

Section 2.1 (page 3) gives vec(Phi_epsilon) = E[U* tensor U* tensor U tensor U]. Here the expectation is the uniform average of the circuit-ordered layer-moment products over all admissible matching words; independent gates have already been integrated inside each layer. The reciprocal cardinality is taken in the complex numbers.

**Definition 1.8 (Four-site permutation vectors).**

$$\forall q \in \mathbb{N},\; \forall b \in (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right)),\; \forall r \in (((\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right))) \times ((\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(q\right)))),\; \operatorname{permutationVector}\left(q, b\right)\left(r\right) = \prod_{s: \operatorname{Fin}\left(4\right)} (\operatorname{sitePermutation}\left(q, b\left(s\right), ((r.1.1\left(s\right), r.1.2\left(s\right)), (r.2.1\left(s\right), r.2.2\left(s\right)))\right))$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.permutationVector` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The four-site physical vector is the tensor product of the normalized one-site identity or swap vectors. No orthonormal coefficient basis is substituted for these physical vectors.

**Definition 1.9 (The antisymmetric physical vector).**

$$\forall q \in \mathbb{N},\; \operatorname{physicalWitness}\left(q\right) = \operatorname{permutationVector}\left(q, ![0, 1, 0, 1]\right) - \operatorname{permutationVector}\left(q, ![0, 1, 1, 0]\right) - \operatorname{permutationVector}\left(q, ![1, 0, 0, 1]\right) + \operatorname{permutationVector}\left(q, ![1, 0, 1, 0]\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.physicalWitness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The vector is (|01>-|10>) on sites 0,1 tensored with (|01>-|10>) on sites 2,3, expressed in the nonorthogonal physical identity/swap vectors. Its squared norm is 4(1-q^(-2)) squared, which is positive for q at least two.

**Definition 1.10 (The even-depth question).**

$$claim = \left(\forall q \in \mathbb{N},\; (2 \le q) \Rightarrow (\forall d \in \mathbb{N},\; (2 \le d) \Rightarrow ((\operatorname{Even}\left(d\right)) \Rightarrow (\neg \operatorname{Matrix.PosSemidef}\left(\operatorname{vecPhi}\left(q, d\right)\right))))\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

Section 5.2 (page 12): "Like the brickwork, this architecture can be shown to have a PSD vectorization if the depth is odd. It is unclear if the vectorization is PSD at even depths." The displayed claim is the negative answer on four sites: all q at least two and all even d at least two fail Matrix.PosSemidef.

**Theorem 1.11 (Failure at every even depth).**

$$\forall q \in \mathbb{N},\; (2 \le q) \Rightarrow (\forall d \in \mathbb{N},\; (2 \le d) \Rightarrow ((\operatorname{Even}\left(d\right)) \Rightarrow (\neg \operatorname{Matrix.PosSemidef}\left(\operatorname{vecPhi}\left(q, d\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

Put a=q/(q squared + 1) and h=(q to the fourth + 1)/(q squared + 1) squared. The sum of the three layer projections has eigenvalue h on the physical vector. The unnormalized no-repeat word sum R obeys R_(d+1)=(S-I)R_d, while the word count is 3 times 2 to the power d-1. The average therefore has eigenvalue (h/3)(-a squared) to the power d-1 on this vector. Multiplying by its strictly positive squared norm gives a negative real quadratic form at every even depth. At q=2,d=2 this form is -51/625. A positive semidefinite matrix must have nonnegative quadratic forms, giving the contradiction.

## References

- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.NoRepeat`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.admissibleWords`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.claim`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.layerMoment`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.matching`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.permutationVector`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.physicalWitness`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.restrictReplica`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.result`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.vecPhi`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.wordMoment`
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](HaarTwoCopyTwirl.md)
