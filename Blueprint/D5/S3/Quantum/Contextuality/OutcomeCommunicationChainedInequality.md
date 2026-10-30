# The relabelled chained inequality for outcome communication

## Abstract

The relabelled chained inequality holds for every odd-input binary COD model.

**Definition 1.1 (Finite causal outcome-dependent models).**

$$\forall (n: \mathbb{N}), (\forall (\alpha: \operatorname{Type}), ([\operatorname{Fintype}\left(\alpha\right)], (\forall (w: (\alpha) \to (\mathbb{R})), (\forall (alice: (\operatorname{Fin}\left(n\right)) \to ((\alpha) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{R})))), (\forall (bob: (\operatorname{Fin}\left(n\right)) \to ((\alpha) \to ((\operatorname{Fin}\left(2\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{R}))))), ((\operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.IsCODModel}\left(w, alice, bob\right)) \Leftrightarrow ((\forall (l: \alpha), ((0: \mathbb{R}) \le w\left(l\right))) \land ((\sum_{(l: \alpha)} (w\left(l\right)) = (1: \mathbb{R})) \land ((\forall (x: \operatorname{Fin}\left(n\right)), (\forall (l: \alpha), (\forall (a: \operatorname{Fin}\left(2\right)), ((0: \mathbb{R}) \le alice\left(x, l, a\right))))) \land ((\forall (x: \operatorname{Fin}\left(n\right)), (\forall (l: \alpha), (\sum_{(a: \operatorname{Fin}\left(2\right))} (alice\left(x, l, a\right)) = (1: \mathbb{R})))) \land ((\forall (y: \operatorname{Fin}\left(n\right)), (\forall (l: \alpha), (\forall (a: \operatorname{Fin}\left(2\right)), (\forall (b: \operatorname{Fin}\left(2\right)), ((0: \mathbb{R}) \le bob\left(y, l, a, b\right)))))) \land (\forall (y: \operatorname{Fin}\left(n\right)), (\forall (l: \alpha), (\forall (a: \operatorname{Fin}\left(2\right)), (\sum_{(b: \operatorname{Fin}\left(2\right))} (bob\left(y, l, a, b\right)) = (1: \mathbb{R}))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.IsCODModel` (`✓ std3`).

*Citation.* Jonatan Bohr Brask and Rafael Chaves (2017). *Bell scenarios with communication*. DOI: [10.1088/1751-8121/aa5840](https://doi.org/10.1088/1751-8121/aa5840). URL: <https://arxiv.org/abs/1607.08182v1>.

*Commentary.*

A finite hidden-variable model has nonnegative weights summing to one. For each input and hidden value, Alice's binary response probabilities are nonnegative and normalized, and Bob's response probabilities are nonnegative and normalized for every raw Alice output. This is the finite formal reading of the causal outcome-dependent model in the source's equation (7), TeX lines 150–155.

**Definition 1.2 (The COD behaviour).**

$$\forall (n: \mathbb{N}), (\forall (\alpha: \operatorname{Type}), ([\operatorname{Fintype}\left(\alpha\right)], (\forall (w: (\alpha) \to (\mathbb{R})), (\forall (alice: (\operatorname{Fin}\left(n\right)) \to ((\alpha) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{R})))), (\forall (bob: (\operatorname{Fin}\left(n\right)) \to ((\alpha) \to ((\operatorname{Fin}\left(2\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{R}))))), (\forall (x: \operatorname{Fin}\left(n\right)), (\forall (y: \operatorname{Fin}\left(n\right)), (\forall (a: \operatorname{Fin}\left(2\right)), (\forall (b: \operatorname{Fin}\left(2\right)), (\operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.codBehaviour}\left(w, alice, bob, x, y, a, b\right) = \sum_{(l: \alpha)} (((w\left(l\right)) \cdot (alice\left(x, l, a\right))) \cdot (bob\left(y, l, a, b\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.codBehaviour` (`✓ std3`).

*Citation.* Jonatan Bohr Brask and Rafael Chaves (2017). *Bell scenarios with communication*. DOI: [10.1088/1751-8121/aa5840](https://doi.org/10.1088/1751-8121/aa5840). URL: <https://arxiv.org/abs/1607.08182v1>.

*Commentary.*

The behaviour is the weighted sum over hidden values of Alice's response at x and raw output a, followed by Bob's response at y conditioned on that same raw output. It is the factorization in the source's equation (7), TeX lines 150–155.

**Definition 1.3 (Alice's every-second-input relabelling).**

$$\forall (n: \mathbb{N}), (\forall (x: \operatorname{Fin}\left(n\right)), (\forall (a: \operatorname{Fin}\left(2\right)), (\operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.relabel}\left(x, a\right) = \operatorname{ite}\left((\operatorname{Nat.mod}\left(\operatorname{Fin.val}\left(x\right), 2\right) = 0), a, \operatorname{Fin.rev}\left(a\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.relabel` (`✓ std3`).

*Citation.* Jonatan Bohr Brask and Rafael Chaves (2017). *Bell scenarios with communication*. DOI: [10.1088/1751-8121/aa5840](https://doi.org/10.1088/1751-8121/aa5840). URL: <https://arxiv.org/abs/1607.08182v1>.

*Commentary.*

The binary output is unchanged when the natural index of x is even and is reversed otherwise. Nat.mod denotes natural-number remainder, and the source input number is Fin.val(x)+1. Thus the displayed inequality reads Alice's output with the flip on every second input, as specified in TeX line 325.

**Definition 1.4 (The relabelled chained expression).**

$$\forall (n: \mathbb{N}), (\forall (p: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(2\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{R}))))), (\operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.chainedValue}\left(n, p\right) = ((\sum_{(x: \operatorname{Fin}\left(n\right))} (\sum_{(c: \operatorname{Fin}\left(2\right))} (\sum_{(b: \operatorname{Fin}\left(2\right))} (\operatorname{ite}\left((c \ne b), p\left(x, x, \operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.relabel}\left(x, c\right), b\right), (0: \mathbb{R})\right))))) + (\sum_{(x: \operatorname{Fin}\left(n\right))} (\sum_{(y: \operatorname{Fin}\left(n\right))} (\operatorname{ite}\left((\operatorname{Fin.val}\left(x\right) = (\operatorname{Fin.val}\left(y\right)) + (1)), \sum_{(c: \operatorname{Fin}\left(2\right))} (\sum_{(b: \operatorname{Fin}\left(2\right))} (\operatorname{ite}\left((c \ne b), p\left(x, y, \operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.relabel}\left(x, c\right), b\right), (0: \mathbb{R})\right))), (0: \mathbb{R})\right))))) + (\sum_{(x: \operatorname{Fin}\left(n\right))} (\sum_{(y: \operatorname{Fin}\left(n\right))} (\operatorname{ite}\left(((\operatorname{Fin.val}\left(x\right) = 0) \land ((\operatorname{Fin.val}\left(y\right)) + (1) = n)), \sum_{(c: \operatorname{Fin}\left(2\right))} (\sum_{(b: \operatorname{Fin}\left(2\right))} (\operatorname{ite}\left((c = b), p\left(x, y, \operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.relabel}\left(x, c\right), b\right), (0: \mathbb{R})\right))), (0: \mathbb{R})\right))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.chainedValue` (`✓ std3`).

*Citation.* Jonatan Bohr Brask and Rafael Chaves (2017). *Bell scenarios with communication*. DOI: [10.1088/1751-8121/aa5840](https://doi.org/10.1088/1751-8121/aa5840). URL: <https://arxiv.org/abs/1607.08182v1>.

*Commentary.*

The expression sums the unequal-output diagonal terms, the unequal-output consecutive off-diagonal terms, and the equal-output closing term. The predicates on Fin.val select consecutive pairs and the pair from zero to n−1. This is equation (25) in the source, TeX lines 317–325, with the relabelling made explicit.

**Definition 1.5 (The finite odd-input COD inequality).**

$$(\operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.claim}\left(\right)) \Leftrightarrow (\forall (n: \mathbb{N}), ((\operatorname{Odd}\left(n\right)) \Rightarrow (\forall (\alpha: \operatorname{Type}), ([\operatorname{Fintype}\left(\alpha\right)], (\forall (w: (\alpha) \to (\mathbb{R})), (\forall (alice: (\operatorname{Fin}\left(n\right)) \to ((\alpha) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{R})))), (\forall (bob: (\operatorname{Fin}\left(n\right)) \to ((\alpha) \to ((\operatorname{Fin}\left(2\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{R}))))), ((\operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.IsCODModel}\left(w, alice, bob\right)) \Rightarrow ((1: \mathbb{R}) \le \operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.chainedValue}\left(n, \operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.codBehaviour}\left(w, alice, bob\right)\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonatan Bohr Brask and Rafael Chaves (2017). *Bell scenarios with communication*. DOI: [10.1088/1751-8121/aa5840](https://doi.org/10.1088/1751-8121/aa5840). URL: <https://arxiv.org/abs/1607.08182v1>.

*Commentary.*

For every odd natural number of inputs and every finite hidden-variable binary COD model, the relabelled chained expression is at least one. This is the precise finite formal reading of the conjecture in TeX lines 321–325.

**Theorem 1.6 (The odd-input COD inequality is proved).**

$$\operatorname{D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.result` (`✓ std3`). ∎

*Resolves.* `Problems/brask-chaves-2017-outcome-communication-chained-inequality` (proved) by `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"brask-chaves-2017-outcome-communication-chained-inequality","declaration_gid":"D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jonatan Bohr Brask and Rafael Chaves (2017). *Bell scenarios with communication*. DOI: [10.1088/1751-8121/aa5840](https://doi.org/10.1088/1751-8121/aa5840). URL: <https://arxiv.org/abs/1607.08182v1>.

*Commentary.*

Fix an odd n, a finite hidden-variable type, and a COD model. For a deterministic response table, the chained expression is a sum of nonnegative zero-or-one terms. If it were below one, every diagonal term and every consecutive off-diagonal term would vanish. The diagonal condition then identifies Bob's response on each raw Alice output, while the consecutive condition identifies the response at the neighboring input. The relabelling makes these two required binary outputs different, so Alice's raw outputs must alternate along the consecutive inputs.

Because n is odd, the last input has the same raw Alice output as the first, and both endpoint relabellings are the identity. The last diagonal condition therefore forces Bob's closing response to equal that output, whereas the closing equal-output term being zero forces it to differ. This contradiction proves the lower bound for every deterministic table.

Every stochastic COD model is a convex mixture of those deterministic response tables. The mixture weights are nonnegative, sum to one, and reproduce the original factorized behaviour by finite response marginalization. The chained expression is linear in the behaviour, so it is the weighted sum of the deterministic expressions. Applying the deterministic lower bound to each table and summing the weighted inequalities gives the claimed bound.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.IsCODModel`
- Truth anchor: `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.chainedValue`
- Truth anchor: `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.codBehaviour`
- Truth anchor: `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.relabel`
- Truth anchor: `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.result`
- Dependency: [D5/S3/Entropy/NamingWindow/SumProductUpdate](../../Entropy/NamingWindow/SumProductUpdate.md)
- Dependency: [D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift](../../TotalVariation/Equality/FiberwiseEqualDistanceLift.md)
