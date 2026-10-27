# A sequential advantage for classical permutation discrimination

## Abstract

Two adaptive queries distinguish four permutations with success one, while parallel success is at most three quarters.

**Definition 1.1 (Average success for two parallel queries).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (p: \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right)), (\forall (\pi: (\operatorname{Fin}\left(m\right)) \to (\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right))), (\forall (q: \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right))\right)), (\forall (\delta: ((\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right))) \to (((\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right))) \to (\operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right)))), ((\operatorname{D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage.parallelSuccess}\left(p, \pi, q, \delta\right): \mathbb{R}) = \sum_{i: \operatorname{Fin}\left(m\right)} (\operatorname{Finsupp.toFun}\left(\operatorname{Convexity.StdSimplex.weights}\left(p\right), i\right) \cdot \sum_{x: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right))} (\operatorname{Finsupp.toFun}\left(\operatorname{Convexity.StdSimplex.weights}\left(q\right), x\right) \cdot \operatorname{Finsupp.toFun}\left(\operatorname{Convexity.StdSimplex.weights}\left(\delta\left(x, (\operatorname{Equiv.toFun}\left(\pi\left(i\right), \operatorname{Prod.fst}\left(x\right)\right), \operatorname{Equiv.toFun}\left(\pi\left(i\right), \operatorname{Prod.snd}\left(x\right)\right))\right)\right), i\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.parallelSuccess` (`✓ std3`).

*Citation.* Jessica Bavaresco; Mio Murao; Marco Túlio Quintino (2022). *Unitary channel discrimination beyond group structures: Advantages of sequential and indefinite-causal-order strategies*. DOI: [10.1063/5.0075919](https://doi.org/10.1063/5.0075919). URL: <https://arxiv.org/abs/2105.13369v3>.

*Commentary.*

The prior p assigns probabilities to m permutations of Fin n. A probability vector q selects an ordered pair of inputs before either output is observed. For each input pair and output pair, the probability vector δ specifies the distribution of the guessed label. The average probability of a correct guess sums over the true label and the chosen input pair. This is the classical two-query form of the average-success objective and parallel strategy described in main.tex, lines 178–186 and 232, for the permutation setting of line 514. The simplex weights are evaluated through Finsupp.toFun, and each permutation through Equiv.toFun.

**Definition 1.2 (Average success for two sequential queries).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (p: \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right)), (\forall (\pi: (\operatorname{Fin}\left(m\right)) \to (\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right))), (\forall (q_{1}: \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)), (\forall (q_{2}: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)))), (\forall (\delta: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right)))))), ((\operatorname{D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage.sequentialSuccess}\left(p, \pi, q_{1}, q_{2}, \delta\right): \mathbb{R}) = \sum_{i: \operatorname{Fin}\left(m\right)} (\operatorname{Finsupp.toFun}\left(\operatorname{Convexity.StdSimplex.weights}\left(p\right), i\right) \cdot \sum_{x_{1}: \operatorname{Fin}\left(n\right)} (\operatorname{Finsupp.toFun}\left(\operatorname{Convexity.StdSimplex.weights}\left(q_{1}\right), x_{1}\right) \cdot \sum_{x_{2}: \operatorname{Fin}\left(n\right)} (\operatorname{Finsupp.toFun}\left(\operatorname{Convexity.StdSimplex.weights}\left(\left(q_{2}\right)\left(x_{1}, \operatorname{Equiv.toFun}\left(\pi\left(i\right), x_{1}\right)\right)\right), x_{2}\right) \cdot \operatorname{Finsupp.toFun}\left(\operatorname{Convexity.StdSimplex.weights}\left(\delta\left(x_{1}, \operatorname{Equiv.toFun}\left(\pi\left(i\right), x_{1}\right), x_{2}, \operatorname{Equiv.toFun}\left(\pi\left(i\right), x_{2}\right)\right)\right), i\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.sequentialSuccess` (`✓ std3`).

*Citation.* Jessica Bavaresco; Mio Murao; Marco Túlio Quintino (2022). *Unitary channel discrimination beyond group structures: Advantages of sequential and indefinite-causal-order strategies*. DOI: [10.1063/5.0075919](https://doi.org/10.1063/5.0075919). URL: <https://arxiv.org/abs/2105.13369v3>.

*Commentary.*

The first input has distribution q₁. After observing the first input x₁ and its output π i x₁, the second input has distribution q₂ x₁ (π i x₁). The decision distribution δ depends on both inputs and both outputs in transcript order. Multiplying these conditional probabilities and averaging over the prior gives the success probability. This specializes the discrimination objective of main.tex, lines 178–186, and the sequential strategy of line 243 to the classical permutation setting of line 514. All probability vectors and all such conditional probability vectors are allowed.

**Definition 1.3 (A strict advantage over every parallel strategy).**

$$(\operatorname{D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage.claim}: \operatorname{Prop}) = (\exists (n: \mathbb{N}), (\exists (m: \mathbb{N}), (\exists (p: \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right)), (\exists (\pi: (\operatorname{Fin}\left(m\right)) \to (\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right))), (\exists (q_{1}: \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)), (\exists (q_{2}: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)))), (\exists (\delta: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right)))))), (\exists (c: \mathbb{R}), ((\forall (q: \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right))\right)), (\forall (d: ((\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right))) \to (((\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right))) \to (\operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right)))), (\operatorname{D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage.parallelSuccess}\left(p, \pi, q, d\right) \le c))) \land (c < \operatorname{D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage.sequentialSuccess}\left(p, \pi, q_{1}, q_{2}, \delta\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jessica Bavaresco; Mio Murao; Marco Túlio Quintino (2022). *Unitary channel discrimination beyond group structures: Advantages of sequential and indefinite-causal-order strategies*. DOI: [10.1063/5.0075919](https://doi.org/10.1063/5.0075919). URL: <https://arxiv.org/abs/2105.13369v3>.

*Commentary.*

There are natural numbers n and m, a prior p on m permutations π of Fin n, a sequential strategy q₁, q₂, δ, and a real number c such that every parallel input distribution q and every parallel decision distribution d have success at most c, whereas the chosen sequential strategy has success strictly greater than c. The same unknown permutation is queried twice in both strategies. This is an existential two-query formulation of the classical permutation question in main.tex, line 514. A single ensemble with two uses suffices for this existence question.

**Theorem 1.4 (Perfect adaptive discrimination and a parallel upper bound).**

$$\operatorname{D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.result` (`✓ std3`). ∎

*Resolves.* `Problems/bavaresco-murao-quintino-2022-classical-permutation-sequential-advantage` (proved) by `D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bavaresco-murao-quintino-2022-classical-permutation-sequential-advantage","declaration_gid":"D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jessica Bavaresco; Mio Murao; Marco Túlio Quintino (2022). *Unitary channel discrimination beyond group structures: Advantages of sequential and indefinite-causal-order strategies*. DOI: [10.1063/5.0075919](https://doi.org/10.1063/5.0075919). URL: <https://arxiv.org/abs/2105.13369v3>.

*Commentary.*

Take n = 6 and m = 4 with the uniform prior. The four permutations, in label order, are the identity, the transposition (2 3), the transposition (0 1), and the product (0 1)(4 5). First query 0. When its output is 0, query 2; otherwise query 4. If the first output is 0, guess label 0 when the second output is 2 and label 1 otherwise. If the first output is not 0, guess label 2 when the second output is 4 and label 3 otherwise. The four possible output transcripts are (0,2), (0,3), (1,4), and (1,5), respectively. Thus the decision is correct for each label and the average sequential success is 1.

For every fixed input pair x, at least one of three equalities of output pairs holds: labels 0 and 1 give the same pair, labels 0 and 2 give the same pair, or labels 2 and 3 give the same pair. Indeed, two input symbols cannot meet all three disjoint blocks {0,1}, {2,3}, and {4,5}. Omitting {2,3} gives the first equality, omitting {0,1} gives the second, and omitting {4,5} gives the third.

For any probability vector, the weights of two distinct labels sum to at most 1, because all weights are nonnegative and their total is 1. Now fix x and an arbitrary parallel decision rule. Each of the four correct-label probabilities is at most 1. Choose one of the three equalities above. The two coinciding output pairs use the same decision distribution, so their correct-label probabilities sum to at most 1; the other two probabilities contribute at most 1 each. The sum of the four correct-label probabilities is therefore at most 3.

Under the uniform prior each label has weight 1/4. Interchanging the finite sums expresses parallel success as the q-weighted average, over input pairs x, of one quarter of the sum just bounded. Nonnegativity of each q weight preserves the bound 3/4, and the weights of q sum to 1. Hence every randomized parallel strategy has success at most 3/4. Choose c = 3/4. The sequential success is 1 and 3/4 < 1, giving the asserted strict advantage.

## References

- Truth anchor: `D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.claim`
- Truth anchor: `D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.parallelSuccess`
- Truth anchor: `D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.result`
- Truth anchor: `D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.sequentialSuccess`
