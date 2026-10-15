# A quantum behavior with rank of contextuality three

## Abstract

A quantum behavior has rank of contextuality three.

Fin n consists of the n labels starting at zero. A context C(x) is an ordered list of observable labels; its outcome is a function Fin (List.length (C(x))) → Bool. The bit true means eigenvalue −1. Behavior is the real table carrier; IsQuantum supplies the quantum probabilities. The real weights mu correspond to μ and the matrix rho to ρ. All matrix traces are complex traces; ofReal explicitly embeds each real probability into Complex. Finite sets count distinct behaviors, rather than labels of models that happen to agree.

**Definition 1.1 (Behavior tables).**

$$\forall (k: Nat), \forall (m: Nat), \forall (C: (Fin\left(k\right) \to List\left(Fin\left(m\right)\right))), Behavior\left(C\right) = (x: Fin\left(k\right)) \to ((Fin\left(\operatorname{List}.\operatorname{length}\left(C\left(x\right)\right)\right) \to Bool) \to Real)$$

*Formalization.* `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.Behavior` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Horodecki; J. Zhou; M. Stankiewicz; R. Salazar; P. Horodecki; R. Raussendorf; R. Horodecki; R. Ramanathan; E. Tyhurst (2022). *The rank of contextuality*. DOI: [10.1088/1367-2630/acdf78](https://doi.org/10.1088/1367-2630/acdf78). URL: <https://arxiv.org/abs/2205.10307>.

*Commentary.*

The carrier consists of real-valued tables indexed by contexts and outcomes, on which IsQuantum and NonContextual impose the source's probability conditions.

**Definition 1.2 (Restriction of a global assignment).**

$$\forall (k: Nat), \forall (m: Nat), \forall (C: (Fin\left(k\right) \to List\left(Fin\left(m\right)\right))), \forall (x: Fin\left(k\right)), \forall (g: (Fin\left(m\right) \to Bool)), restrict\left(C, x, g\right) = fun (i: Fin\left(\operatorname{List}.\operatorname{length}\left(C\left(x\right)\right)\right)) \mapsto g\left(\operatorname{List}.\operatorname{get}\left(C\left(x\right), i\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.restrict` (`✓ std3`).

*Citation.* K. Horodecki; J. Zhou; M. Stankiewicz; R. Salazar; P. Horodecki; R. Raussendorf; R. Horodecki; R. Ramanathan; E. Tyhurst (2022). *The rank of contextuality*. DOI: [10.1088/1367-2630/acdf78](https://doi.org/10.1088/1367-2630/acdf78). URL: <https://arxiv.org/abs/2205.10307>.

*Commentary.*

Section 2, PDF page 4: “We refer to output A given input X as an ordered list of outcomes (a₁, a₂, . . . , a|X|)), that is, it assigns a value to every observable in the context corresponding to X.” The i-th output is the predetermined value of the observable at position i in C(x).

**Definition 1.3 (Noncontextual distributions).**

$$\forall (k: Nat), \forall (m: Nat), \forall (C: (Fin\left(k\right) \to List\left(Fin\left(m\right)\right))), \forall (N: Behavior\left(C\right)), NonContextual\left(C, N\right) \iff \exists (mu: ((Fin\left(m\right) \to Bool) \to Real)), (\forall (g: (Fin\left(m\right) \to Bool)), 0 \le mu\left(g\right)) \land ((\sum_{g: (Fin\left(m\right) \to Bool)} mu\left(g\right) = 1) \land (\forall (x: Fin\left(k\right)), \forall (a: (Fin\left(\operatorname{List}.\operatorname{length}\left(C\left(x\right)\right)\right) \to Bool)), N\left(x, a\right) = \sum_{g: (Fin\left(m\right) \to Bool) with restrict\left(C, x, g\right) = a} mu\left(g\right)))$$

*Formalization.* `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.NonContextual` (`✓ std3`).

*Citation.* K. Horodecki; J. Zhou; M. Stankiewicz; R. Salazar; P. Horodecki; R. Raussendorf; R. Horodecki; R. Ramanathan; E. Tyhurst (2022). *The rank of contextuality*. DOI: [10.1088/1367-2630/acdf78](https://doi.org/10.1088/1367-2630/acdf78). URL: <https://arxiv.org/abs/2205.10307>.

*Commentary.*

Section 2, PDF page 4, equation (2): “In other words: a non-contextual behavior PNC is a probabilistic mixture of deterministic behaviors that have fixed values of outcomes to any observable beforehand.” The weight mu is nonnegative and has total mass one. The fiber sum is over all assignments g whose restriction equals a.

**Definition 1.4 (Cardinalities of noncontextual covers).**

$$\forall (k: Nat), \forall (m: Nat), \forall (C: (Fin\left(k\right) \to List\left(Fin\left(m\right)\right))), \forall (P: Behavior\left(C\right)), coverSizes\left(C, P\right) = \{n: Nat \mid \exists (S: Finset\left(Behavior\left(C\right)\right)), (\operatorname{Finset}.\operatorname{card}\left(S\right) = n) \land ((\forall (N: Behavior\left(C\right)), N \in S \implies NonContextual\left(C, N\right)) \land (\forall (x: Fin\left(k\right)), \exists (N: Behavior\left(C\right)), (N \in S) \land (\forall (a: (Fin\left(\operatorname{List}.\operatorname{length}\left(C\left(x\right)\right)\right) \to Bool)), N\left(x, a\right) = P\left(x, a\right))))\}$$

*Formalization.* `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.coverSizes` (`✓ std3`).

*Citation.* K. Horodecki; J. Zhou; M. Stankiewicz; R. Salazar; P. Horodecki; R. Raussendorf; R. Horodecki; R. Ramanathan; E. Tyhurst (2022). *The rank of contextuality*. DOI: [10.1088/1367-2630/acdf78](https://doi.org/10.1088/1367-2630/acdf78). URL: <https://arxiv.org/abs/2205.10307>.

*Commentary.*

Definition 3.1, PDF page 5: “Let P be a behavior. Let N be the set of all non-contextual behaviors, each of the form Nᵢ(A | X). Then we define the rank of contextuality denoted as RC in the following way” “where |S| denotes the cardinality of the set S.” A single member must reproduce all outcomes at a given context; the member may depend on the context.

**Definition 1.5 (The least cover cardinality).**

$$\forall (k: Nat), \forall (m: Nat), \forall (C: (Fin\left(k\right) \to List\left(Fin\left(m\right)\right))), \forall (P: Behavior\left(C\right)), \forall (r: Nat), IsRankOfContextuality\left(C, P, r\right) \iff IsLeast\left(coverSizes\left(C, P\right), r\right)$$

*Formalization.* `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.IsRankOfContextuality` (`✓ std3`).

*Citation.* K. Horodecki; J. Zhou; M. Stankiewicz; R. Salazar; P. Horodecki; R. Raussendorf; R. Horodecki; R. Ramanathan; E. Tyhurst (2022). *The rank of contextuality*. DOI: [10.1088/1367-2630/acdf78](https://doi.org/10.1088/1367-2630/acdf78). URL: <https://arxiv.org/abs/2205.10307>.

*Commentary.*

Definition 3.1, PDF page 5, equation (3): “Let P be a behavior. Let N be the set of all non-contextual behaviors, each of the form Nᵢ(A | X). Then we define the rank of contextuality denoted as RC in the following way” “where |S| denotes the cardinality of the set S.” IsLeast expresses membership and the lower bound on every cover cardinality.

**Definition 1.6 (Quantum realization).**

$$\forall (k: Nat), \forall (m: Nat), \forall (C: (Fin\left(k\right) \to List\left(Fin\left(m\right)\right))), \forall (P: Behavior\left(C\right)), IsQuantum\left(C, P\right) \iff \exists (d: Nat), \exists (rho: Matrix\left(Fin\left(d\right), Fin\left(d\right), Complex\right)), \exists (O: (Fin\left(m\right) \to Matrix\left(Fin\left(d\right), Fin\left(d\right), Complex\right))), (\operatorname{Matrix}.\operatorname{PosSemidef}\left(rho\right)) \land ((\operatorname{Matrix}.\operatorname{trace}\left(rho\right) = 1) \land ((\forall (v: Fin\left(m\right)), (\operatorname{Matrix}.\operatorname{IsHermitian}\left(O\left(v\right)\right)) \land ((O\left(v\right)) \cdot (O\left(v\right)) = 1)) \land ((\forall (x: Fin\left(k\right)), \forall (i: Fin\left(\operatorname{List}.\operatorname{length}\left(C\left(x\right)\right)\right)), \forall (j: Fin\left(\operatorname{List}.\operatorname{length}\left(C\left(x\right)\right)\right)), Commute\left(O\left(\operatorname{List}.\operatorname{get}\left(C\left(x\right), i\right)\right), O\left(\operatorname{List}.\operatorname{get}\left(C\left(x\right), j\right)\right)\right)) \land (\forall (x: Fin\left(k\right)), \forall (a: (Fin\left(\operatorname{List}.\operatorname{length}\left(C\left(x\right)\right)\right) \to Bool)), \operatorname{Complex}.\operatorname{ofReal}\left(P\left(x, a\right)\right) = \operatorname{Matrix}.\operatorname{trace}\left((rho) \cdot (\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left(fun (i: Fin\left(\operatorname{List}.\operatorname{length}\left(C\left(x\right)\right)\right)) \mapsto \operatorname{HSMul}.\operatorname{hSMul}\left((\frac{1}{2}: Complex), 1 + \operatorname{HSMul}.\operatorname{hSMul}\left((if a\left(i\right) then -1 else 1: Complex), O\left(\operatorname{List}.\operatorname{get}\left(C\left(x\right), i\right)\right)\right)\right)\right)\right))\right)))))$$

*Formalization.* `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.IsQuantum` (`✓ std3`).

*Citation.* K. Horodecki; J. Zhou; M. Stankiewicz; R. Salazar; P. Horodecki; R. Raussendorf; R. Horodecki; R. Ramanathan; E. Tyhurst (2022). *The rank of contextuality*. DOI: [10.1088/1367-2630/acdf78](https://doi.org/10.1088/1367-2630/acdf78). URL: <https://arxiv.org/abs/2205.10307>.

*Commentary.*

Section 2, PDF page 4: “With any set of observables V = {Vᵢ}, we can identify their commutation relations and represent them by a hypergraph H on this set where hyperedges are subsets of the powerset of V that denote contexts, i.e. sets of mutually commuting observables.” Binary observables are Hermitian involutions. Their spectral projections are multiplied in the list order, and the Born probability is the trace against the density matrix.

**Definition 1.7 (The construction question).**

$$claim \iff \exists (m: Nat), \exists (k: Nat), \exists (C: (Fin\left(k\right) \to List\left(Fin\left(m\right)\right))), \exists (P: Behavior\left(C\right)), \exists (r: Nat), (IsQuantum\left(C, P\right)) \land ((IsRankOfContextuality\left(C, P, r\right)) \land (\forall (n: Nat), r \ne 2^{n}))$$

*Formalization.* `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.claim` (`✓ std3`).

*Citation.* K. Horodecki; J. Zhou; M. Stankiewicz; R. Salazar; P. Horodecki; R. Raussendorf; R. Horodecki; R. Ramanathan; E. Tyhurst (2022). *The rank of contextuality*. DOI: [10.1088/1367-2630/acdf78](https://doi.org/10.1088/1367-2630/acdf78). URL: <https://arxiv.org/abs/2205.10307>.

*Commentary.*

Section 9 (Section IX in the arXiv source), PDF page 19: “Finally, it would be interesting to construct a quantum behavior having the rank of contextuality different from the power of 2 (the power of 2 is achieved by a tensor product of the Peres-Mermin behaviors).” The observable and context counts m and k, their lists C, the behavior P and its integer rank r are all existential. The final universal quantifier excludes every power 2^n, including n = 0.

**Theorem 1.8 (A quantum rank that is not a power of two).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.result` (`✓ std3`). ∎

*Resolves.* `Problems/horodecki-2022-rank-of-contextuality-non-power-of-two` (proved) by `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"horodecki-2022-rank-of-contextuality-non-power-of-two","declaration_gid":"D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Horodecki; J. Zhou; M. Stankiewicz; R. Salazar; P. Horodecki; R. Raussendorf; R. Horodecki; R. Ramanathan; E. Tyhurst (2022). *The rank of contextuality*. DOI: [10.1088/1367-2630/acdf78](https://doi.org/10.1088/1367-2630/acdf78). URL: <https://arxiv.org/abs/2205.10307>.

*Commentary.*

The behavior is the product of two Peres–Mermin squares: 18 observable labels, 36 paired contexts, and the maximally mixed state on Fin 16. Each square has five positive parity contexts and one negative parity context. For every context c, the uniform weight on the 16 assignments with the sole parity defect at c agrees with the square away from c. The three products with matching row defects cover every paired context, since at most two of the three rows occur in that pair. For the lower bound, each noncontextual product-scenario model has noncontextual copy marginals. One bad first-copy context for one model and one bad second-copy context for another produce a paired context that neither model reproduces. Thus every cover has at least three distinct members, and the displayed three-member cover is optimal. The rank is 3, which is odd and greater than one, so it is not 2^n for any natural n.

## References

- Truth anchor: `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.Behavior`
- Truth anchor: `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.IsQuantum`
- Truth anchor: `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.IsRankOfContextuality`
- Truth anchor: `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.NonContextual`
- Truth anchor: `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.claim`
- Truth anchor: `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.coverSizes`
- Truth anchor: `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.restrict`
- Truth anchor: `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw](../Arith/FibonacciAtomic/NativeContinuation/JointLaw.md)
- Dependency: [D5/S3/Entropy/Forgetting/PushforwardComposition](../Entropy/Forgetting/PushforwardComposition.md)
- Dependency: [D5/S3/Entropy/Observation/MultiTargetInformationChain](../Entropy/Observation/MultiTargetInformationChain.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../Quantum/FiniteDimensional.md)
- Dependency: [D5/S3/QuantumBounds/StatisticalStrengthMagicSquare](../QuantumBounds/StatisticalStrengthMagicSquare.md)
