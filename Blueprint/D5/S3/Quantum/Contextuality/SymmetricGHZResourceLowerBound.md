# A lower bound for symmetric GHZ resources

## Abstract

For 2 ≤ k ≤ n, every symmetric integer lift of C^k_n requires a selected size j with k / 2 ≤ j and j ≤ n - k / 2.

The input type is Fin n → Bool. Natural numbers start at zero. Annotations with ℤ or ℝ denote the corresponding casts of natural or integer values. Nat.div is natural-number division and Int.emod is the nonnegative remainder. The exponent in claim is an integer, so for k=1 it is −1. All local names below belong to D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.

**Definition 1.1 (All parity bits of a fixed size).**

$$\forall (n: \mathbb{N}), (\forall (i: \mathbb{N}), (\forall (x: (\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (\operatorname{D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.layer}\left(n, i, x\right) = \sum_{(S: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \in \operatorname{Finset.filter}\left(\lambda (S: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{Finset.card}\left(S\right) = i), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right))\right)} (\operatorname{ite}\left(\operatorname{Odd}\left(\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (l: \operatorname{Fin}\left(n\right)) \mapsto (x\left(l\right) = \operatorname{true}), S\right)\right)\right), (1: \mathbb{Z}), (0: \mathbb{Z})\right)))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.layer` (`✓ std3`).

*Citation.* Michael de Oliveira, Luís Soares Barbosa, Ernesto F. Galvão (2024). *Quantum advantage in temporally flat measurement-based quantum computation*. DOI: [10.22331/q-2024-04-09-1312](https://doi.org/10.22331/q-2024-04-09-1312). URL: <https://arxiv.org/abs/2212.03668>.

*Commentary.*

Definition 16, pp. 26–27: “A symmetric measurement assignment for an NMQC⊕ computation is composed of a set of linear functions L, which is limited to having either all parity bases of a specific size or none,” followed by Equation (71). The layer is the sum over all subsets of the specified size, as in Equation (72).

**Definition 1.2 (The complete symmetric Boolean function).**

$$\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (x: (\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (\operatorname{D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.csf}\left(n, k, x\right) = \operatorname{Int.emod}\left((\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (S: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto ((\operatorname{Finset.card}\left(S\right) = k) \land (\forall (l: \operatorname{Fin}\left(n\right)), ((l \in S) \Rightarrow (x\left(l\right) = \operatorname{true})))), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right))\right)\right): \mathbb{Z}), 2\right))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.csf` (`✓ std3`).

*Citation.* Michael de Oliveira, Luís Soares Barbosa, Ernesto F. Galvão (2024). *Quantum advantage in temporally flat measurement-based quantum computation*. DOI: [10.22331/q-2024-04-09-1312](https://doi.org/10.22331/q-2024-04-09-1312). URL: <https://arxiv.org/abs/2212.03668>.

*Commentary.*

Definition 5, p. 13: “The complete symmetric function (CSF) of dimension k, Cᵏ(x) : {0, 1}ⁿ → {0, 1} is defined as the sum, modulo 2, of all terms with degree equal to k, i.e.” Equation (27) counts exactly the k-element subsets whose inputs are all true.

**Definition 1.3 (Integer lifts with one coefficient per size).**

$$\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (T: \operatorname{Finset}\left(\mathbb{N}\right)), (\forall (a: (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.ComputesSym}\left(n, k, T, a\right)) \Leftrightarrow ((\forall (i: \mathbb{N}), ((i \in T) \Rightarrow ((1 \le i) \land (i \le n)))) \land (\forall (x: (\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (\exists (z: \mathbb{Z}), ((\sum_{(i: \mathbb{N}) \in T} (a\left(i\right) \cdot (\operatorname{D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.layer}\left(n, i, x\right): \mathbb{R})) = (z: \mathbb{R})) \land (\operatorname{Int.emod}\left(z, 2\right) = \operatorname{D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.csf}\left(n, k, x\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.ComputesSym` (`✓ std3`).

*Citation.* Michael de Oliveira, Luís Soares Barbosa, Ernesto F. Galvão (2024). *Quantum advantage in temporally flat measurement-based quantum computation*. DOI: [10.22331/q-2024-04-09-1312](https://doi.org/10.22331/q-2024-04-09-1312). URL: <https://arxiv.org/abs/2212.03668>.

*Commentary.*

Definition 15, p. 26: “The minimum number of qubits necessary for the deterministic evaluation of a Boolean function f : {0, 1}ⁿ → {0, 1} in the NMQC⊕ model can be defined as the sparsest multi-linear polynomial equivalent to the function, i.e.” Equation (70) requires an integer lift modulo two. Definition 16 continues on p. 27: “and the corresponding dichotomic measurement operators, which have to be equal for all parity bases of the same size, i.e.” Together with Equation (72), this gives a real coefficient a i for each size i∈T. Selected sizes lie between one and n. There is no constant term.

**Definition 1.4 (The number of selected parity measurements).**

$$\forall (n: \mathbb{N}), (\forall (T: \operatorname{Finset}\left(\mathbb{N}\right)), (\operatorname{D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.qubits}\left(n, T\right) = \sum_{(i: \mathbb{N}) \in T} (\operatorname{Nat.choose}\left(n, i\right))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.qubits` (`✓ std3`).

*Citation.* Michael de Oliveira, Luís Soares Barbosa, Ernesto F. Galvão (2024). *Quantum advantage in temporally flat measurement-based quantum computation*. DOI: [10.22331/q-2024-04-09-1312](https://doi.org/10.22331/q-2024-04-09-1312). URL: <https://arxiv.org/abs/2212.03668>.

*Commentary.*

Equations (71)–(72) select every parity basis of each size in T. There are Nat.choose n i subsets of size i, and one qubit for each basis. The sum counts every selected layer, including a layer whose coefficient is zero.

**Definition 1.5 (Conjecture 2 as a quantified asymptotic bound).**

$$(\operatorname{D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.claim}) \Leftrightarrow (\forall (k: \mathbb{N}), ((1 \le k) \Rightarrow (\exists (c: \mathbb{R}), ((0 < c) \land (\exists (N: \mathbb{N}), (\forall (n: \mathbb{N}), ((N \le n) \Rightarrow (\forall (T: \operatorname{Finset}\left(\mathbb{N}\right)), (\forall (a: (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.ComputesSym}\left(n, k, T, a\right)) \Rightarrow (c \cdot (n: \mathbb{R})^{(\operatorname{Nat.div}\left(k, 2\right): \mathbb{Z}) - 1} \le (\operatorname{D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.qubits}\left(n, T\right): \mathbb{R}))))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.claim` (`✓ std3`).

*Citation.* Michael de Oliveira, Luís Soares Barbosa, Ernesto F. Galvão (2024). *Quantum advantage in temporally flat measurement-based quantum computation*. DOI: [10.22331/q-2024-04-09-1312](https://doi.org/10.22331/q-2024-04-09-1312). URL: <https://arxiv.org/abs/2212.03668>.

*Commentary.*

Section 4.2, Conjecture 2, p. 27: “The number of qubits in a GHZ state necessary for the deterministic evaluation of a complete symmetric function Cᵏ, of constant degree k, with an n bit input string and a symmetric measurement assignment, scales as Ω(n^{⌊k/2⌋−1}).” For each k≥1, the positive constant c and threshold N may depend on k, and work uniformly for all larger input sizes, all selected size sets and all real coefficient functions that satisfy ComputesSym.

**Theorem 1.6 (The asymptotic lower bound).**

$$\operatorname{D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/de-oliveira-barbosa-galvao-2024-symmetric-ghz-resource` (proved) by `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"de-oliveira-barbosa-galvao-2024-symmetric-ghz-resource","declaration_gid":"D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michael de Oliveira, Luís Soares Barbosa, Ernesto F. Galvão (2024). *Quantum advantage in temporally flat measurement-based quantum computation*. DOI: [10.22331/q-2024-04-09-1312](https://doi.org/10.22331/q-2024-04-09-1312). URL: <https://arxiv.org/abs/2212.03668>.

*Commentary.*

For 2≤k≤n, put m=⌊k/2⌋ and r=k−2m. The signed layer polynomial at Hamming weight w is (1−X)^w(1+X)^(n−w). The coefficients d_u=(−1)^(m−u) Nat.choose m u, for 0≤u≤m, at weights 2u+r, have sum zero. Their weighted sum of these polynomials is (−4)^m X^m (1−X)^r (1+X)^(n−2m−r). Its coefficients vanish below m and above n−m, so the same weighted sum annihilates every parity layer outside that interval. An integer lift of csf is even at all the earlier weights and odd at weight k; its weighted sum is therefore odd. Consequently some selected layer lies between m and n−m, and its cost is at least Nat.choose n m. This proves the finite bound for 2≤k≤n. For n≥2k, the binomial lower estimate n^m/(2^m m!) gives the requested asymptotic bound with c=1/(2^m m!) and N=2k. For k=1 and n≥1, a computing assignment has a nonempty selected size set, so it gives at least one qubit, which bounds n^(−1) for n≥1.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.ComputesSym`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.csf`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.layer`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.qubits`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.result`
- Dependency: [D5/S1/Words/AssociatedMersenne/SingleRunDegrees](../../../S1/Words/AssociatedMersenne/SingleRunDegrees.md)
- Dependency: [D5/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder](../../Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound](../../Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.md)
