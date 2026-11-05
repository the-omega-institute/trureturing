# Fibonacci Multiplicity Dominance

## Abstract

Fibonacci multiplicity support has equal hike and prefix dominance.

**Definition 1.1 (Fibonacci words of fixed weight).**

$$\forall n \in Nat, w \in List\left(Nat\right),\; (YF\left(n, w\right)) \Leftrightarrow ((\forall a \in Nat,\; (a \in w) \Rightarrow ((a = 1) \lor (a = 2))) \land (\operatorname{List}.\operatorname{sum}\left(w\right) = n))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.YF` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

A Fibonacci word w=w₁…wℓ is any binary word with letters wⱼ∈{1,2}. The integer |w|≔w₁+…+wℓ=n is called the weight of the word w. (Section 2.1, p. 12.) Words are List Nat, and weight is List.sum.

**Definition 1.2 (Total hike).**

$$\forall w \in List\left(Nat\right),\; hike\left(w\right) = \operatorname{List}.\operatorname{count}\left(2, w\right)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.hike` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

The matrix 𝐍ₙ is upper triangular. Furthermore, if Nᵤ,ᵥ is nonzero then u ⪰ v and ℎ(u)=ℎ(v), where ℎ(w) denotes the total hike, i.e., the number of 2’s appearing in a Fibonacci word w. (Conjecture 8.22, p. 47.) List.count 2 counts the letters equal to two.

**Definition 1.3 (From ribbon rows to words).**

$$\forall c \in List\left(Nat\right),\; Fib\left(c\right) = (if (\operatorname{List}.\operatorname{length}\left(c\right) \le 1) then \operatorname{List}.\operatorname{replicate}\left(\operatorname{List}.\operatorname{headD}\left(c, 0\right), 1\right) else \operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{replicate}\left(\operatorname{List}.\operatorname{headD}\left(c, 0\right) - 1, 1\right), \operatorname{List}.\operatorname{flatMap}\left((fun (j : Nat) \mapsto \operatorname{List}.\operatorname{append}\left([2], \operatorname{List}.\operatorname{replicate}\left(c[j + 1]! - (if (j + 2 = \operatorname{List}.\operatorname{length}\left(c\right)) then 1 else 2), 1\right)\right)), \operatorname{List}.\operatorname{range}\left(\operatorname{List}.\operatorname{length}\left(c\right) - 1\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.Fib` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

The Fibonacci word in 𝕐𝔽ₙ corresponding to a Fibonacci composition ς = (ς₁, …, ςₚ) of n is denoted Fib(ς). (Definition 8.10, pp. 42–43.) A single row gives only ones. Otherwise the initial and final runs have row size minus one, and interior runs have row size minus two. List indices start at zero; getElem! and headD zero also specify the values outside this domain.

**Definition 1.4 (The first split composition).**

$$\forall k \in List\left(Nat\right),\; splitA\left(k\right) = (let m := \operatorname{List}.\operatorname{length}\left(k\right); (let p := \operatorname{Nat}.\operatorname{div}\left(m, 2\right); (if (m \le 2) then k else (if (m = 3) then [k[0]!, k[1]! + k[2]!] else \operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left([k[0]!], \operatorname{List}.\operatorname{map}\left((fun (j : Nat) \mapsto k[2 \cdot j + 1]! + k[2 \cdot j + 2]!), \operatorname{List}.\operatorname{range}\left(p - 1\right)\right)\right), [(if (\operatorname{Nat}.\operatorname{mod}\left(m, 2\right) = 0) then k[2 \cdot p - 1]! else k[2 \cdot p - 1]! + k[2 \cdot p]!)]\right)))))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.splitA` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

Let κ = (κ₁, …, κₘ) be a composition of an integer n ≥ 1. We associate with κ two auxiliary Fibonacci compositions of n, denoted A(κ) = (α₁, …, αₚ₊₁) and B(κ) = (β₁, …, βₚ₊₁), where p = ⌊m/2⌋, defined as follows: (Definition 8.12, p. 43.) The cases m ≤ 2 and m = 3 are separate. The coordinates use zero-based list indices. Nat.div is integer division and Nat.mod is remainder.

**Definition 1.5 (The second split composition).**

$$\forall k \in List\left(Nat\right),\; splitB\left(k\right) = (let m := \operatorname{List}.\operatorname{length}\left(k\right); (let p := \operatorname{Nat}.\operatorname{div}\left(m, 2\right); (if (m \le 2) then k else (if (m = 3) then [k[0]! + k[2]!, k[1]!] else \operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left([1 + \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((fun (j : Nat) \mapsto k[2 \cdot j]!), \operatorname{List}.\operatorname{range}\left(p\right)\right)\right) - p], \operatorname{List}.\operatorname{map}\left((fun (j : Nat) \mapsto 1 + k[2 \cdot j + 1]!), \operatorname{List}.\operatorname{range}\left(p - 1\right)\right)\right), [k[2 \cdot p - 1]!]\right)))))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.splitB` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

Let κ = (κ₁, …, κₘ) be a composition of an integer n ≥ 1. We associate with κ two auxiliary Fibonacci compositions of n, denoted A(κ) = (α₁, …, αₚ₊₁) and B(κ) = (β₁, …, βₚ₊₁), where p = ⌊m/2⌋, defined as follows: (Definition 8.12, p. 43.) The first coordinate sums exactly p odd-indexed source parts. On positive compositions, (1 + sum) - p represents the integer expression 1 - p + sum. For odd m ≥ 5 the printed formula need not preserve weight; the matrix below keeps only pairs of weight n. Nat.div is integer division.

**Definition 1.6 (Consecutive elements in a partition block).**

$$\forall n \in Nat, pi \in Finpartition\left((\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right), a \in Fin\left(n\right), b \in Fin\left(n\right),\; (Arc\left(pi, a, b\right)) \Leftrightarrow ((a < b) \land (\exists block \in Finset\left(Fin\left(n\right)\right),\; (block \in \operatorname{Finpartition}.\operatorname{parts}\left(pi\right)) \land ((a \in block) \land ((b \in block) \land (\forall c \in Fin\left(n\right),\; (c \in block) \Rightarrow (\neg ((a < c) \land (c < b))))))))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.Arc` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

An arc is drawn in the upper half-plane between i, j ∈ {1, …, n} whenever i precedes j. (Section 8.1, p. 38.) The condition says that no element of the same block lies strictly between a and b. Source labels are shifted down by one into Fin n; partitions are Finpartition of Finset.univ.

**Definition 1.7 (Noncrossing partitions).**

$$\forall n \in Nat, pi \in Finpartition\left((\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right),\; (IsNoncrossing\left(pi\right)) \Leftrightarrow (\forall a \in Fin\left(n\right), b \in Fin\left(n\right), c \in Fin\left(n\right), d \in Fin\left(n\right),\; (Arc\left(pi, a, b\right)) \Rightarrow ((Arc\left(pi, c, d\right)) \Rightarrow (\neg ((a < c) \land ((c < b) \land (b < d))))))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.IsNoncrossing` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

A set partition π ∈ Π(n) is said to be non-crossing if its arcs are pairwise non-crossing; the set of non-crossing set partitions of n is denoted NC(n). (Section 8.1, p. 38.) The forbidden strict order is a < c < b < d for two arcs.

**Definition 1.8 (Active left endpoints).**

$$\forall n \in Nat, pi \in Finpartition\left((\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right), i \in Fin\left(n\right),\; Gamma\left(pi, i\right) = \operatorname{Finset}.\operatorname{filter}\left((fun (a : Fin\left(n\right)) \mapsto \exists b \in Fin\left(n\right),\; (Arc\left(pi, a, b\right)) \land ((a < i) \land (i \le b))), \operatorname{Finset}.\operatorname{univ}\right)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.Gamma` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

For i ∈ {1, …, n}, let Γᵢ(π) denote the set of openers or transients a < i such that i ≤ b, where b is the element succeeding a in the same block of π. (Section 8.1, p. 38.) The finite filter records the active arcs by their left endpoints.

**Definition 1.9 (Predecessor position).**

$$\forall n \in Nat, pi \in Finpartition\left((\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right), i \in Fin\left(n\right),\; gamma\left(pi, i\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun (a : Fin\left(n\right)) \mapsto \exists b \in Fin\left(n\right),\; (Arc\left(pi, b, i\right)) \land (a \le b)), Gamma\left(pi, i\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.gamma` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

For i ∈ C(π) ∪ T(π), let γᵢ(π) be the position of the opener or transient in Γᵢ(π) preceding i, where we list the elements Γᵢ(π) = {a₁ < … < aₖ} in increasing order. (Section 8.1, p. 38.) The rank starts at one and is zero if no predecessor exists.

**Definition 1.10 (Visits to each level).**

$$\forall n \in Nat, pi \in Finpartition\left((\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right), k \in Nat,\; ell\left(pi, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun (i : Fin\left(n\right)) \mapsto \operatorname{Finset}.\operatorname{card}\left(Gamma\left(pi, i\right)\right) = k), \operatorname{Finset}.\operatorname{univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.ell` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

ℓₖ(π) ≔ #{1 ≤ i ≤ n : #Γᵢ(π)=k}, k ≥ 0. (Equation (8.1), p. 38.) The cardinality is taken over Fin n.

**Definition 1.11 (Predecessors at each rank).**

$$\forall n \in Nat, pi \in Finpartition\left((\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right), k \in Nat,\; g\left(pi, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun (i : Fin\left(n\right)) \mapsto (\exists a \in Fin\left(n\right),\; Arc\left(pi, a, i\right)) \land (gamma\left(pi, i\right) = k)), \operatorname{Finset}.\operatorname{univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.g` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

gₘ(π) ≔ #{i ∈ C(π) ∪ T(π) : γᵢ(π)=m}, m ≥ 1. (Equation (8.1), p. 38.) Having a predecessor is exactly being a closer or transient.

**Definition 1.12 (Maximum active level).**

$$\forall n \in Nat, pi \in Finpartition\left((\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right),\; peak\left(pi\right) = \operatorname{Finset}.\operatorname{sup}\left(\operatorname{Finset}.\operatorname{univ}, (fun (i : Fin\left(n\right)) \mapsto \operatorname{Finset}.\operatorname{card}\left(Gamma\left(pi, i\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.peak` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

p = max{k : ℓₖ(π) > 0}. (Definition 8.16, p. 44.) For n ≥ 1 this is the maximum cardinality of Gamma over Fin n. Finset.sup also specifies the empty case.

**Definition 1.13 (The alternating composition).**

$$\forall n \in Nat, pi \in Finpartition\left((\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right),\; z\left(pi\right) = (let p := peak\left(pi\right); (let zs := \operatorname{List}.\operatorname{cons}\left(ell\left(pi, 0\right), \operatorname{List}.\operatorname{flatMap}\left((fun (j : Nat) \mapsto [g\left(pi, j + 1\right), ell\left(pi, j + 1\right) - g\left(pi, j + 1\right)]), \operatorname{List}.\operatorname{range}\left(p\right)\right)\right); (if (ell\left(pi, p\right) = g\left(pi, p\right)) then \operatorname{List}.\operatorname{dropLast}\left(zs\right) else zs)))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.z` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

Let π ∈ NC(n) be a non-crossing set partition. Define z₁(π)=ℓ₀(π), z₂ₖ(π)=gₖ(π), z₂ₖ₊₁(π)=ℓₖ(π)−gₖ(π), where 1 ≤ k ≤ p and where p = max{k : ℓₖ(π) > 0}. (Definition 8.16, p. 44.) The final coordinate alone is deleted when ℓₚ(π)=gₚ(π).

**Definition 1.14 (The partition multiplicity).**

$$\forall n \in Nat, k \in List\left(Nat\right),\; multiplicity\left(n, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun (pi : Finpartition\left((\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right)) \mapsto (IsNoncrossing\left(pi\right)) \land (z\left(pi\right) = k)), \operatorname{Finset}.\operatorname{univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.multiplicity` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

N(κ) = #{π ∈ NC(n) : z(π) = κ}. (Corollary 8.20, p. 46.) The cardinality is a finite filter of all set partitions.

**Definition 1.15 (The multiplicity matrix).**

$$\forall n \in Nat, u \in List\left(Nat\right), v \in List\left(Nat\right),\; matrixEntry\left(n, u, v\right) = (if h : \exists k \in Composition\left(n\right),\; (u = Fib\left(splitA\left(\operatorname{Composition}.\operatorname{blocks}\left(k\right)\right)\right)) \land (v = Fib\left(splitB\left(\operatorname{Composition}.\operatorname{blocks}\left(k\right)\right)\right)) then multiplicity\left(n, \operatorname{Composition}.\operatorname{blocks}\left(\operatorname{Classical}.\operatorname{choose}\left(h\right)\right)\right) else 0)$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.matrixEntry` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

For a pair of Fibonacci words u, v ∈ 𝕐𝔽ₙ, set Nᵤ,ᵥ = N(κ) if u = u(κ) and v = v(κ) for some composition κ ∈ Comp(n). By Lemma 8.14, this composition is unique if it exists. Otherwise, set Nᵤ,ᵥ = 0. (Definition 8.21, p. 47.) Classical.choose selects a matching Composition n; its blocks are supplied to the partition count. Both matrix indices in the theorem have weight n.

**Definition 1.16 (Dominance by prefix sums).**

$$\forall u \in List\left(Nat\right), v \in List\left(Nat\right),\; (Dominates\left(u, v\right)) \Leftrightarrow (\forall k \in Nat,\; (1 \le k) \Rightarrow ((k \le min\left(\operatorname{List}.\operatorname{length}\left(u\right), \operatorname{List}.\operatorname{length}\left(v\right)\right)) \Rightarrow (\operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{take}\left(k, v\right)\right) \le \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{take}\left(k, u\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.Dominates` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

Recall from [Oka94] that u ⪰ v if u=u₁⋯uₚ and v=v₁⋯v_q in 𝕐𝔽ₙ, and u₁+⋯+uₖ ≥ v₁+⋯+vₖ for all 1 ≤ k ≤ min(p,q). (Section 8.5, p. 47.) List.take includes every common nonempty prefix.

**Definition 1.17 (Petrov–Scott Conjecture 8.22).**

$$(claim) \Leftrightarrow (\forall n \in Nat,\; (1 \le n) \Rightarrow (\forall u \in List\left(Nat\right), v \in List\left(Nat\right),\; (YF\left(n, u\right)) \Rightarrow ((YF\left(n, v\right)) \Rightarrow (((\operatorname{List}.\operatorname{Lex}\left((fun (a : Nat) \mapsto (fun (b : Nat) \mapsto b < a)), v, u\right)) \Rightarrow (matrixEntry\left(n, u, v\right) = 0)) \land ((matrixEntry\left(n, u, v\right) \ne 0) \Rightarrow ((Dominates\left(u, v\right)) \land (hike\left(u\right) = hike\left(v\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.claim` (`✓ std3`).

*Citation.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

The matrix 𝐍ₙ is upper triangular. Furthermore, if Nᵤ,ᵥ is nonzero then u ⪰ v and ℎ(u)=ℎ(v), where ℎ(w) denotes the total hike, i.e., the number of 2’s appearing in a Fibonacci word w. (Conjecture 8.22, p. 47.) The descending lexicographic order is the order 221, 212, 2111, 122, 1211, 1121, 1112, 11111 shown in Figure 8. The two sentences are encoded for every n ≥ 1 and every pair of words of weight n. The printed splitB expression is retained; the weight-preserving correction is a separate question.

**Theorem 1.18 (Upper triangularity and dominance at every weight).**

$$\forall n \in Nat,\; (1 \le n) \Rightarrow (\forall u \in List\left(Nat\right), v \in List\left(Nat\right),\; (YF\left(n, u\right)) \Rightarrow ((YF\left(n, v\right)) \Rightarrow (((\operatorname{List}.\operatorname{Lex}\left((fun (a : Nat) \mapsto (fun (b : Nat) \mapsto b < a)), v, u\right)) \Rightarrow (matrixEntry\left(n, u, v\right) = 0)) \land ((matrixEntry\left(n, u, v\right) \ne 0) \Rightarrow ((Dominates\left(u, v\right)) \land (hike\left(u\right) = hike\left(v\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.result` (`✓ std3`). ∎

*Resolves.* `Problems/multiplicity-dominance` (proved) by `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"multiplicity-dominance","declaration_gid":"D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Leonid Petrov and Jeanne Scott (2026). *Random Fibonacci words via clone Schur functions*. DOI: [10.1017/fms.2025.10165](https://doi.org/10.1017/fms.2025.10165). URL: <https://arxiv.org/abs/2412.21126v2>.

*Commentary.*

Equal numbers of split rows give equal hike. Enlarging the trailing runs reduces the number of twos in every reversed prefix, independently of the initial runs. Equal weight and hike give equal lengths and convert this to the required forward-prefix inequalities. At the first different letter, dominance excludes the opposite descending lexicographic direction.

## References

- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.Arc`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.Dominates`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.Fib`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.Gamma`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.IsNoncrossing`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.YF`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.claim`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.ell`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.g`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.gamma`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.hike`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.matrixEntry`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.multiplicity`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.peak`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.result`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.splitA`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.splitB`
- Truth anchor: `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.z`
- Dependency: [D5/S1/Words/UnaryGapWords](../../../S1/Words/UnaryGapWords.md)
