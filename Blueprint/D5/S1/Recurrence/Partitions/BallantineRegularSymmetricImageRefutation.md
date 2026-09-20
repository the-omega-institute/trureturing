# A Counterexample to the Regular Elementary Symmetric Image Table

## Abstract

Conjecture 16's d=5 column is false at n=4: the actual difference is 2, not 1.

A partition of n is represented by Nat.Partition n, whose positive parts sum to n. Multiset powersetCard selects positions, so equal parts retain the multiplicity of the corresponding square-free monomials. Finite-set image removes duplicate image partitions.

**Definition 1.1 (The elementary symmetric image of a partition).**

$$\forall k \in \mathrm{Nat}, n \in \mathrm{Nat}, l \in \operatorname{Partition}\left(n\right),\; \operatorname{pre}\left(k, l\right) = \operatorname{map}\left(prod, \operatorname{powersetCard}\left(\operatorname{parts}\left(l\right), k\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.pre` (`✓ std3`).

*Citation.* Cristina Ballantine, George Beck, Mircea Merca, Bruce E. Sagan (2024). *Elementary symmetric partitions*. DOI: [10.48550/arXiv.2409.11268](https://doi.org/10.48550/arXiv.2409.11268). URL: <https://arxiv.org/abs/2409.11268v3>.

*Commentary.*

For a partition lambda, pre(k,lambda) is the multiset obtained by taking every k-position submultiset of its parts and mapping it to its product.

**Definition 1.2 (The image family ImP).**

$$\forall k \in \mathrm{Nat}, n \in \mathrm{Nat},\; \operatorname{imP}\left(k, n\right) = \operatorname{image}\left(\operatorname{pre}\left(k\right), \operatorname{filter}\left((l: \operatorname{Partition}\left(n\right) \mapsto k \le \operatorname{card}\left(\operatorname{parts}\left(l\right)\right)), \operatorname{univ}\left(\operatorname{Partition}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.imP` (`✓ std3`).

*Citation.* Cristina Ballantine, George Beck, Mircea Merca, Bruce E. Sagan (2024). *Elementary symmetric partitions*. DOI: [10.48550/arXiv.2409.11268](https://doi.org/10.48550/arXiv.2409.11268). URL: <https://arxiv.org/abs/2409.11268v3>.

*Commentary.*

The filter retains exactly the partitions with at least k parts, and image applies pre(k) while counting equal images once.

**Definition 1.3 (Regularity of an image partition).**

$$\forall d \in \mathrm{Nat}, mu \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; (\operatorname{IsRegular}\left(d, mu\right)) \Leftrightarrow (\forall x \in \mathrm{Nat},\; (x \in mu) \Rightarrow (\neg d \mid x))$$

*Formalization.* `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.IsRegular` (`✓ std3`).

*Citation.* Cristina Ballantine, George Beck, Mircea Merca, Bruce E. Sagan (2024). *Elementary symmetric partitions*. DOI: [10.48550/arXiv.2409.11268](https://doi.org/10.48550/arXiv.2409.11268). URL: <https://arxiv.org/abs/2409.11268v3>.

*Commentary.*

IsRegular(d,mu) says that no part x of mu is divisible by d.

**Definition 1.4 (The regular image count).**

$$\forall d \in \mathrm{Nat}, k \in \mathrm{Nat}, n \in \mathrm{Nat},\; \operatorname{r}\left(d, k, n\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{IsRegular}\left(d\right), \operatorname{imP}\left(k, n\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.r` (`✓ std3`).

*Citation.* Cristina Ballantine, George Beck, Mircea Merca, Bruce E. Sagan (2024). *Elementary symmetric partitions*. DOI: [10.48550/arXiv.2409.11268](https://doi.org/10.48550/arXiv.2409.11268). URL: <https://arxiv.org/abs/2409.11268v3>.

*Commentary.*

The value r(d,k,n) is the cardinality of the d-regular members of imP(k,n).

**Definition 1.5 (The printed residue-class table).**

$$\forall d \in \mathrm{Nat}, n \in \mathrm{Nat},\; \begin{aligned}(((d = 2) \land (n \bmod 2 = 0)) \Rightarrow (\operatorname{table}\left(d, n\right) = (\operatorname{natDiv}\left(n + 2, 4\right) : \mathrm{Int})))\\(((d = 2) \land (n \bmod 2 = 1)) \Rightarrow (\operatorname{table}\left(d, n\right) = (0 : \mathrm{Int})))\\(((d = 3) \land (n \bmod 6 = 0)) \Rightarrow (\operatorname{table}\left(d, n\right) = (2 \cdot \operatorname{natDiv}\left(n, 6\right) : \mathrm{Int})))\\(((d = 3) \land (n \bmod 6 = 1)) \Rightarrow (\operatorname{table}\left(d, n\right) = (\operatorname{natDiv}\left(n, 6\right) : \mathrm{Int})))\\(((d = 3) \land (n \bmod 6 = 2)) \Rightarrow (\operatorname{table}\left(d, n\right) = (\operatorname{natDiv}\left(n, 6\right) + 1 : \mathrm{Int})))\\(((d = 3) \land (n \bmod 6 = 3)) \Rightarrow (\operatorname{table}\left(d, n\right) = (2 \cdot \operatorname{natDiv}\left(n, 6\right) + 1 : \mathrm{Int})))\\(((d = 3) \land (n \bmod 6 = 4)) \Rightarrow (\operatorname{table}\left(d, n\right) = (\operatorname{natDiv}\left(n, 6\right) + 1 : \mathrm{Int})))\\(((d = 3) \land (n \bmod 6 = 5)) \Rightarrow (\operatorname{table}\left(d, n\right) = (\operatorname{natDiv}\left(n, 6\right) + 1 : \mathrm{Int})))\\(((d = 4) \land (n \bmod 4 = 0)) \Rightarrow (\operatorname{table}\left(d, n\right) = (\operatorname{natDiv}\left(n, 4\right) : \mathrm{Int})))\\(((d = 4) \land (n \bmod 4 = 1)) \Rightarrow (\operatorname{table}\left(d, n\right) = (\operatorname{natDiv}\left(n, 4\right) : \mathrm{Int})))\\(((d = 4) \land (n \bmod 4 = 2)) \Rightarrow (\operatorname{table}\left(d, n\right) = (\operatorname{natDiv}\left(n, 4\right) + 1 : \mathrm{Int})))\\(((d = 4) \land (n \bmod 4 = 3)) \Rightarrow (\operatorname{table}\left(d, n\right) = (\operatorname{natDiv}\left(n, 4\right) + 1 : \mathrm{Int})))\\(((d = 5) \land (n \bmod 10 = 0)) \Rightarrow (\operatorname{table}\left(d, n\right) = (3 \cdot \operatorname{natDiv}\left(n, 10\right) : \mathrm{Int})))\\(((d = 5) \land (n \bmod 10 = 1)) \Rightarrow (\operatorname{table}\left(d, n\right) = (4 \cdot \operatorname{natDiv}\left(n, 10\right) : \mathrm{Int})))\\(((d = 5) \land (n \bmod 10 = 2)) \Rightarrow (\operatorname{table}\left(d, n\right) = (3 \cdot \operatorname{natDiv}\left(n, 10\right) : \mathrm{Int})))\\(((d = 5) \land (n \bmod 10 = 3)) \Rightarrow (\operatorname{table}\left(d, n\right) = (3 \cdot \operatorname{natDiv}\left(n, 10\right) + 1 : \mathrm{Int})))\\(((d = 5) \land (n \bmod 10 = 4)) \Rightarrow (\operatorname{table}\left(d, n\right) = (3 \cdot \operatorname{natDiv}\left(n, 10\right) + 1 : \mathrm{Int})))\\(((d = 5) \land (n \bmod 10 = 5)) \Rightarrow (\operatorname{table}\left(d, n\right) = (3 \cdot \operatorname{natDiv}\left(n, 10\right) + 2 : \mathrm{Int})))\\(((d = 5) \land (n \bmod 10 = 6)) \Rightarrow (\operatorname{table}\left(d, n\right) = (4 \cdot \operatorname{natDiv}\left(n, 10\right) + 2 : \mathrm{Int})))\\(((d = 5) \land (n \bmod 10 = 7)) \Rightarrow (\operatorname{table}\left(d, n\right) = (3 \cdot \operatorname{natDiv}\left(n, 10\right) + 2 : \mathrm{Int})))\\(((d = 5) \land (n \bmod 10 = 8)) \Rightarrow (\operatorname{table}\left(d, n\right) = (3 \cdot \operatorname{natDiv}\left(n, 10\right) + 2 : \mathrm{Int})))\\(((d = 5) \land (n \bmod 10 = 9)) \Rightarrow (\operatorname{table}\left(d, n\right) = (3 \cdot \operatorname{natDiv}\left(n, 10\right) + 3 : \mathrm{Int})))\\((\neg d \in \left\{2, 3, 4, 5\right\}) \Rightarrow (\operatorname{table}\left(d, n\right) = (0 : \mathrm{Int})))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.table` (`✓ std3`).

*Citation.* Cristina Ballantine, George Beck, Mircea Merca, Bruce E. Sagan (2024). *Elementary symmetric partitions*. DOI: [10.48550/arXiv.2409.11268](https://doi.org/10.48550/arXiv.2409.11268). URL: <https://arxiv.org/abs/2409.11268v3>.

*Commentary.*

Each displayed natDiv is natural-number division, hence the floor of the corresponding nonnegative rational quotient. Every branch is then cast to an integer. The rows are displayed column by column for d equal to 2, 3, 4 and 5.

**Definition 1.6 (Conjecture 16).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat}, d \in \mathrm{Nat},\; (d \in \left\{2, 3, 4, 5\right\}) \Rightarrow ((\operatorname{r}\left(d, 2, n\right) : \mathrm{Int}) - (\operatorname{r}\left(d, 3, n\right) : \mathrm{Int}) = \operatorname{table}\left(d, n\right)))$$

*Formalization.* `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.claim` (`✓ std3`).

*Citation.* Cristina Ballantine, George Beck, Mircea Merca, Bruce E. Sagan (2024). *Elementary symmetric partitions*. DOI: [10.48550/arXiv.2409.11268](https://doi.org/10.48550/arXiv.2409.11268). URL: <https://arxiv.org/abs/2409.11268v3>.

*Commentary.*

The source definitions say: "Given a partition λ = (λ₁, λ₂, …, λ_ℓ) with ℓ ≥ k, we define pre_k(λ) to be the partition whose parts are the summands in the evaluation e_k(λ₁, λ₂, …, λ_ℓ)." "ImP_k(n) = pre_k(P_k(n))" "By contrast, a partition is d-regular if it contains no part which is a multiple of d." "Let r_{d,k}(n) = |{λ | λ ∈ ImP_k(n) is d-regular}|." Conjecture 16 states: "The value of r_{d,2}(n) − r_{d,3}(n) for d = 2, 3, 4, and 5 are shown in the columns of the following table. These values depend on the congruence class of n modulo 2, 6, 4, and 10, respectively. The first column of the table gives the congruence class for n."

**Theorem 1.7 (The printed table fails at d=5 and n=4).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n=4, the degree-two image set is {(3), (4), (2,2,1), (1,1,1,1,1,1)} and the degree-three image set is {(2), (1,1,1,1)}. All six listed images are 5-regular, so the two cardinalities are 4 and 2. Their integer difference is 2, whereas the residue-four entry in the d=5 column is 3 natDiv(4,10) + 1 = 1.

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.IsRegular`
- Truth anchor: `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.claim`
- Truth anchor: `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.imP`
- Truth anchor: `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.pre`
- Truth anchor: `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.r`
- Truth anchor: `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.result`
- Truth anchor: `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.table`
