# Bernards--Gühne hybrid classical bound

## Abstract

The sharp Bernards--Gühne classical bound holds for two cells of arbitrary sizes k,m >= 2, including the conjectured range m > 2.

**Definition 1.1 (The sign in the Bell functional).**

$$\forall h \in \mathbb{N},\; phase\left(h\right) = (-1)^{1 + NatDiv\left(h + 1, 2\right)}$$

*Formalization.* `D5/S3/QuantumBounds/HybridMerminDepthBound.phase` (`✓ std3`).

*Citation.* F. Bernards; O. Gühne (2023). *Bell inequalities for nonlocality depth*. DOI: [10.1103/PhysRevA.107.022412](https://doi.org/10.1103/PhysRevA.107.022412). URL: <https://arxiv.org/abs/2205.04250v2>.

*Commentary.*

The sign is (-1)^(1+ceil(h/2)), as in Eq. (28), PDF p. 5. NatDiv(a,b) denotes natural-number division, rounded down; hence NatDiv(h+1,2) is ceil(h/2). The values at residues 0,1,2,3 modulo 4 are respectively -1,1,1,-1.

**Definition 1.2 (Two arbitrary deterministic cell responses).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in ((Fin\left(k\right) \to Bool) \to Units\left(\mathbb{Z}\right)),\; \forall B \in ((Fin\left(m\right) \to Bool) \to Units\left(\mathbb{Z}\right)),\; hybridValue\left(k, m, A, B\right) = \sum_{x:(Fin\left(k\right) \to Bool)} (\sum_{y:(Fin\left(m\right) \to Bool)} (IntCast\left(hammingDist\left(x, const\left(Fin\left(k\right), false\right)\right) + hammingDist\left(y, const\left(Fin\left(m\right), false\right)\right)\right) \cdot phase\left(hammingDist\left(x, const\left(Fin\left(k\right), false\right)\right) + hammingDist\left(y, const\left(Fin\left(m\right), false\right)\right)\right) \cdot val\left(A\left(x\right)\right) \cdot val\left(B\left(y\right)\right)))$$

*Formalization.* `D5/S3/QuantumBounds/HybridMerminDepthBound.hybridValue` (`✓ std3`).

*Citation.* F. Bernards; O. Gühne (2023). *Bell inequalities for nonlocality depth*. DOI: [10.1103/PhysRevA.107.022412](https://doi.org/10.1103/PhysRevA.107.022412). URL: <https://arxiv.org/abs/2205.04250v2>.

*Commentary.*

Section II, PDF p. 2, states: “Every cell c_i of the partition is considered as one system. The measurement settings are all combinations of measurement settings that apply to each subsystem within a cell. However, no restrictions apply to the correlations between subsystems within a cell, since the cell is regarded as one system. In particular, this allows for signaling to take place between the parties within one cell.” A Boolean setting string uses false for setting 1 and true for setting 2. hammingDist(x,const(Fin k,false)) counts its true coordinates. const(T,b) is the standard Function.const T b, the constant-b function on T. Fin k labels the k parties by 0,...,k-1. Thus the product of the outcomes of a cell may be any function of that cell's entire setting string. Integer units encode exactly the outcomes +1 and -1; val takes their integer value and IntCast embeds a natural number in the integers. Section II, PDF p. 3, defines M_h by Eq. (11) as the convex hull of the local models of the partitions with cardinality tuple h. A linear functional has the same maximum over this convex hull as over its deterministic points. The same page states: “where ’party permutations’ only includes permutations that yield different terms.” In particular (1122) consists of six terms. Accordingly each Boolean string occurs once in the displayed double sum; the string of weight zero contributes zero. The paper considers inequalities symmetric under permutation of the parties, so changing the assignment of parties to the two cells leaves F_n unchanged.

**Definition 1.3 (The conjectured sharp classical bound).**

$$(claim) \Leftrightarrow (\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; (2 \le k) \Rightarrow ((2 \le m) \Rightarrow (IsGreatest\left(\{v:\mathbb{Z} \mid \exists A \in ((Fin\left(k\right) \to Bool) \to Units\left(\mathbb{Z}\right)),\; \exists B \in ((Fin\left(m\right) \to Bool) \to Units\left(\mathbb{Z}\right)),\; v = hybridValue\left(k, m, A, B\right)\}, IntCast\left((k + m) \cdot 2^{NatSub\left(k + m, 2\right)}\right)\right))))$$

*Formalization.* `D5/S3/QuantumBounds/HybridMerminDepthBound.claim` (`✓ std3`).

*Citation.* F. Bernards; O. Gühne (2023). *Bell inequalities for nonlocality depth*. DOI: [10.1103/PhysRevA.107.022412](https://doi.org/10.1103/PhysRevA.107.022412). URL: <https://arxiv.org/abs/2205.04250v2>.

*Commentary.*

Section III.F, Eq. (28), PDF p. 5, displays: “F_n = ∑_{ℓ=1}^n (−1)^{1+⌈ℓ/2⌉} ℓ (1…1 2…2) ≤ n 2^{n−2}.” The bracket has n−ℓ settings labelled 1 and ℓ settings labelled 2 and sums over distinct permutations. Section V, PDF p. 8, states verbatim: “For (k, m) models with m > 2, we have a conjecture for the classical bound. Proving this bound or finding a counterexample remains an open problem.” The encoded sizes satisfy n=k+m and k,m >= 2; IsGreatest states both universal boundedness and attainment. NatSub is truncated natural-number subtraction, and all sums are finite sums over the indicated finite types.

**Theorem 1.4 (The maximum is attained and equals the bound).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/HybridMerminDepthBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. Bernards; O. Gühne (2023). *Bell inequalities for nonlocality depth*. DOI: [10.1103/PhysRevA.107.022412](https://doi.org/10.1103/PhysRevA.107.022412). URL: <https://arxiv.org/abs/2205.04250v2>.

*Commentary.*

Distribute the weight over the k+m marked coordinates. Fixing a marked coordinate to true removes it and replaces the sign s(h+1) by t(h)=(-1)^NatDiv(h,2). Both remaining cells are nonempty because k,m >= 2. Fix all but one setting in each of these cells. Each resulting four-term block is a CHSH expression up to local sign changes, so its absolute value is at most 2. There are 2^(r+s-2) such blocks for remaining cell sizes r,s; their sum is at most 2^(r+s-1). Each marked-coordinate contribution is therefore at most 2^(k+m-2). The responses A(x)=t(hammingDist(x,const(Fin k,false))) and B(y)=t(hammingDist(y,const(Fin m,false))) make every four-term block equal to 2, attaining all marked-coordinate bounds simultaneously. The exact sharp value follows. The formal assertion concerns the deterministic correlator functional; the passage to the convex hybrid model uses the linearity and symmetry described above. Models with a singleton cell and sharp bounds for more cells are outside this assertion.

## References

- Truth anchor: `D5/S3/QuantumBounds/HybridMerminDepthBound.claim`
- Truth anchor: `D5/S3/QuantumBounds/HybridMerminDepthBound.hybridValue`
- Truth anchor: `D5/S3/QuantumBounds/HybridMerminDepthBound.phase`
- Truth anchor: `D5/S3/QuantumBounds/HybridMerminDepthBound.result`
