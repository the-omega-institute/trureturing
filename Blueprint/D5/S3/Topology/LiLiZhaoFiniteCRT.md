# Prime-tail topology bridge

## Abstract

Finite prime-residue cylinders supply the compatibility bridge for the Li--Li--Zhao prime-tail topology construction.

The underlying space is the set N of natural numbers including zero. The function primeSeq(i), abbreviated p(i), is the increasing enumeration Nat.nth Nat.Prime i, starting with p(0)=2. For natural i and a, residue(i,a) is the set of x with x congruent to a modulo p(i). For a finite set s of natural indices and an arbitrary assignment a:N to N, finiteCylinder(s,a) is the intersection of residue(i,a(i)) over i in s; the empty intersection is the whole space. No bound on the residues is needed for CRT. Nonempty(S) means that some natural number belongs to S; inter denotes set intersection and mod denotes the natural remainder. TOneSpace and TTwoSpace mean T1 and Hausdorff, with the displayed topology.

**Theorem 1.1 (Finite Chinese-remainder compatibility).**

$$(\forall s:\operatorname{Finset}(\mathbb{N}), (\forall a:\mathbb{N}\to \mathbb{N}, (\exists x:\mathbb{N}, (\forall i:\mathbb{N}, ((i\in s)\implies (\operatorname{mod}(x,\operatorname{primeSeq}(i))= \operatorname{mod}(\operatorname{a}(i),\operatorname{primeSeq}(i))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LiLiZhaoFiniteCRT.finite_crt` (`✓ std3`). ∎

*Citation.* Xiangrui Li, Qingguo Li, Dongsheng Zhao (2025). *Sober topologies on a set*. URL: <https://arxiv.org/abs/2508.05419v1>.

*Commentary.*

Every finite assignment of residue classes at distinct prime indices has a natural-number solution. The proof uses Mathlib's finite Chinese-remainder construction and pairwise coprimality of distinct entries of primeSeq.

**Theorem 1.2 (Every finite cylinder is nonempty).**

$$(\forall s:\operatorname{Finset}(\mathbb{N}), (\forall a:\mathbb{N}\to \mathbb{N}, \operatorname{Nonempty}(\operatorname{finiteCylinder}(s,a))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LiLiZhaoFiniteCRT.finiteCylinder_nonempty` (`✓ std3`). ∎

*Citation.* Xiangrui Li, Qingguo Li, Dongsheng Zhao (2025). *Sober topologies on a set*. URL: <https://arxiv.org/abs/2508.05419v1>.

*Commentary.*

The finite CRT solution lies in the intersection of all selected prime residue classes.

**Theorem 1.3 (Disjoint supports still have a common point).**

$$(\forall s:\operatorname{Finset}(\mathbb{N}), (\forall t:\operatorname{Finset}(\mathbb{N}), (\operatorname{Disjoint}(s,t)\implies (\forall a:\mathbb{N}\to \mathbb{N}, (\forall b:\mathbb{N}\to \mathbb{N}, \operatorname{Nonempty}(\operatorname{inter}(\operatorname{finiteCylinder}(s,a),\operatorname{finiteCylinder}(t,b))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LiLiZhaoFiniteCRT.disjoint_cylinders_nonempty` (`✓ std3`). ∎

*Citation.* Xiangrui Li, Qingguo Li, Dongsheng Zhao (2025). *Sober topologies on a set*. URL: <https://arxiv.org/abs/2508.05419v1>.

*Commentary.*

Given disjoint finite supports and arbitrary assignments a and b, merge the assignments on their union and take a point of the resulting nonempty cylinder. Its restrictions give a common point of the two original cylinders.

**Definition 1.4 (Prime-tail subbases).**

$$(\forall n:\mathbb{N}, (\forall U:\operatorname{Set}(\mathbb{N}), ((U\in \operatorname{tailSubbasis}(n))\iff (\exists i:\mathbb{N}, ((n\le i)\land (\exists a:\mathbb{N}, ((a< \operatorname{primeSeq}(i))\land (U= \operatorname{residue}(i,a)))))))))$$

*Formalization.* `D5/S3/Topology/LiLiZhaoFiniteCRT.tailSubbasis` (`✓ std3`).

*Citation.* Xiangrui Li, Qingguo Li, Dongsheng Zhao (2025). *Sober topologies on a set*. URL: <https://arxiv.org/abs/2508.05419v1>.

*Commentary.*

At level n the subbasis contains every residue class modulo p(i) with i at least n and representative a less than p(i). The definition tailTopology(n) is TopologicalSpace.generateFrom(tailSubbasis(n)). Increasing n removes subbasic opens, so the open-set collections decrease. In Mathlib's reverse order on topologies, n at most m gives tailTopology(n) at most tailTopology(m).

**Theorem 1.5 (Every prime-tail topology is Hausdorff).**

$$(\forall n:\mathbb{N}, \operatorname{TTwoSpace}(\mathbb{N},\operatorname{tailTopology}(n)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LiLiZhaoFiniteCRT.tailTopology_t2` (`✓ std3`). ∎

*Citation.* Xiangrui Li, Qingguo Li, Dongsheng Zhao (2025). *Sober topologies on a set*. URL: <https://arxiv.org/abs/2508.05419v1>.

*Commentary.*

For distinct x and y, choose i=max(n,x+y+1). The bound i+2 at most p(i) makes x and y distinct representatives below p(i). Their singleton-support cylinders are disjoint neighborhoods, obtained from the finite-cylinder neighborhood lemma.

**Theorem 1.6 (Finite cylinders form local basic neighborhoods).**

$$(\forall n:\mathbb{N}, (\forall U:\operatorname{Set}(\mathbb{N}), (\operatorname{IsOpen}(\operatorname{tailTopology}(n),U)\implies (\forall x:\mathbb{N}, ((x\in U)\implies (\exists s:\operatorname{Finset}(\mathbb{N}), (\exists a:\mathbb{N}\to \mathbb{N}, ((\forall i:\mathbb{N}, ((i\in s)\implies (n\le i)))\land ((\forall i:\mathbb{N}, ((i\in s)\implies (\operatorname{a}(i)< \operatorname{primeSeq}(i))))\land ((x\in \operatorname{finiteCylinder}(s,a))\land (\operatorname{finiteCylinder}(s,a)\subseteq U)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LiLiZhaoFiniteCRT.finiteCylinder_basis_of_isOpen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every open U at level n and every x in U there is a finite cylinder through x, contained in U, with all support indices at least n and all representatives below their prime moduli. Induction on generated opens handles basic sets, the whole space, intersections, and arbitrary unions. In an intersection, the common point forces the two representatives to agree wherever the supports overlap. This explicit support-and-representative extraction is the local bridge used in the irreducibility proof.

The definition commonTopology is the Mathlib supremum iSup n (tailTopology n). Precisely, commonTopology_isOpen_iff says that a set is open in commonTopology if and only if it is open in every tailTopology(n). Mathlib orders topologies by reverse inclusion of their open sets. Thus this supremum is the intersection, or infimum in the paper's inclusion order, of the tail open-set collections. IsOpen(T,U) below uses the displayed topology T; TOneSpace, TTwoSpace and QuasiSober likewise carry the displayed topology explicitly.

**Theorem 1.7 (The common topology is T1).**

$$\operatorname{TOneSpace}(\mathbb{N},commonTopology)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LiLiZhaoFiniteCRT.commonTopology_t1` (`✓ std3`). ∎

*Citation.* Xiangrui Li, Qingguo Li, Dongsheng Zhao (2025). *Sober topologies on a set*. URL: <https://arxiv.org/abs/2508.05419v1>.

*Commentary.*

Every singleton is closed in each Hausdorff tail topology. Closed singletons persist in the intersection of the tail open-set collections, which is Mathlib's supremum.

**Theorem 1.8 (The whole space is irreducible in the common topology).**

$$\operatorname{IsIrreducible}(commonTopology,\operatorname{univ}(\mathbb{N}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LiLiZhaoFiniteCRT.commonTopology_univ_irreducible` (`✓ std3`). ∎

*Citation.* Xiangrui Li, Qingguo Li, Dongsheng Zhao (2025). *Sober topologies on a set*. URL: <https://arxiv.org/abs/2508.05419v1>.

*Commentary.*

Given two nonempty common opens U and V, take a finite cylinder contained in U at level zero, with support s. The cutoff m=sum(s)+1 is greater than every index in s, including the empty-support case. Take a cylinder contained in V at level m. Its support is disjoint from s, so CRT compatibility gives a point in U and V. The whole space is nonempty, hence irreducible and closed.

**Theorem 1.9 (The common topology is not quasi-sober).**

$$\neg \operatorname{QuasiSober}(\mathbb{N},commonTopology)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LiLiZhaoFiniteCRT.commonTopology_not_quasiSober` (`✓ std3`). ∎

*Citation.* Xiangrui Li, Qingguo Li, Dongsheng Zhao (2025). *Sober topologies on a set*. URL: <https://arxiv.org/abs/2508.05419v1>.

*Commentary.*

Quasi-sobriety would give the whole irreducible closed space a generic point x. T1 makes the closure of the singleton x equal to that singleton; the natural number x+1 shows that it is smaller than the whole space. Thus even existence of a generic point fails, and in particular the space is not sober.

These are the prime-tail topologies of Li--Li--Zhao, Sober topologies on a set, Example 3.9. Their underlying N-zero is Lean's N. Their prime p(k), indexed from 1, is primeSeq(k-1); their tail at index n+1 is tailTopology(n). This reindexing preserves every tail and their common-open topology. Their meet is our Mathlib supremum, by the order convention above. The construction proves every tail Hausdorff and the common topology T1, irreducible on the whole space, and non-quasi-sober. No claim about the separate cofinite-topology comparison in Remark 3.10 is included.

## References

- Truth anchor: `D5/S3/Topology/LiLiZhaoFiniteCRT.commonTopology_not_quasiSober`
- Truth anchor: `D5/S3/Topology/LiLiZhaoFiniteCRT.commonTopology_t1`
- Truth anchor: `D5/S3/Topology/LiLiZhaoFiniteCRT.commonTopology_univ_irreducible`
- Truth anchor: `D5/S3/Topology/LiLiZhaoFiniteCRT.disjoint_cylinders_nonempty`
- Truth anchor: `D5/S3/Topology/LiLiZhaoFiniteCRT.finiteCylinder_basis_of_isOpen`
- Truth anchor: `D5/S3/Topology/LiLiZhaoFiniteCRT.finiteCylinder_nonempty`
- Truth anchor: `D5/S3/Topology/LiLiZhaoFiniteCRT.finite_crt`
- Truth anchor: `D5/S3/Topology/LiLiZhaoFiniteCRT.tailSubbasis`
- Truth anchor: `D5/S3/Topology/LiLiZhaoFiniteCRT.tailTopology_t2`
