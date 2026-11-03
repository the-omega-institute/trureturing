# Formal generator coefficient extraction and the exact physical scalar.

## Abstract

Formal generator coefficient extraction and the exact physical scalar.

For endpoint maps s,t, the incidence degree d_v counts all edge endpoints at v. The mass M_v(s,t,n,k) is the sum of k_e over edges with source v plus n_e-k_e over edges with target v. The selected total is three on A and two off A. Source splits satisfy 1 <= k_e < n_e. Boolean choices are false off A; a true choice receives at s(e), a false choice at t(e). Set f_d(0)=1, f_d(1)=d/3 and f_d(r)=d(d+1)/12 for r at least two. The polynomial R_(d,s,t) sums product_v f_(d_v)(r_v) times product_v (1+(-1)^d_v X^(d_v+r_v)) over every unordered two-edge set and all its endpoint choices. Here r_v is the number of chosen endpoints receiving at v. Let h count the vertices for which d_v is odd. Set C(s,t,a)=50(-1)^e 12^e product_v(d_v-1)!/a, where e is the edge count. H_N denotes canonical homogenization. The source vertices, endpoint factors and formal generator sums are those of equation (2.19); formalSource(M,f) sums f(n) times product_e Z_(2n_e-1) over all totals between two and M. At cutoff M, allVertexSource is the sum over every total map n:E to the integers from two to M of its payload times product_e Z_(2n_e-1). The payload is (-2)^e/a times product_e((-1)^n_e/n_e), times the sum over every split map with 1 <= k_e < n_e of product_e binomial(2n_e,2k_e) times the product over ALL vertices v of the following factor: ((M_v-1)!/(M_v-d_v+2)!) times product over source incidences of endpointFactor(k_e), times product over target incidences of endpointFactor(n_e-k_e), times (1+(-1)^d_v X^M_v). Here endpointFactor(k)=(2k)!/((k-1)! k!), M_v is the mass defined above, and d_v is incidence degree. The full binary source replaces the last factor by lambda1^M_v+(-1)^d_v lambda2^M_v, with variable zero representing lambda2 and variable one lambda1. All factorials are taken on natural numbers; admissible split masses are at least the incidence degrees. The formal generators are algebraic variables; no independence statement about numerical zeta values is used.

The formal generator monomial is Z_5^2 Z_3^(e-2). For every cutoff M at least three, its coefficient forces exactly two distinct edges to have total three and every other edge total two. The literal all-vertex equation (2.19) supplies the factorial, binomial, degree-parity and automorphism factors. Equation (2.31) literally prints m, whereas (2.19) prints m+1; no erratum or authorial intent is inferred. The split and Boolean endpoint choices are in bijection. A selected two-edge set has all four endpoint choices, and the receiving increments sum to two. The source coefficient equals C_T times the complete allocation polynomial; its exact scalar is 50*(-1)^e*12^e*product_v(d_v-1)!/aut. The aut parameter here is instantiated by the actual graph automorphism order in TreePairTheorem. Variable zero is the dimensionless second coupling, and variable one is the first. The source binary vertex contains lambda1^M+(-1)^degree*lambda2^M and all original factorial factors. The proof uses the total incident mass 2e+2 and canonical homogenization of finite sums and products. The full source bridge is derived, not assumed.

**Lemma 1.1 (Formal pair coefficient).**

$$\begin{aligned}E\ \text{finite},\ R\ \text{a commutative semiring},\ M\ge3,\ f:(E\to\mathbb{N})\to R\\{}[Z_{5}^{2}Z_{3}^{|E|-2}]\operatorname{formalSource}(M,f)=\sum_{A\subseteq E,\ |A|=2}f(\operatorname{selectedTotals}(A))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairSource.formal_pair_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.2 (Source scalar).**

$$\begin{aligned}e,a\in\mathbb{N},\ e\ge2,\ a\neq0,\ D\in\mathbb{R}\\\frac{(-2)^{e}(-1)^{2e+2}}{9\cdot2^{e-2}a}\frac{24^{e-2}360^{2}D}{2^{e+1}}=\frac{50(-1)^{e}12^{e} D}{a}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairSource.source_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.3 (Sourcemass total).**

$$\begin{aligned}V,E\ \text{finite},\ s,t:E\to V,\ n,k:E\to\mathbb{N},\ (\forall e\ k_{e}\le n_{e})\implies\sum_{v} M_{v}(s,t,n,k)=\sum_{e} n_{e}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairSource.sourceMass_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.4 (Sum ordered distinct twice).**

$$\begin{aligned}E\ \text{finite},\ R\ \text{a commutative ring},\ F:\mathcal{P}(E)\to R\\\sum_{e,f\in E,\ e\neq f}F(\{e,f\})=2\sum_{A\subseteq E,\ |A|=2}F(A)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairSource.sum_ordered_distinct_twice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.5 (Sum sourcesplits).**

$$\begin{aligned}E\ \text{finite},\ R\ \text{an additive commutative monoid},\ A\subseteq E,\ f:(E\to\mathbb{N})\to R\\\sum_{k\in\operatorname{sourceSplits}(\operatorname{selectedTotals}(A))}f(k)=\sum_{b\in\operatorname{edgeChoices}(A)}f(\operatorname{choiceSplit}(A,b))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairSource.sum_sourceSplits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.6 (Receivedcount pairchoice).**

$$\begin{aligned}E\ \text{finite},\ s,t:E\to V,\ e\neq f,\ p,q\in\operatorname{Bool},\ v\in V\\\operatorname{receivedCount}(s,t,\{e,f\},\operatorname{pairChoice}(e,f,p,q),v)=\mathbf{1}_{\operatorname{endpoint}(e,p)=v}+\mathbf{1}_{\operatorname{endpoint}(f,q)=v}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairSource.receivedCount_pairChoice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.7 (Exact source coefficient).**

$$\begin{aligned}V,E\ \text{finite},\ s,t:E\to V,\ e=|E|\ge2,\ |V|=e+1,\ d_{v}=\operatorname{sourceDegree}(s,t,v)\ge1,\ a\in\mathbb{N},\ a\neq0,\ M\ge3\\{}[Z_{5}^{2}Z_{3}^{e-2}]\operatorname{allVertexSource}(s,t,a,M)=C(s,t,a)R_{d,s,t}(X)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairSource.exact_source_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.8 (Treeallocation degree multiplicity).**

$$\begin{aligned}V,E\ \text{finite},\ s,t:E\to V,\ e=|E|\ge2,\ d_{v}\ge1,\ \sum_{v} d_{v}=2e,\ R=R_{d,s,t}\\\operatorname{natDegree}(R)=2e+2\land R\neq0\land\operatorname{leadingCoeff}(R)=R_{0}\land\operatorname{ord}_{1}(R)=h\land R_{0}>0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairSource.treeAllocation_degree_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.9 (Full source coefficient homogenize).**

$$\begin{aligned}V,E\ \text{finite},\ s,t:E\to V,\ a,M\in\mathbb{N},\ M\ge3,\ e=|E|\\{}[Z_{5}^{2}Z_{3}^{e-2}]\operatorname{fullVertexSource}(s,t,a,M)=H_{2e+2}([Z_{5}^{2}Z_{3}^{e-2}]\operatorname{allVertexSource}(s,t,a,M))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairSource.full_source_coefficient_homogenize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Theorem 1.10 (Exact full source coefficient).**

$$\begin{aligned}V,E\ \text{finite},\ s,t:E\to V,\ e=|E|\ge2,\ |V|=e+1,\ d_{v}=\operatorname{sourceDegree}(s,t,v)\ge1,\ a\in\mathbb{N},\ a\neq0,\ M\ge3\\{}[Z_{5}^{2}Z_{3}^{e-2}]\operatorname{fullVertexSource}(s,t,a,M)=C(s,t,a)H_{2e+2}(R_{d,s,t})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairSource.exact_full_source_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairSource.exact_full_source_coefficient`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairSource.exact_source_coefficient`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairSource.formal_pair_coefficient`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairSource.full_source_coefficient_homogenize`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairSource.receivedCount_pairChoice`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairSource.sourceMass_total`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairSource.source_scalar`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairSource.sum_ordered_distinct_twice`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairSource.sum_sourceSplits`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairSource.treeAllocation_degree_multiplicity`
- Dependency: [D5/S3/Zeros/LeeYang/TreePairStability](TreePairStability.md)
