# The complete arbitrary finite tree physical pair coefficient theorem.

## Abstract

The complete arbitrary finite tree physical pair coefficient theorem.

For endpoint maps s,t, put T=treeGraph(s,t), d_v=sourceDegree(s,t,v), e=|E|, and A_uv=receivingAdjacency(s,t,u,v). Let B_uv count ordered receiving incidences at u and v on distinct edges. Loopless means s(e) differs from t(e); simple means equality of unordered endpoint pairs forces equality of the edge names. NamedSpanningTree(s,t,E) selects every edge and requires the resulting simple graph to be connected and acyclic. Write F(d,r;X)=1+(-1)^d X^(d+r), kappa(d)=d^2(d^2-1)/24 and W_uv=d_u d_v(d_u d_v-a_uv)/9. The grouped polynomial G_(d,a) is sum_v kappa(d_v) F(d_v,2) product over w distinct from v of F(d_w,0), plus one half the ordered sum over u distinct from v of W_uv F(d_u,1) F(d_v,1) product over all other vertices of F(d_w,0). R is the complete endpoint allocation polynomial defined in TreePairSource. The Cayley and quadratic notation is that of TreePairStability. For the physical coefficient, the divisor is the order of the actual graph automorphism group, C_T=50(-1)^e 12^e product_v(d_v-1)!/|Aut(T)|, p is the all-vertex source coefficient at cutoff three, b is its full binary source coefficient, and q=C_T times the allocation quotient. The two homogeneous coordinates are the second and first dimensionless coupling, respectively. H_N is canonical homogenization, p_C and b_C mean complex coefficient extension, and ord_1 means root multiplicity at one.

The grouped single-vertex coefficient is d_v^2(d_v^2-1)/24. Its double sum uses ordered distinct receiving vertices with factor one half, equivalently unordered distinct pairs of coefficient d_u*d_v*(d_u*d_v-A_uv)/9. The exact receiving-incidence identity connects it to the complete allocation polynomial. The root argument uses positivity, the constrained quadratic identity and reciprocity. It asserts neither stability of an individual placement nor simplicity of the remaining roots. One fixed finite simple connected acyclic tree has at least two edges. The NamedSpanningTree src tgt Set.univ condition selects every edge; source incidence degree equals actual graph degree. The automorphism divisor is the cardinality of actual graph self-isomorphisms and is nonzero. The literal all-vertex formal coefficient has exact degree 2e+2, every complex root has norm one, and root one has multiplicity exactly the odd-degree vertex count. The quotient degree is N-h, and its roots avoid both endpoints. Zero, minus one and projective infinity are excluded. The full binary source is the homogenization and uses the same coupling ratio. This does not resolve the whole Fiol conjecture, other total multisets or tau values, arbitrary positive rho, a sum across trees, or root simplicity.

**Lemma 1.1 (Receivingpaircount add).**

$$\begin{aligned}E\ \text{finite},\ s,t:E\to V,\ \forall e\ s(e)\neq t(e),\ d_{v}=\operatorname{sourceDegree}(s,t,v)\\\forall u,v\in V,\quad B_{uv}+\mathbf{1}_{u=v}d_{u}+\mathbf{1}_{u\neq v}A_{uv}=d_{u} d_{v}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.receivingPairCount_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.2 (Sum by receivers).**

$$\begin{aligned}V,E\ \text{finite},\ R\ \text{a commutative ring},\ s,t:E\to V,\ F:V\times V\to R\\\sum_{i,j\in E\times\operatorname{Bool},\ i_{1}\neq j_{1}}F(\operatorname{incidenceVertex}(i),\operatorname{incidenceVertex}(j))=\sum_{u,v\in V}B_{uv}F(u,v)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.sum_by_receivers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.3 (Grouped cayley).**

$$\begin{aligned}V\ \text{finite},\ d_{v}\ge1,\ a_{uv}\in\mathbb{R},\ x\in\mathbb{C},\ |x|<1\\G_{d,a}(x)=((1-x)/2)^{2}\prod_{v} F_{d_{v},0}(x)(\mathcal{Q}(d,a,c(-x),\operatorname{eta}(d,x))+\sum_{v}\kappa(d_{v}))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.grouped_cayley` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.4 (Treeallocation grouped).**

$$\begin{aligned}V,E\ \text{finite},\ s,t:E\to V,\ \forall e\ s(e)\neq t(e),\ d_{v}=\operatorname{sourceDegree}(s,t,v),\ A_{uv}=\operatorname{receivingAdjacency}(s,t,u,v)\\R_{d,s,t}=G_{d,A}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_grouped` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.5 (Treeallocation disk nonzero).**

$$\begin{aligned}V,E\ \text{finite},\ (s,t)\ \text{loopless and simple},\ d_{v}=\operatorname{sourceDegree}(s,t,v)\ge1,\ \exists v\ d_{v}\ge2\\\forall x\in\mathbb{C},\quad|x|<1\implies (R_{d,s,t})_{\mathbb{C}}(x)\neq0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_disk_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.6 (Treeallocation unit circle).**

$$\begin{aligned}V,E\ \text{finite},\ (s,t)\ \text{loopless and simple},\ d_{v}=\operatorname{sourceDegree}(s,t,v)\ge1,\ \exists v\ d_{v}\ge2\\\forall x\in\mathbb{C},\quad(R_{d,s,t})_{\mathbb{C}}(x)=0\implies |x|=1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_unit_circle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.7 (Treeallocation neg one pos).**

$$\begin{aligned}V,E\ \text{finite},\ (s,t)\ \text{loopless},\ d_{v}=\operatorname{sourceDegree}(s,t,v)\ge1,\ \exists v\ d_{v}\ge2\implies R_{d,s,t}(-1)>0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_neg_one_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.8 (Named tree card vertices).**

$$\begin{aligned}V,E\ \text{finite},\ s,t:E\to V,\ \operatorname{NamedSpanningTree}(s,t,E)\implies |V|=|E|+1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.named_tree_card_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.9 (Named tree source degree).**

$$\begin{aligned}V,E\ \text{finite},\ s,t:E\to V,\ \operatorname{NamedSpanningTree}(s,t,E)\implies\forall v\in V,\ \operatorname{sourceDegree}(s,t,v)=\operatorname{degree}_{\operatorname{treeGraph}(s,t)}(v)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.named_tree_source_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.10 (Named tree degree positive).**

$$\begin{aligned}V,E\ \text{finite},\ s,t:E\to V,\ \operatorname{NamedSpanningTree}(s,t,E),\ |E|\ge2\implies\forall v\in V,\ \operatorname{sourceDegree}(s,t,v)\ge1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.named_tree_degree_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Theorem 1.11 (Complete named tree pair).**

$$\begin{aligned}V,E\ \text{finite},\ s,t:E\to V,\ \operatorname{NamedSpanningTree}(s,t,E),\ e=|E|\ge2\\p=\operatorname{physicalCoefficient}(s,t),\ b=\operatorname{physicalBinaryCoefficient}(s,t),\ q=\operatorname{physicalQuotient}(s,t),\ N=2e+2,\ h=|\{v:\operatorname{degree}_{T}(v)\ \text{odd}\}|\\p=C_{T} R_{d,s,t}\land b=H_{N}(p)\land\operatorname{natDegree}(p)=N\land p\neq0\land\operatorname{leadingCoeff}(p)=p_{0}\\\land\operatorname{ord}_{1}(p)=h\land\operatorname{ord}_{1}(p_{\mathbb{C}})=h\land p(0)\neq0\land p(-1)\neq0\\\land(\forall x\in\mathbb{C},\ p_{\mathbb{C}}(x)=0\implies|x|=1)\land p=(1-X)^{h}q\land\operatorname{natDegree}(q)=N-h\\\land q(1)\neq0\land q(-1)\neq0\land(\forall x\in\mathbb{C},\ q_{\mathbb{C}}(x)=0\implies |x|=1\land x\neq1\land x\neq-1)\\\land b(1,0)\neq0\land(\forall u\in\mathbb{C},\ u\neq0\implies b_{\mathbb{C}}(u,0)\neq0)\\\land(\forall (u,v)\in\mathbb{C}^{2},\ v\neq0\land b_{\mathbb{C}}(u,v)=0\implies|u/v|=1)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairTheorem.complete_named_tree_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.complete_named_tree_pair`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.grouped_cayley`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.named_tree_card_vertices`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.named_tree_degree_positive`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.named_tree_source_degree`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.receivingPairCount_add`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.sum_by_receivers`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_disk_nonzero`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_grouped`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_neg_one_pos`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_unit_circle`
- Dependency: [D5/S3/Observer/AgencyHolonomy/NamedTreePhaseTransport](../../Observer/AgencyHolonomy/NamedTreePhaseTransport.md)
- Dependency: [D5/S3/Zeros/LeeYang/TreePairSource](TreePairSource.md)
- Dependency: [D5/S3/Zeros/LeeYang/TreePairStability](TreePairStability.md)
