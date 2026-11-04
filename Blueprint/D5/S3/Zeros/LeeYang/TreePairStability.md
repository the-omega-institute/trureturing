# Physical pair zero exclusion and its allocation polynomial infrastructure.

## Abstract

Physical pair zero exclusion and its allocation polynomial infrastructure.

For a finite vertex type, write kappa(d)=d^2(d^2-1)/24, c_d=(d^2-3)/(4(d-1)) when d differs from one and c_1=0. Put L_1=13/48 and, for d at least two, L_d=d(d^2-1)(d-3)/96+d(d+1)(2d-3)/(16(d-1)). The form H is one half sum_v d_v^2 t_v^2 plus one half sum_uv a_uv t_u t_v minus z/4 times sum_v d_v(d_v^2-1)t_v plus z^2 sum_v kappa(d_v). The form Q is the pairQuadratic of the source, with one half the ordered distinct-vertex sum of d_u d_v(d_u d_v-a_uv)(z+eta_u)(z+eta_v)/9 and diagonal term kappa(d_v)(z^2+2z eta_v). The Cayley map is c(w)=(1-w)/(1+w), and eta(d,X)_v=c((-1)^d_v X^d_v).

The complexification is bilinear, with no conjugates. The graph identity retains the leaf constraint t_v=2z/3 and the exact 13/48 compensation per leaf. The internal degree-2 remainder is 5/16. The finite index types have no cardinality bound. The real parts of the physical Cayley variables are positive. Leaves obey eta_v=z in real and imaginary parts. The positive real quadratic value, the real sum-of-squares certificate and the bilinear lemma imply nonvanishing for every complex X of norm less than one; independent arbitrary leaf weights are outside this statement.

**Lemma 1.1 (Rank one minus squares nonzero).**

$$\begin{aligned}J\ \text{finite},\quad w_{j}\ge0,\quad K\ge0,\quad l,t_{j}\in\mathbb{C}\\(\Re l)^{2}/2-\sum_{j} w_{j}(\Re t_{j})^{2}>0\implies l^{2}/2-\sum_{j} w_{j} t_{j}^{2}+K\neq0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairStability.rank_one_minus_squares_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.2 (Graph sum of squares).**

$$\begin{aligned}V\ \text{finite},\ R\ \text{a field of characteristic zero},\ d_{v}\ge1,\ a_{uv}=a_{vu},\ \sum_{v} a_{uv}=d_{u},\ d_{v}=1\implies t_{v}=2z/3\\H(d,a,z,t)=\sum_{v} d_{v}(d_{v}-1)(t_{v}-c_{d_{v}}z)^{2}/2+\sum_{u,v}a_{uv}(t_{u}+t_{v}-z/2)^{2}/4+\sum_{v} L_{d_{v}}z^{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairStability.graph_sum_of_squares` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.3 (Pairquadratic rank one).**

$$\begin{aligned}V\ \text{finite},\ R\ \text{a field of characteristic zero},\ d_{v}\in\mathbb{N},\ a_{vv}=0,\ z,\operatorname{eta}_{v}\in R,\ t_{v}=d_{v}(z+\operatorname{eta}_{v})/3\\\mathcal{Q}(d,a,z,\operatorname{eta})=(\sum_{v} d_{v} t_{v})^{2}/2-H(d,a,z,t)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairStability.pairQuadratic_rank_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Theorem 1.4 (Physical pairquadratic nonzero).**

$$\begin{aligned}V\ \text{finite},\ d_{v}\ge1,\ 0\le a_{uv}\le1,\ a_{uv}=a_{vu},\ a_{vv}=0,\ \sum_{v} a_{uv}=d_{u},\ \exists v\ d_{v}\ge2\\\forall X\in\mathbb{C},\ K\in\mathbb{R},\quad |X|<1\land K\ge0\implies \mathcal{Q}(d,a,c(-X),\operatorname{eta}(d,X))+K\neq0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairStability.physical_pairQuadratic_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

Write F(d,r;X)=1+(-1)^d X^(d+r) and P(X)=sum_alpha w_alpha product_v F(d_v,r_alpha,v;X). Let h count the vertices of odd d_v. Define the quotient vertex factor as the geometric sum from i=0 to d+r-1 when d is odd, and as F(d,r;X) when d is even; Q is the same weighted allocation sum with these quotient factors. The notation p_C means extension of real coefficients to the complex numbers, ord_1 means root multiplicity at one, and H_N(p)(u,v)=sum over k at most N of p_k u^k v^(N-k) is canonical homogenization. Natural degree uses zero as the natural degree of the zero polynomial.

The hypotheses quantify over arbitrary finite allocation types, positive degrees and weights, a common total mass and even degree sum. No coefficient cancellation is assumed. Every odd-degree vertex contributes one factor 1-X; the quotient has strictly positive value at one. Reciprocity transfers open-disk exclusion to the exterior. Homogenization uses the canonical Mathlib polynomial construction.

**Lemma 1.5 (Allocation degree and leading).**

$$\begin{aligned}V,A\ \text{finite},\ A\neq\varnothing,\ d_{v}>0,\ w_{\alpha}>0,\ r_{\alpha v}\in\mathbb{N},\ \sum_{v}(d_{v}+r_{\alpha v})=N,\ \sum_{v} d_{v}\ \text{even}\\\operatorname{natDegree}(P)=N\land\operatorname{leadingCoeff}(P)=\sum_{\alpha} w_{\alpha}\land P\neq0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairStability.allocation_degree_and_leading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.6 (Allocation multiplicity one).**

$$\begin{aligned}V,A\ \text{finite},\ A\neq\varnothing,\ d_{v}>0,\ r_{\alpha v}\in\mathbb{N},\ w_{\alpha}>0\implies \operatorname{ord}_{1}(P)=h\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairStability.allocation_multiplicity_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.7 (Allocation roots on circle).**

$$\begin{aligned}V,A\ \text{finite},\ d_{v},r_{\alpha v}\in\mathbb{N},\ w_{\alpha}\in\mathbb{R},\ \sum_{v}(d_{v}+r_{\alpha v})=N,\ \sum_{v} d_{v}\ \text{even}\\(\forall z\in\mathbb{C},\ |z|<1\implies P_{\mathbb{C}}(z)\neq0)\implies(\forall z\in\mathbb{C},\ P_{\mathbb{C}}(z)=0\implies|z|=1)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairStability.allocation_roots_on_circle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.8 (Allocation quotient degree).**

$$\begin{aligned}V,A\ \text{finite},\ A\neq\varnothing,\ d_{v}>0,\ r_{\alpha v}\in\mathbb{N},\ w_{\alpha}>0,\ \operatorname{natDegree}(P)=N\implies\operatorname{natDegree}(Q)=N-h\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairStability.allocation_quotient_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Lemma 1.9 (Homogenize complex eval).**

$$\begin{aligned}\forall p\in\mathbb{R}[X],\ N\in\mathbb{N},\ (u,v)\in\mathbb{C}^{2},\quad \operatorname{natDegree}(p)\le N\land v\neq0\implies H_{N}(p)(u,v)=p_{\mathbb{C}}(u/v)v^{N}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairStability.homogenize_complex_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

**Theorem 1.10 (Homogenize complex infinity).**

$$\begin{aligned}\forall p\in\mathbb{R}[X],\ N\in\mathbb{N},\ u\in\mathbb{C},\quad H_{N}(p)(u,0)=p_{N} u^{N}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/TreePairStability.homogenize_complex_infinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Natural-number subtraction is truncated at zero. All parameters range universally over the indicated domains. The displayed conditions are the hypotheses of the relation that follows.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairStability.allocation_degree_and_leading`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairStability.allocation_multiplicity_one`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairStability.allocation_quotient_degree`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairStability.allocation_roots_on_circle`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairStability.graph_sum_of_squares`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairStability.homogenize_complex_eval`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairStability.homogenize_complex_infinity`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairStability.pairQuadratic_rank_one`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairStability.physical_pairQuadratic_nonzero`
- Truth anchor: `D5/S3/Zeros/LeeYang/TreePairStability.rank_one_minus_squares_nonzero`
