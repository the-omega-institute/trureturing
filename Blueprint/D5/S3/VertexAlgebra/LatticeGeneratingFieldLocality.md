# Actual Lattice Creation Coefficients

## Abstract

Polynomial translation of the actual lattice creation coefficients gives the binomial contraction.

Let r be any natural number, including zero, and G any symmetric integral r by r matrix with even diagonal. No positivity is assumed. Charges are functions Fin(r) to Z, oscillator variables are indexed by Fin(r) times N, and variable (i,n) has weight n+1. The polynomial algebra P is over C and the actual carrier is V, the finite-support functions from charges to P. The bilinear form is B(alpha,beta)=sum_i,j alpha_i G_ij beta_j.

For charge beta, S_beta has constant coefficient zero and positive coefficient q equal to q^(-1) times sum_i beta_i X(i,q-1). Set C_beta=exp.subst(S_beta), using the formal power-series exponential over P. Its integer creation coefficient c_beta(t) is zero for t<0 and otherwise the t.toNat coefficient. Translation T_alpha is the complex algebra map sending X(i,n) to X(i,n)-B(alpha,e_i) U^(n+1) in P[U]. These are the actual exponential and polynomial translation, rather than arbitrary coefficients satisfying a contraction hypothesis.

**Theorem 1.1 (Every integer creation index and polynomial translation coefficient).**

$$\forall G,a,b, (\forall t\in \mathbb{Z}, \operatorname{Hom}\left(\operatorname{c}\left(b, t\right), \operatorname{toNat}\left(t\right)\right)) \land (\forall t\in \mathbb{Z}, j\in \mathbb{N}, \operatorname{coeff}\left(j, \operatorname{T}\left(a, \operatorname{c}\left(b, t\right)\right)\right)=\operatorname{h}\left(\operatorname{B}\left(a, b\right), j\right) \operatorname{c}\left(b, t-j\right)) \land (\forall k\in \mathbb{Z}, d\in L, p\in P, \operatorname{F}\left(a, k, \operatorname{single}\left(d, p\right)\right)=\operatorname{rawSingle}\left(a, k, d, p\right)) \land (\forall u,v\in \mathbb{Z}, d\in L, p\in P, \operatorname{K}\left(a, b, u, v, \operatorname{single}\left(d, p\right)\right)=\operatorname{commonKernelSingle}\left(a, b, u, v, d, p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality.actual_creation_coefficient_transport` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every such G and all charges alpha,beta, written a,b in the display, Hom is weighted homogeneity for the weights n+1, toNat is integer truncation at zero, and h(B(a,b),j) denotes h_b(j) with b=B(a,b). c_beta(t) is weighted homogeneous of degree t.toNat for every integer t. For every integer t and natural j, coeff_j(T_alpha(c_beta(t))) = h_b(j) c_beta(t-j), where b=B(alpha,beta) and h_b(j) is coeff_j of rescale(-1)(binomialSeries(C,b)), with its parameter ring explicitly Z. Thus h_b(j)=(-1)^j choose(b,j); negative b uses integer binomial coefficients, without a Laurent-series integer power.

The proof differentiates the actual substituted exponential and proves the homogeneous grading by strong induction on its coefficient recurrence. After translation, the derivative difference has coefficient -B(alpha,beta) U^(n+1). Multiplication by 1-Uw converts this to a constant polynomial coefficient. The descending-Pochhammer recurrence for integer choose gives the same differential equation for the binomial factor. Equality of constant coefficients and strong induction identify the two actual series. Extracting their finite antidiagonal convolution proves the displayed translation coefficient equality.

The same conjunction proves that the raw field and common-kernel monomial basis extensions agree with their prescribed formulas on every single(delta,p), for every charge delta, polynomial p and all integer indices. These equalities use algebra-map linearity and finite coefficient sums; they are not assumed to hold by definition. The explicit cocycle uses the lower-triangular exponent and G_ii/2 diagonal exponent, each interpreted by integer parity.

The actual raw family is packaged by VertexOperator.of_coeff. A finite polynomial translation support gives a lower Laurent bound on each monomial state, and finite monomial and charge supports give a statewise lower bound for every carrier vector. Normalized mode m corresponds to raw Laurent power -m-1.

Bakalov-Kac, arXiv math/0402315v1 (2004-02-19), section 4.1, printed pages 8-9, equation (4.12) specifies the exponential lattice field, and (4.14) uses its annihilation-creation contraction in the ordered product. The Library note records the inspected arXiv version and published DOI 10.1142/9789812702562_0001. This coefficient theorem is classical formalization; it does not establish the two common-kernel composed mode formulas, uniform locality, lattice Jacobi, a Monster construction, full CFT, string theory or an AdS/CFT bridge.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality.actual_creation_coefficient_transport`
