# Actual Lattice Field Products

## Abstract

Both ordered actual lattice-field products use the same two-variable kernel, with finite sums on each recipient.

Let r be any natural number, including zero. Let G be any symmetric integral r by r matrix with even diagonal, without a positivity hypothesis. Charges are functions Fin(r) to Z. The oscillator algebra P is the complex multivariate polynomial algebra on Fin(r) times N, and V is the space of finite-support charge-indexed functions with values in P. Write B(alpha,beta) for the integral bilinear pairing.

F_alpha(k) denotes the actual raw Laurent coefficient of the exponential charge-changing lattice field, using the creation exponential, polynomial annihilation translation, and lower-triangular parity cocycle epsilon. Its normalized mode m has raw index k=-m-1. The common kernel K(alpha,beta)(u,v) uses the translated pair polynomial with variables U,W: X(i,n) maps to X(i,n)-B(alpha,e_i) U^(n+1)-B(beta,e_i) W^(n+1). On single(delta,p), its summand at exponent pair e has coefficient q_e c_alpha(u-B(alpha,delta)+e_0) c_beta(v-B(beta,delta)+e_1), with charge alpha+beta+delta and prefactor epsilon(alpha+beta,delta).

**Theorem 1.1 (Both products on every recipient and every pair of integer indices).**

$$\forall G,a,b,k,l,v, \operatorname{Finite}\left(\operatorname{supp}\left(\operatorname{jmap}\left(j, \operatorname{h}\left(\operatorname{B}\left(a, b\right), j\right) \operatorname{K}\left(a, b, k-\operatorname{B}\left(a, b\right)+j, l-j, v\right)\right)\right)\right) \land \operatorname{Finite}\left(\operatorname{supp}\left(\operatorname{jmap}\left(j, \operatorname{h}\left(\operatorname{B}\left(a, b\right), j\right) \operatorname{K}\left(a, b, k-j, l-\operatorname{B}\left(a, b\right)+j, v\right)\right)\right)\right) \land (\operatorname{F}\left(a, k, \operatorname{F}\left(b, l, v\right)\right)=\operatorname{epsilon}\left(a, b\right) \operatorname{finsum}\left(j, \operatorname{h}\left(\operatorname{B}\left(a, b\right), j\right) \operatorname{K}\left(a, b, k-\operatorname{B}\left(a, b\right)+j, l-j, v\right)\right)) \land (\operatorname{F}\left(b, l, \operatorname{F}\left(a, k, v\right)\right)=\operatorname{epsilon}\left(b, a\right) \operatorname{finsum}\left(j, \operatorname{h}\left(\operatorname{B}\left(a, b\right), j\right) \operatorname{K}\left(a, b, k-j, l-\operatorname{B}\left(a, b\right)+j, v\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeGeneratingFieldProducts.actual_lattice_field_products` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all charges alpha,beta, all integers k,l and every v in V, both displayed summands have finite support as functions of the natural index j. Here h_b(j) is coeff_j of rescale(-1)(binomialSeries(C,b)), with parameter ring Z and b=B(alpha,beta). Thus h_b(j)=(-1)^j choose(b,j), including negative integer b. The two product equations are F_alpha(k)(F_beta(l)v)=epsilon(alpha,beta) sum_j h_b(j) K(alpha,beta)(k-b+j,l-j)v and F_beta(l)(F_alpha(k)v)=epsilon(beta,alpha) sum_j h_b(j) K(alpha,beta)(k-j,l-b+j)v. The notation jmap in the display forms the function of j, and finsum sums its finite support in the recipient space V.

For single(delta,p), write q for the translated pair polynomial. A nonzero forward summand requires j<=l-B(beta,delta)+sup_e(e_1), where e ranges over q.support. The reverse bound is j<=k-B(alpha,delta)+sup_e(e_0). A negative upper bound forces every summand to vanish. These bounds depend on the recipient; finite charge supports extend finiteness to arbitrary v. No uniform polynomial or recipient cutoff is assumed.

Nested polynomial maps identify translating the beta-translated polynomial by alpha with the same pair polynomial. The actual creation-coefficient transport identity gives the binomial contraction for every integer creation index, including negative indices. Applying coefficient linear maps and exchanging sums with already finite support yields the first product. Bilinear additivity and cocycle multiplicativity match its charge shifts and scalar factors. Swapping the pair variables proves kernel symmetry and gives the second product.

The classical source is Bakalov-Kac, arXiv math/0402315v1 (2004-02-19), section 4.1, printed pages 8-9, equations (4.12) and (4.14), with published DOI 10.1142/9789812702562_0001. The Library note records the inspected version and the limits of the FLM citation. This theorem does not establish mutual locality, a full lattice VOA constructor, the Leech or Monster construction, a full CFT, string theory, or an AdS/CFT bridge.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeGeneratingFieldProducts.actual_lattice_field_products`
- Dependency: [D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality](LatticeGeneratingFieldLocality.md)
