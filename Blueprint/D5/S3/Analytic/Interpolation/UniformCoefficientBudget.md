# Uniform coefficient budgets and joint Laplace certificates

## Abstract

The same exact interpolating polynomial separates two actual atomic supports without paying an inverse node-spacing cost.

**Definition 1.1 (The monomial coefficient one-norm).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1`

*Formalization.* `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1` (`✓ std3`).

*Citation.* Jiyuan Tan (2026). *Causalean polynomial coefficient one-norm*. URL: <https://github.com/Jiyuan-Tan/CausalSmith/tree/e56c1daecf6fc95cad721ff71d188e8fc526cbca/Causalean/Mathlib/Analysis/Approximation/Chebyshev>.

*Commentary.*

For every real polynomial p, coeffL1(p) is the sum of |p.coeff k| over its finite support. The leaf definition and elementary norm proofs follow the licensed Causalean source.

**Lemma 1.2 (The triangle inequality).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_add_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_add_le` (`✓ std3`). ∎

*Citation.* Jiyuan Tan (2026). *Causalean polynomial coefficient one-norm*. URL: <https://github.com/Jiyuan-Tan/CausalSmith/tree/e56c1daecf6fc95cad721ff71d188e8fc526cbca/Causalean/Mathlib/Analysis/Approximation/Chebyshev>.

*Commentary.*

For every pair of real polynomials p and q, coeffL1(p+q) <= coeffL1(p)+coeffL1(q).

**Lemma 1.3 (Submultiplicativity).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_mul_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_mul_le` (`✓ std3`). ∎

*Citation.* Jiyuan Tan (2026). *Causalean polynomial coefficient one-norm*. URL: <https://github.com/Jiyuan-Tan/CausalSmith/tree/e56c1daecf6fc95cad721ff71d188e8fc526cbca/Causalean/Mathlib/Analysis/Approximation/Chebyshev>.

*Commentary.*

For every pair of real polynomials p and q, coeffL1(p*q) <= coeffL1(p)*coeffL1(q).

**Lemma 1.4 (Scalar homogeneity).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_C_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_C_mul` (`✓ std3`). ∎

*Citation.* Jiyuan Tan (2026). *Causalean polynomial coefficient one-norm*. URL: <https://github.com/Jiyuan-Tan/CausalSmith/tree/e56c1daecf6fc95cad721ff71d188e8fc526cbca/Causalean/Mathlib/Analysis/Approximation/Chebyshev>.

*Commentary.*

For every real c and real polynomial p, coeffL1(C(c)*p)=|c| coeffL1(p).

**Lemma 1.5 (A single nodal factor).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_X_sub_C`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_X_sub_C` (`✓ std3`). ∎

*Citation.* Jiyuan Tan (2026). *Causalean polynomial coefficient one-norm*. URL: <https://github.com/Jiyuan-Tan/CausalSmith/tree/e56c1daecf6fc95cad721ff71d188e8fc526cbca/Causalean/Mathlib/Analysis/Approximation/Chebyshev>.

*Commentary.*

For every real x, coeffL1(X-C(x))=1+|x|.

**Theorem 1.6 (Derivative budgets control the exact interpolant).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.interpolate_coeffL1_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.interpolate_coeffL1_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carl de Boor (2005). *Divided Differences*. URL: <https://arxiv.org/abs/math/0502036>.

*Commentary.*

Let s be any finite set of distinct real nodes in [a,b], with |x| <= 1 at every node. Let f have card(s)-1 continuous derivatives near every point of [a,b]. Suppose B(j) >= 0 for j < card(s), and |D^j f(x)| <= j! B(j) for every such j and every x in [a,b]. Then coeffL1(Lagrange.interpolate s id f) <= sum_{j<card(s)} 2^j B(j). Empty sets are allowed. Successive Rolle zeros identify each top coefficient with a derivative divided by a factorial. The Newton insertion identity and the nodal product budget propagate this estimate for the same exact interpolant. No positive separation between nodes is assumed.

**Theorem 1.7 (A common polynomial separates two atomic laws).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.atomic_endpoint_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.atomic_endpoint_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carl de Boor (2005). *Divided Differences*. URL: <https://arxiv.org/abs/math/0502036>.

*Commentary.*

Let alpha and beta be nonnegative finitely supported real weights, beta have total mass 1, eta > 0, b < y <= 1, supp(alpha) be contained in [0,y], supp(beta) in [0,b], and alpha(y) >= eta. There exists a real polynomial P of degree strictly below N=card(supp(alpha) union supp(beta)), with sum alpha(x)P(x)-sum beta(x)P(x) >= 1 and coeffL1(P) <= (2/eta) sum_{j<N} [16/(eta(y-b))]^j/(2j)!. Here P=C(2/eta)*I, where I interpolates x -> endpoint(eta,(y-x)/(y-b)) on the union of both supports; coincident atoms have combined weight. Alpha need not have total mass 1.

**Theorem 1.8 (A finite-degree certificate budget).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.sparse_endpoint_coefficient_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.sparse_endpoint_coefficient_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the preceding atomic hypotheses, for every q > 0 with N <= q+1, there is a degree-at-most-q separating polynomial with coefficient budget (2/eta) [exp(1) max(1,16/(eta(y-b)q^2))]^q.

**Definition 1.9 (The Laplace curve of finite weights).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.atomicLaplace`

*Formalization.* `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.atomicLaplace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finitely supported real weight function mu and every real t, atomicLaplace(mu,t)=sum_E mu(E) exp(-t E). The definition imposes no positivity or normalization.

**Theorem 1.10 (An exponential sampling grid).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.sparse_laplace_grid_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.sparse_laplace_grid_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative finite weights mu and nu, total nu mass 1, eta > 0, h > 0, 0 <= gmu < gnu, support energies at least their corresponding grounds, mu(gmu) >= eta, and card(supp(mu))+card(supp(nu)) <= q+1 with q > 0, a linear combination of differences at times kh, k <= q, is at least 1. Its coefficient one-norm is at most (2/eta) [exp(1) max(1,16/(eta[exp(-h gmu)-exp(-h gnu)]q^2))]^q. The exponential map is injective and preserves the combined atomic weights.

**Theorem 1.11 (Legal times with a square-order gain).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.sparse_laplace_window_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.sparse_laplace_window_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume E > 0, U > 0, 0 < eta <= 1, 0 <= gmu < gnu <= E, nonnegative weights with total nu mass 1 and ground mu mass at least eta. Both supports have at most m > 0 nodes and lie above their respective grounds. If m <= ceil(3/sqrt(eta Delta)), where Delta=(gnu-gmu)/E, put q=2m-1, M=max(1,q/U), h=1/(ME). There is a separating linear combination at times kh in [0,U/E], k <= q, with coefficient one-norm at most [288M/(eta^2 m^2 Delta)]^q.

**Theorem 1.12 (The sparse and dense branches share one order).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.ordered_laplace_joint_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.ordered_laplace_joint_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two nonnegative normalized finite weight laws on [gmu,E] and [gnu,E], with 0 <= gmu < gnu <= E, 0 < eta <= 1, ground mu mass at least eta, and at most d > 0 nodes each, every U > 0 admits the following certificate. Put Delta=(gnu-gmu)/E, m=min(d,ceil(3/sqrt(eta Delta))), q=2m-1, M=max(1,q/U), h=1/(ME). Then 0 < m <= d and m^2 Delta <= 16/eta; a separating combination at legal times kh in [0,U/E] has coefficient one-norm at most [1024M/(eta^2 m^2 Delta)]^q. The dense branch directly uses the Chebyshev noisy-moment endpoint estimate.

**Theorem 1.13 (One order gives all-time and every window certificates).**

Lean statement: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.laplace_joint_certificates`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.laplace_joint_certificates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E > 0, 0 < eta <= 1 and d > 0. Let mu and nu be nonnegative normalized finite weights with at most d nodes each, grounds gmu and gnu in [0,E], supports in [gmu,E] and [gnu,E], masses at both grounds at least eta, and distinct grounds. Put Delta=|gmu-gnu|/E, m=min(d,ceil(3/sqrt(eta Delta))) and q=2m-1. Then 0 < m <= d and m^2 Delta <= 16/eta. A separating combination at times k/E, k <= q, has coefficient one-norm <= [1024/(eta^2 m^2 Delta)]^q. For every U > 0, with M=max(1,q/U), another combination at times k/(ME) in [0,U/E] has coefficient one-norm <= [1024M/(eta^2 m^2 Delta)]^q. The same order m is used in both conclusions; the coefficient vectors may differ. No support-spacing or lower mass bound at nonground atoms is required.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.atomicLaplace`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.atomic_endpoint_certificate`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_C_mul`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_X_sub_C`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_add_le`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1_mul_le`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.interpolate_coeffL1_le`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.laplace_joint_certificates`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.ordered_laplace_joint_certificate`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.sparse_endpoint_coefficient_certificate`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.sparse_laplace_grid_certificate`
- Truth anchor: `D5/S3/Analytic/Interpolation/UniformCoefficientBudget.sparse_laplace_window_certificate`
- Dependency: [D5/S3/Analytic/ChebyshevEndpointCertificate](../ChebyshevEndpointCertificate.md)
- Dependency: [D5/S3/Analytic/SincSquareDerivativeBudget](../SincSquareDerivativeBudget.md)
