# Absolute Budget for Dirichlet Inversion

## Abstract

An absolute head gap gives absolute summability and a quantitative norm bound for a Dirichlet inverse.

**Theorem 1.1 (A finite tail budget controls the entire inverse).**

$$\forall b,g\in \operatorname{ArithmeticFunction}\left(\mathbb{R}\right), \forall T\in \mathbb{R}, (\forall N\in \mathbb{N}, \sum_{1< d\le N}\left|\operatorname{b}\left(d\right)\right|\le T)\land T< \left|\operatorname{b}\left(1\right)\right|\land \operatorname{DirichletConvolution}\left(b, g\right)= delta_{1}\Rightarrow \operatorname{Summable}\left(n\mapsto \left|\operatorname{g}\left(n\right)\right|\right)\land \sum_{n\in \mathbb{N}}\left|\operatorname{g}\left(n\right)\right|\le \frac{1}{\left|\operatorname{b}\left(1\right)\right|-T}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DirichletInverseAbsBudget.dirichletInverse_absolute_budget` (`✓ std3`). ∎

*Citation.* Helge Glöckner and Lutz G. Lucht (2011). *Weighted inversion of general Dirichlet series*. URL: <https://arxiv.org/abs/1112.0749v2>.

*Commentary.*

Let b and g be real ArithmeticFunction values and T a real number. This carrier includes b(0)=g(0)=0. Multiplication means Dirichlet convolution, with unit delta at index one. Assume b*g=1, assume every finite sum of |b(d)| over 1<d<=N is at most T, and assume T<|b(1)|. Then the absolute coefficients of g are summable over all natural indices, including the zero coefficient, and their sum is at most 1/(|b(1)|-T). The first coefficient may be negative. The empty tail at N=0 is included; it forces T>=0 and the strict gap makes the denominator positive.

Write r=b-b(1) delta, B(d)=|r(d)|, G(d)=|g(d)|, and S_N=sum over 0<n<=N of |g(n)|. The inverse identity and the coefficient triangle inequality give |b(1)| |g(n)|<=delta(n)+(B*G)(n). The existing summatory convolution formula expresses the finite convolution sum as sum B(d) S_floor(N/d). Nonnegative coefficients and floor(N/d)<=N bound it by T S_N. Thus (|b(1)|-T) S_N<=1 for every finite cutoff, with cutoff zero handled by its empty sum. Since g(0)=0, the same bound controls all range sums. The existing nonnegative real-series APIs give summability and the total sum bound.

This is the classical l1 Dirichlet convolution inversion estimate. Glöckner and Lucht describe the absolute coefficient convolution Banach algebra on page 1, its ordinary Dirichlet series model on page 3, and the standard norm perturbation invertibility principle in Theorem 2(a), page 4. The quantitative estimate is the elementary Neumann-series consequence obtained by normalizing the head. The Lean proof uses finite absorption and does not assume a global norm or summability for the unknown inverse. The cited general Wiener theorem has stronger spectral hypotheses than a pointwise nonvanishing claim. This theorem supplies an inverse coefficient budget; it establishes no Riemann hypothesis or originality claim.

## References

- Truth anchor: `D5/S3/Arith/DirichletInverseAbsBudget.dirichletInverse_absolute_budget`
