# BaezDuarteMertensTransfer

## Abstract

The signed unweighted Mertens bound implies power decay of the original finite coefficients.

Here c(k) is the existing actual baezDuarte finite binomial coefficient, M(x) is exactly the sum of ArithmeticFunction.moebius(n), cast to the reals, over the natural interval Icc 1 floor(x), and kernel(k,x)=x^(-2)*(1-x^(-2))^k. GlobalM(a) means there exists real A>0 such that for every real x>=1, |M(x)|<=A*Real.rpow(x,a). EventualM(a) means there exist real A>0 and real X such that the same inequality holds for every real x>=X. CoefficientBound(a) means there exists real C>0 such that for every natural k>=1, |c(k)|<=C*Real.rpow(k,a/2-1). No RH hypothesis is assumed by this transfer; the final necessity direction needs the independently verified RH-to-Mertens theorem.

**Theorem 1.1 (The signed Abel identity).**

$$k\ge 1\Rightarrow \operatorname{c}\left(k\right)=-\operatorname{integralIoi}\left(1, \operatorname{MtimesDerivative}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteMertensTransfer.baez_duarte_abel_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

For every k>=1, c(k) equals minus the integral over x>1 of M(x)*deriv(kernel(k))(x). The proof uses the public Abel summation theorem with mu(0)=0, retains mu(1)=1, proves local derivative integrability and domination, and proves the boundary term tends to zero. The signed coefficient HasSum identifies the limit.

**Theorem 1.2 (Full quantitative Mertens transfer).**

$$0\le a\land a<2\land \operatorname{GlobalM}\left(a\right)\Rightarrow \operatorname{CoefficientBound}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteMertensTransfer.baez_duarte_decay_of_mertens_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

For each real a with 0<=a<2, GlobalM(a) implies CoefficientBound(a). With b=1-a/2>0, the two integrable weighted derivative terms contribute A*(B(b,k+1)+k*B(b+1,k)) in real parts. The public beta recurrence and GammaSeq bound give exponent a/2-1 and a constant independent of k.

**Theorem 1.3 (The actual finite prefix is absorbed).**

$$0\le a\land a<2\land \operatorname{EventualM}\left(a\right)\Rightarrow \operatorname{CoefficientBound}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteMertensTransfer.baez_duarte_decay_of_eventual_mertens_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The eventual bound extends to x>=1 using the actual finite sum: |M(x)|<=floor(x)<=x and x^a>=1. The constant max(A,max(1,X)) retains every prefix term, including n=1. The resulting bound is then passed to the quantitative transfer.

## References

- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteMertensTransfer.baez_duarte_abel_identity`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteMertensTransfer.baez_duarte_decay_of_eventual_mertens_bound`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteMertensTransfer.baez_duarte_decay_of_mertens_bound`
- Dependency: [D5/S3/Weil/Analytic/BaezDuarteMertensKernel](BaezDuarteMertensKernel.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RieszBaezDuarte](../ZetaBridge/RieszBaezDuarte.md)
