# Higher Derivatives of the Log-Log Scale

## Abstract

The log-log scale has strict alternating derivative signs at every positive order on x>1.

Put f(x)=log(log(x)), with natural logarithms. The domain is x>1; no claim is made at x=1 or below. In the arithmetic Robin margin the scale variable is x=log(n), so this is the derivative kernel for the triple-logarithmic threshold, rather than a derivative with respect to the integer n.

**Definition 1.1 (A positive kernel recursion).**

Lean statement: `D5/S3/Arith/Robin/LogLogHigherDerivative.positiveKernel`

*Formalization.* `D5/S3/Arith/Robin/LogLogHigherDerivative.positiveKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural m,a,b, define K(0,a,b;x)=x^(-(a+1))*(log(x))^(-(b+1)). Recursively, K(m+1,a,b;x)=(a+1)*K(m,a+1,b;x) +(b+1)*K(m,a+1,b+1;x). Every coefficient and base factor is positive on x>1. Induction also proves d K(m,a,b;x)/dx=-K(m+1,a,b;x).

**Theorem 1.2 (Strict positivity of the recursive kernel).**

Lean statement: `D5/S3/Arith/Robin/LogLogHigherDerivative.positiveKernel_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogLogHigherDerivative.positiveKernel_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural m,a,b and every real x>1, K(m,a,b;x)>0. The base inverse powers are positive; each recursion step is a sum of two positive multiples. At m=1 and a=b=0 the kernel equals (log(x)+1)/(x^2*log(x)^2), the activation density used by the mixed arithmetic response.

**Theorem 1.3 (The exact all-order sign).**

$$\forall m \in \mathbb{N}, x \in \mathbb{R},\; 1 < x \Rightarrow 0 < (-1)^{m} \cdot \operatorname{iteratedDeriv}\left(m + 1, (y \mapsto \operatorname{log}\left(\operatorname{log}\left(y\right)\right)), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogLogHigherDerivative.signed_iteratedDeriv_logLog_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural parameter m starts at zero, so the statement covers every positive derivative order m+1. The proof identifies f^(m+1)(x)=(-1)^m*K(m,0,0;x) on the entire open domain and proves strict positivity of the kernel by induction. Elementary log, power and product derivatives and locality of iterated derivatives are reused from Mathlib. This is an analytic statement for arbitrary orders and scales, with no finite cutoff.

To infer alternating mixed corner responses of actual integer menus, one still needs the repeated fundamental-theorem-of-calculus transport over the positive increment box and cancellation of the prime-local divisor terms for distinct prime axes. Those corner statements are not asserted by this module. Derivative signs also supply no absolute Robin margin, zeta zero exclusion or proof of RH.

## References

- Truth anchor: `D5/S3/Arith/Robin/LogLogHigherDerivative.positiveKernel`
- Truth anchor: `D5/S3/Arith/Robin/LogLogHigherDerivative.positiveKernel_pos`
- Truth anchor: `D5/S3/Arith/Robin/LogLogHigherDerivative.signed_iteratedDeriv_logLog_pos`
