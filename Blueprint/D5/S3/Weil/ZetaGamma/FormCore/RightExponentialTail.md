# Right exponential tail and its half-line energy balance

## Abstract

Exact half-line energy balances for the actual right exponential tail retain its boundary value at zero, both complex channels, and the derivative-of-weight charge.

**Definition 1.1 (The literal right exponential-tail integral).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail.rightExponentialTail`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail.rightExponentialTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real rate k and complex profile u, R_k u(t) is the actual integral from zero to infinity of exp(-k*s)*u(t+s). The rate is allowed to be negative. On a continuous compactly supported input, the relevant integral is over a bounded interval at each t, so no decay assumption is added.

**Theorem 1.2 (Exact norm balance including the actual endpoint value).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail.right_exponential_tail_energy_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail.right_exponential_tail_energy_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u be any continuous compactly supported complex profile on the real line and let k and c be arbitrary real numbers. With all norms integrated over t>0, the identity is ||u-c*R_k u||_2^2+c*(2*k-c)*||R_k u||_2^2 +c*|R_k u(0)|^2=||u||_2^2. No zero boundary value, parity, reality, differentiability of u, Fourier-domain hypothesis, or positivity of k or c is assumed.

The proof translates the literal right-tail integral to exp(k*t) times the weighted tail integral. Compact support supplies one upper cutoff. The fundamental theorem of calculus gives (R_k u)'=k*R_k u-u. Differentiating its complex norm square through the real and imaginary channels and integrating to the cutoff pays the actual value at zero. The transformed norm is then expanded with integral additivity justified on that compact interval.

For 0<=c<=2*k the two displayed correction terms are nonnegative, yielding the half-line contraction. In the W338 logarithmic coordinate u=x^(9/4)*U, k=5/4 and c=3/2 make both coefficients equal to 3/2. In the W314 coordinate g_U=x^(5/2)*U, the same c=3/2 instead gives k=3/2, a tail coefficient 9/4, and an endpoint coefficient 3/2. These applications still need their actual source-coordinate identifications. This norm balance does not construct the complete arithmetic debit, identify its Weil value, bound the full logarithmic Gamma form by physical moments, or determine the sign required for RH.

**Theorem 1.3 (Weighted energy balance with the actual endpoint and interior charge).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail.right_exponential_tail_weighted_energy_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail.right_exponential_tail_weighted_energy_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep the same continuous compactly supported complex input u. Let w and dw be arbitrary continuous real functions on the real line, with w'=dw required only at positive t. For arbitrary real k and c, all integrals over t>0 satisfy integral(w*|u-c*R_k u|^2)+c*(2*k-c)*integral(w*|R_k u|^2) +c*w(0)*|R_k u(0)|^2+c*integral(dw*|R_k u|^2) =integral(w*|u|^2). No positivity of the weight, its derivative, or the parameters is assumed in this equality.

The proof reuses the actual tail derivative and common support cutoff, differentiates w*|R_k u|^2 on the open positive interval, and integrates to the cutoff. The product rule produces the interior dw charge; continuity at zero retains the actual weighted endpoint without imposing differentiability there.

At the W314 rate k=c=3/2, the weighted tail coefficient is 9/4, while the endpoint and dw coefficients are both 3/2. With w(t)=t, dw(t)=1 and k=c=1, w(0)=0 removes the weighted endpoint, but the unweighted interior tail integral remains. These are compact-core applications. A weighted noncompact extension still requires actual integral identification and control of every retained output charge.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail.rightExponentialTail`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail.right_exponential_tail_energy_balance`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail.right_exponential_tail_weighted_energy_balance`
