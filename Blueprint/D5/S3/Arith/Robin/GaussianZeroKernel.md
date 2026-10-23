# Gaussian polynomial zero response

## Abstract

Complex Gaussian moments determine the signed response of each zero exponential.

**Theorem 1.1 (Exact moments, polynomial response, and positive envelope).**

Lean statement: `D5/S3/Arith/Robin/GaussianZeroKernel.gaussian_zero_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GaussianZeroKernel.gaussian_zero_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m>0 and real M, let g(y)=exp(-(y-M)^2/(4m))/sqrt(4*pi*m), u(y)=(y-M)/(2m), and F(w)=exp(m*w^2+M*w). For every complex w, the functions exp(w*y)*g(y), u(y)*exp(w*y)*g(y), and u(y)^2*exp(w*y)*g(y) are integrable on the whole real line. Their integrals are F(w), w*F(w), and (w^2+1/(2m))*F(w).

For real gamma set P(y)=(u(y)+i*gamma)*(u(y)+i*gamma-1)-1/(2m), K(y)=-Re(exp(-i*gamma*y)*P(y))*g(y), and v(y)=2*(u(y)^2+gamma^2+1)*g(y). If rho is distinct from 0 and 1 and a=1/(rho*(1-rho)), then both a*exp(rho*y)*exp(-i*gamma*y)*P(y)*g(y) and a*exp(rho*y)*v(y) are integrable. Their integrals are -F(rho-i*gamma) and 2*a*(rho^2+gamma^2+1+1/(2m))*F(rho), respectively.

The envelope v is nonnegative. When m>=1, |K(y)|<=v(y) and |exp(-i*gamma*y)*P(y)|*g(y)<=v(y) at every y. A lower bound on m is necessary: at gamma=0 and y=M, the inequality would require 1/(2m)<=2. The moment and response identities hold throughout m>0.

Mathlib's complex Gaussian moment-generating function, its integral derivative formula, and exponential-moment integrability supply the raw moments. Centering and expanding the quadratic gives the response. At w=rho-i*gamma the polynomial factor becomes rho*(rho-1), so multiplication by a gives -1. These are individual integrals; summation over an infinite zero family also requires a summable bound on the integrals of the norms.

## References

- Truth anchor: `D5/S3/Arith/Robin/GaussianZeroKernel.gaussian_zero_kernel`
