# The complete zeta ordinate optimizer

## Abstract

Uniform logarithmic corrections for the complete zeta ordinate optimizer.

**Theorem 1.1 (All minimizers have the same quantitative logarithmic corrections).**

Lean statement: `D5/S3/Weil/ZeroData/ZetaOrdinateCompleteOptimizer.actual_zeta_complete_optimizer`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ZetaOrdinateCompleteOptimizer.actual_zeta_complete_optimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The indices are all distinct nontrivial complex zeta zeros rho with positive ordinate gamma(rho), retaining their analytic multiplicities m(rho) and every finite early ordinate. Set D(rho)=1/4+gamma(rho)^2 and a(rho)=m(rho)/(gamma(rho)*D(rho)). The frozen complete phase is delta(t)=sum of 2*a(rho)*(1-cos(gamma(rho)*t)).

Use the same coefficients b=1/D-2, c=2*gamma/D, g=8*gamma^2/D^2 and h=-2/gamma+8*gamma/D-4*gamma/D^2. Define F(t)=sum of a*(b*cos(gamma*t)-c*sin(gamma*t)), G(t)=sum of a*(g*cos(gamma*t)-h*sin(gamma*t)), J(epsilon,t)=delta(t)+epsilon*F(t)+epsilon^2*G(t), K=sum of a*gamma^2/D=sum of m*gamma/D^2, and A=sum of a*gamma^2/D^2.

Let phi(t)(rho)=exp(i*gamma(rho)*t), iota(rho)=i, H be the closure of the range of phi in the product complex space, and z(t)=iota*phi(t). If iota belongs to H, every z(t) belongs to H. For all real epsilon and t, the same phase envelope 2*sum(a)-2*sum(a*Im(z))+epsilon*sum(a*(b*Im(z)+c*Re(z))) +epsilon^2*sum(a*(g*Im(z)+h*Re(z))) at z(t) equals J(epsilon,t).

Under the Riemann hypothesis, the ordinate map on these indices is injective and D(rho) equals the complex norm square of rho. The ordinate-model optimization conclusion itself is unconditional.

K is strictly positive. There exist fixed real a0>0, 0<epsilon0<exp(-2), and Q>=1, chosen before epsilon and the minimizer. For every 0<epsilon<epsilon0, J(epsilon,.) attains a minimum on [-a0,a0]. Every minimizer t on that interval satisfies 0<t<a0 and has derivative zero for J(epsilon,.).

Write L=log(1/epsilon), ell=log(1/t), Cstar=4*pi*K and Dstar=4*pi*K^2. Every such minimizer satisfies abs(ell-(L+2*log(L)-log(Cstar)))<=Q*log(L)/L and abs(t*L^2/(Cstar*epsilon)-(1-4*log(L)/L))<=Q/L.

The value obeys abs(J(epsilon,t)-(epsilon*F(0)+8*A*epsilon^2 -Dstar*epsilon^2/L^2*(1-4*log(L)/L)))<=Q*epsilon^2/L^3. The same Q and epsilon0 cover all minimizers.

The proof derives existence, positive interiority, the stationary equation and the initial scale before logarithmic inversion. Same-spectrum series estimates supply the required derivative modulus for F-delta and the derivative bound for G. The optimizer parameter t is independent of an actual Robin cutoff T=1/epsilon; the theorem supplies no cutoff sign or enlargement of the certified integer interval.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ZetaOrdinateCompleteOptimizer.actual_zeta_complete_optimizer`
- Dependency: [D5/S3/Analytic/Asymptotics/LogarithmicPhaseStiffness](../../Analytic/Asymptotics/LogarithmicPhaseStiffness.md)
- Dependency: [D5/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness](ZetaOrdinatePhaseStiffness.md)
- Dependency: [D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation](../ZetaBridge/AlternatingZetaContinuation.md)
