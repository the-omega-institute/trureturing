# The fourth square-displacement coefficient

## Abstract

The next square-displacement coefficient is strictly negative for every natural q at least three, with an exact second cancellation and a nonzero full natural cubic scaling limit.

In the Bajnok-Beatty square-displacement setting, put Q=(q as a real number), nu=Q^2, beta=dbonacciPerronRoot(q^2), sigma=log(beta), w=exp(-nu*sigma), alpha=(nu-1)/(4*Q*sigma), and g=beta-nu*w. All coefficient functions are total functions on the natural numbers, using the ordinary total real division operation. Pointwise claims below require q>=3; the limit has the full natural domain, including even indices.

Define C=2*(nu+1)/(3*(nu-1)^2), E=4/(3*(nu-1)^2), B=16*(nu^2+nu+1)/(15*(nu-1)^4), and H(s)=C*s^3*(exp(s)-nu^2*exp(-nu*s)). The next analytic term is K(s)=-E*s^3*(exp(s)-nu*exp(-nu*s))+B*s^5*(exp(s)-nu^3*exp(-nu*s))+(C^2/2)*s^6*(exp(s)+nu^4*exp(-nu*s)).

Retain the existing coefficient d=((nu+1)*sigma/(6*Q*(nu-1)))*(((nu^2+1)*beta-2*nu^2)/((nu+1)*beta-2*nu)). Put u=-sigma*d/alpha, G2=beta+nu^2*w, and Hp=C*(3*sigma^2*(beta-nu^2*w)+sigma^3*(beta+nu^3*w)). The coefficient studied here is e=d^2/alpha+alpha/(sigma*g)*(G2*u^2/2+Hp*u+K(sigma)). Thus e is specified by the original analytic expansion rather than by its sign or its limiting value.

**Theorem 1.1 (Strict sign, exact cancellation, compact formula, and full natural scaling).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementFourthCoefficient.square_displacement_fourth_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementFourthCoefficient.square_displacement_fourth_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural q>=3, e(q)<0. For every such q one has u=-H(sigma)/g and the exact second cancellation G2*u^2/2+Hp*u+K(sigma)+g*(sigma*d^2/alpha^2-sigma*e/alpha)=0.

Set r=nu*(nu-1)*w/g, A=[2*(nu^2-4*nu+1)-4*(nu+1)*(3*nu^2-2*nu-2)*r-10*(nu+1)^2*r^2]/[45*(nu-1)^3], and J=beta*nu^2*w*(nu+1)^2/[9*(nu-1)*g^3]. For every natural q>=3, Q*e=-sigma/[3*(nu-1)]+A*sigma^3+J*sigma^4 exactly. As q tends to infinity through all natural numbers, Q^3*e(q) tends to -log(2)/3+2*(log(2))^3/45.

The existing repository PerronRoot, GaussianRoot, Correction, and Profile proofs provide beta+w=2, 2/3<sigma<log(2), g>0, d>0, and g*(sigma*d/alpha)=H(sigma). Substituting this last cancellation into the defining expression for e removes the independent d and u factors. Expanding with beta+w=2 leaves a nonzero positive sixth-degree residual; after the defining prefactor this is exactly J*sigma^4. The full implicit cancellation includes e and still vanishes exactly. The surviving expression has only sigma, sigma^3, and sigma^4, with the explicit rational coefficients A and J above.

A single finite tail estimate proves the strict sign. The function F4(v)=v^4*exp(-2v/3) is antitone on v>=9 because its derivative is v^3*(4-2v/3)*exp(-2v/3)<=0. The exponential sum through degree thirteen at six is 10059173/25025>400, so F4(v)<6561/400. With nu>=9 and sigma>2/3 this gives (nu+1)*w<1/40 and nu^2*(nu+1)^2*w<81/4. Consequently g=2-(nu+1)*w>79/40, A<=2/[45*(nu-1)], and 0<=J<=288000/[493039*(nu-1)].

A finite exponential lower bound at 7/10 gives log(2)<7/10. To bound A*sigma^3, first multiply the upper bound for A by sigma^3>=0, then bound the resulting positive coefficient times sigma^3 using sigma<7/10. This reasoning allows A to be negative. The compact expression therefore gives (nu-1)*Q*e<=-2/9+(2/45)*(7/10)^3+(288000/493039)*(7/10)^4=-740234623/11093377500<0.

For scaling, the standard limit x^4*exp(-x) tending to zero, composed at x=2nu/3, supplies a quartic majorant. Squeezing against it shows nu^j*w tends to zero for every j<=4. The existing Perron limit yields beta tending to 2 and sigma tending to L=log(2); hence g tends to 2, r tends to zero, and nu*r tends to zero. Writing all ratios in terms of 1/nu gives nu*A tending to 2/45 and nu*J tending to zero. Multiplying the compact identity by nu yields the asserted full natural limit.

The negative linear term dominates both surviving positive upper bounds uniformly. Analytically this is why the next displacement appears with a negative coefficient, while the cubic rescaling has a finite nonzero value. The result extends the repository's existing Bajnok-Beatty coefficient analysis. It does not assert a finite inverse-sixth-power remainder envelope, an actual integer threshold bracket, interpolation of finite counts, a rounding law, or literature novelty.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementFourthCoefficient.square_displacement_fourth_coefficient`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattySquareDisplacementCorrection](BajnokBeattySquareDisplacementCorrection.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattySquareDisplacementProfile](BajnokBeattySquareDisplacementProfile.md)
