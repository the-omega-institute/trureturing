# The Complete Xi Square Exterior Remainder

## Abstract

The actual xi square source has its complete divisor and an entire exterior factor with a whole-plane square-mass remainder.

**Theorem 1.1 (A complete actual divisor and exterior remainder).**

Lean statement: `D5/S3/Zeros/Resolvent/XiSquareExteriorRemainder.xi_square_cluster_exterior_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/XiSquareExteriorRemainder.xi_square_cluster_exterior_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F(z) = xi(1/2 + i sqrt(z))/xi(1/2). Even square descent makes F entire and independent of the square-root branch. For every exhaustive ZeroData Z, rho_i = 1/2 + i gamma_i and the analytic order of F at gamma_i squared is the actual multiplicity m_i. Gamma can be complex; the theorem does not assume the Riemann hypothesis or simple zeros. The unconditional canonical ZeroData provider supplies an actual inhabitant of the source type.

Select any finite set s of distinct zero indices. Retain one factor 1 - z/gamma_i squared for every element of Fin(m_i) when Re(gamma_i) is positive; negative-height indices supply the identity. Q_s is the product of all selected multiplicity fibers, and A_s is the complete infinite product over the remaining positive-height fibers. The normalized resolvent, reflection pairing and entire identity theorem identify F with its full canonical product. Splitting that actual product proves F(z) = Q_s(z) A_s(z) for every complex z, while A_s is entire. No tail or finite exceptional set is omitted.

At any complex a with A_s(a) nonzero, put M_s(a) equal to the complete sum of m_i divided by norm(a - gamma_i squared) squared over i outside s with positive real part of gamma. The exact drift-normalized exterior is g_a(w) = A_s(a+w)/A_s(a) times exp(-w A_s'(a)/A_s(a)). It is entire, and for every complex w its remainder norm(g_a(w)-1) is at most (exp(1/2)-1) times norm(w) squared times M_s(a) times exp(norm(w) squared times M_s(a)/2). This is a whole-plane estimate, including product zeros, rather than a small principal-log disk estimate.

The reusable estimate uses E(u) = (1-u) exp(u). Its scalar norm and remainder bounds propagate through a finite product as the sharp invariant norm(product E(u_i)-1) at most (exp(1/2)-1) S exp(S/2), where S is the sum of norm(u_i) squared. Taking the limit over all finite subsets preserves the complete square-summable product. The recenter identity then uses exact infinite product division and the complete logarithmic-derivative sum, and sigma fibers recover the actual multiplicities in M_s(a). The finite sharp square-budget recurrence is the live new proof content; the analytic suppliers and actual-source bindings are used on that proof path. These are classical canonical-product estimates, with no claim of ordinary mathematical originality.

An application of the same primary Gaussian bound gives the complete exterior derivative estimate. With the exact displacement function g_a(w) and the same complete multiplicity-weighted mass M_s(a) defined above, every complex w satisfies norm(g_a'(w)) at most exp(1/2) times norm(w) times M_s(a) times exp(norm(w) squared times M_s(a)/2). Differentiating E(w c_i) gives -w c_i squared exp(w c_i); the scalar Young inequality and the primary Gaussian bound put every finite-product derivative term under one common Gaussian majorant. Mathlib's finite-product derivative rule, norm triangle inequality and summation then give the finite square-mass bound. Locally uniform derivative convergence, the exact recenter identity and the sigma multiplicity fibers carry it to the full actual exterior. This complete application was checked by an exact Lean compilation and is recorded here as reuse, rather than a new derivative theorem. It assumes A_s(a) nonzero but requires neither RH nor a nonzero value of g_a at w, and includes every product zero. The two responses T_n(g_a') and (T_n g_a)' are distinct; this derivative estimate alone supplies neither response bound nor their commutation.

The hypotheses explicitly include A_s(a) nonzero. The result supplies neither the growing-multiplicity joint extraction budget nor the signs of the coupled Jensen responses for a nonempty Q_s. Those signs and the Riemann hypothesis remain separate mathematical obligations.

## References

- Truth anchor: `D5/S3/Zeros/Resolvent/XiSquareExteriorRemainder.xi_square_cluster_exterior_remainder`
- Dependency: [D5/S3/Analytic/Dilation/ScalarUnitDressing](../../Analytic/Dilation/ScalarUnitDressing.md)
- Dependency: [D5/S3/Analytic/Fourier/XiThetaTransform](../../Analytic/Fourier/XiThetaTransform.md)
- Dependency: [D5/S3/Analytic/Isolation/EntireEvenSquareDescent](../../Analytic/Isolation/EntireEvenSquareDescent.md)
- Dependency: [D5/S3/Weil/ZeroData/UnconditionalCanonicalZeroData](../../Weil/ZeroData/UnconditionalCanonicalZeroData.md)
- Dependency: [D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation](../../Weil/ZetaBridge/AlternatingZetaContinuation.md)
- Dependency: [D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare](../../Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.md)
- Dependency: [D5/S3/Zeros/Resolvent/XiNormalizedResolvent](XiNormalizedResolvent.md)
