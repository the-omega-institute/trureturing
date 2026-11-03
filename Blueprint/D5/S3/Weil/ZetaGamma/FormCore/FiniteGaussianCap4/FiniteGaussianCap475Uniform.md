# Uniform surplus for the reflected finite Gaussian family

## Abstract

Uniform surplus for the reflected finite Gaussian family

The actual atom is exp(9*a/2-exp(2*a)*x), and F is a finite real linear combination of these atoms. A permutation r preserves its coefficients and negates its sites; sum_i c(i)=0 is the source mass condition. Set H=integral_(0,infinity) x^(7/2)*F(x)^2 dx and Q=integral_(0,infinity) x^(7/2)*C(x)*F(x)^2 dx, where C(x)=(x/pi)^(5/2)-4*(x/pi)^(-7/2) above pi and zero elsewhere.

The linked Lean statements, rather than this description, determine the proof and its accepted axiom closure. This exposition records no independent final-acceptance or public-priority claim.

**Theorem 1.1 (The same explicit surplus for every admissible finite source).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475Uniform.finiteGaussian_cap475_uniform_coercivity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475Uniform.finiteGaussian_cap475_uniform_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite real source with this permutation symmetry and zero total mass, the declaration states (3/4+1/1000000000)*H<=Q. The surplus is independent of the number of atoms, their sites, their signed coefficients, and whether the head vanishes. No additional physical-norm, complete-tail, or matrix-entry premise is assumed.

The original matrix data give the head margin m=123/125000000. If HH and HT are the actual head and remainder norms, q is the actual head central charge, and E is the complete tail-H energy, the same suppliers give E-rho*q^2>=0, E>=70*HT, and rho*q^2<=3200*HH. Mixing the first two resulting slack bounds with theta=1/10000000000 leaves (m-3200*theta)*HH+70*theta*HT. Both coefficients exceed 1/1000000000. The original rational matrix, rho, and full tail estimate are unchanged.

**Theorem 1.2 (Uniform lower threshold for the actual tail quotients).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475Uniform.finiteGaussian_cap475_uniform_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475Uniform.finiteGaussian_cap475_uniform_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the same source is not identically zero on the whole real line, let D=integral_(pi,infinity) F(x)^2 dx and N=integral_(pi,infinity) x^6*F(x)^2 dx. The declaration states N/(pi^6*D)>19/4+1/1000000000. Its proof uses the new coercivity coefficient, the exact cap identity, positive D, and the strict actual comparison H>pi^(7/2)*D.

As a mathematical consequence, a nonempty set consisting of such quotients has lower bound 19/4+1/1000000000 and hence its real infimum is at least that number once the set and conditional-completeness side conditions are supplied. Individual strict inequalities alone do not make the infimum strictly larger than this threshold. A nonempty finite collection has an attained minimum strictly above it. These infimum statements are logical consequences described here, not additional formal declarations or a definition of the target Suzuki M.

The conclusion applies to this reflected finite Gaussian scaling family. The repository predicate originalPhysicalH6 only supplies a tail L2 condition and a sixth moment; no equality or density bridge from that larger domain is asserted. The complete Suzuki mean-zero condition is not merely sum_i c(i)=0. RH still requires the domain and form correspondence and universal complete zeroSum positivity consumed by WeilSquarePositivityCriterion.weilSquarePositivity_implies_rh. Existing UnconditionalCanonicalZeroData supplies zero data, not that missing positivity.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475Uniform.finiteGaussian_cap475_uniform_coercivity`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475Uniform.finiteGaussian_cap475_uniform_ratio`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475](FiniteGaussianCap475.md)
