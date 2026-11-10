# Arbitrary fields and arbitrary prime-field-linear intertwiners

## Abstract

Derivations are precisely the removable highest jets of the original additive-group action.

Let p be any odd prime, F=ZMod p, K any field with an F-algebra structure, and q:K→K an F-linear map with q(1)=0. The universe of K is independent of F. No finiteness, finite-dimensionality or perfection is required. On V=K[t] of degree less than p, let D be differentiation and L_a=aD+q(a)D^(p−1). Use the existing actual representation rho_a=sum_(j<p) L_a^j/j! of E=Multiplicative K, the original additive parameter group. The existing ordinary representation tau is actual translation f(t)↦f(t+a).

**Theorem 1.1 (The exact derivation criterion).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDerivationRigidity.intertwining_iff_derivation`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDerivationRigidity.intertwining_iff_derivation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist a group automorphism phi:E≃*E and a merely F-linear equivalence P:V≃V satisfying P rho_g=tau_(phi(g)) P for every original g if and only if q is the underlying linear map of a typed Derivation F K K. Neither K-linearity of P nor a chosen basis, a centralizer classification or a commutator hypothesis occurs in the statement.

For necessity, the existing prime-field moment formula L_a=−sum_(i in F) i^(p−2) rho_(i*a) transfers the actual intertwining to P L_a=phi(a) D P. This is a polynomial logarithm recovered from the action itself. Let c=phi(1)≠0 and R_c(t^j)=c^j t^j. Since R_c D=c^(-1) D R_c, P'=R_c P commutes with D and obeys P' L_a=e(a) D P', with e(a)=phi(a)/c. The inverse P'^(-1) also preserves ker D. As ker D consists precisely of constants, restriction gives an actual F-linear equivalence P0:K≃K, without a dimension argument.

For b_j(s)=s*t^j/j!, use every s in K. Evaluating on b_1(s) gives P0(a*s)=e(a)P0(s). Evaluating on b_(p−1)(s) and taking the constant coefficient gives T(a*s)+P0(q(a)*s)=e(a)T(s), where the one common F-linear map T(s)=coeff_0(P'(b_(p−2)(s))) is independent of a. Set Q=P0^(-1)T. These identities give a*Q(s)−Q(a*s)=q(a)*s simultaneously for all a,s. At s=1 this determines Q(a)=a*Q(1)−q(a). Substitution into the general relation yields q(a*b)=a*q(b)+b*q(a), the Leibniz rule. This simultaneous multiplication relation is stronger than the trace of any individual commutator.

For sufficiency, let delta be the derivation q and let deltahat apply delta to every polynomial coefficient. The coefficient formula proves deltahat D=D deltahat and deltahat(a*v)=a*deltahat(v)+delta(a)*v. Put N=deltahat D^(p−2). Since D^p=0 and 3p−6≥p, N^3=0. The uniform gauge P=I−N has inverse I+N+N². In characteristic three N² is retained; no assertion N²=0 is used.

For A_a=aD and B_a=delta(a)D^(p−1), coefficientwise Leibniz gives N A_a−A_a N=B_a. Also N B_a=0 since its derivative order is 2p−3≥p. Thus (I−N)(A_a+B_a)=A_a(I−N). Induction transfers this equality to powers, and F-linearity transfers it to the finite exponential because all inverse factorial coefficients lie in F. The resulting intertwiner uses phi=id. This is finite polynomial functional calculus in characteristic p, with no rational-module exponential or BCH premise.

For finite K, every derivation delta vanishes: x^|K|=x and the Leibniz power formula give delta(x)=|K|*x^(|K|−1)*delta(x)=0 because (|K|:K)=0. Consequently any nonzero normalized q is inequivalent to translations even when trace_(K/F)(q(a))=0 for all a. The finite-field implication is an exact application of this criterion and the existing Mathlib power/cardinality identities; it is not an additional named mathematical result.

For example, in F9=F3[alpha]/(alpha²+1), q(u+v*alpha)=v*alpha is normalized, nonzero and has trace-zero image. It violates Leibniz at alpha²: q(alpha²)=0 but 2*alpha*q(alpha)=1. The criterion rules out every automorphism of the original additive group at once. This illustrates the difference between a trace shadow and the simultaneous multiplication constraints. The existing full odd-prime finite-extension family, including all original cyclic restrictions and the dimension formula, is preserved. No literature-novelty claim is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDerivationRigidity.intertwining_iff_derivation`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation](OddPrimeJetDeformation.md)
