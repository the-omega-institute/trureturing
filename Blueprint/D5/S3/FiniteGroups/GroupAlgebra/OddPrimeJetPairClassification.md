# A fixed arbitrary automorphism of the original parameter group

## Abstract

Intertwining original exponential actions reconstructs the coefficient field and detects derivation moduli.

Let p be any odd prime, including three, let F=ZMod p, and let K be any field with an F-algebra structure. The universe of K is independent of that of F. No finiteness, finite-dimensionality or perfection hypothesis is imposed. On V=K[t] of degree less than p write D=d/dt. For an F-linear q with q(1)=0 the existing original representation is rho_q(a)=sum_(j<p) (aD+q(a)D^(p−1))^j/j!. Its parameter group is the actual additive group of K, written E=Multiplicative K.

**Theorem 1.1 (The full arbitrary-field pair criterion).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPairClassification.fixed_automorphism_intertwining_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPairClassification.fixed_automorphism_intertwining_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix normalized F-linear q,r:K→K and any group automorphism phi:E≃*E. There exists a merely F-linear equivalence P:V≃V satisfying P rho_q(g)=rho_r(phi(g)) P for every original g if and only if there exist c in K×, an F-algebra automorphism sigma of K, and a typed derivation delta:Derivation F K K such that phi(a)=c*sigma(a) and r(c*sigma(a))=sigma(a)*r(c)+c^(p−1)*sigma(q(a)−delta(a)) for every a in K. Neither semilinearity of phi nor semilinearity or K-linearity of P is assumed.

The prime-field moment identity L_q(a)=−sum_(i in F) i^(p−2) rho_q(i*a) recovers the original jet operator from the group action itself. Thus an intertwiner of the original exponential representations intertwines L_q(a)=aD+q(a)D^(p−1) and L_r(phi(a)). Conversely an F-linear jet intertwiner intertwines every finite exponential: all inverse factorial coefficients lie in F. This connects both implications to the actual actions, rather than replacing their equations by unrelated operator assumptions.

For necessity set c=phi(1)≠0, b=r(c)/c^(p−1), R_c(t^j)=c^j*t^j, T=tD^(p−1), H_b=I+bT and C=H_b R_c. The identities T²=TD=0, DT=D^(p−1) and T D^(p−1)=D^(p−1) T=0 give an explicit inverse I−bT for H_b. Consequently C L_r(phi(a)) C^(-1)=e(a)D+s(a)D^(p−1), where e(a)=phi(a)/c and s(a)=(r(phi(a))−e(a)r(c))/c^(p−1). Since q(1)=s(1)=0 and e(1)=1, U=CP commutes with D.

The kernel of D is exactly the constants. Both U and U^(-1) preserve it, so their restrictions give an F-linear equivalence P0:K≃K even in infinite dimension. In the divided monomials b_j(z)=z*t^j/j!, the b_1(z) equation gives P0(a*z)=e(a)P0(z). Write u=P0(1)≠0. Then P0(a)=u*e(a), and cancellation of u proves e(a*z)=e(a)e(z). The already bijective, unital F-linear e therefore upgrades to an F-algebra automorphism sigma. The field multiplication is reconstructed from the action and the intertwiner.

For the top equation define B(z)=coeff_0(U(b_(p−2)(z))) and Q=P0^(-1) composed with B. The normalization order matters: Q(z)=sigma^(-1)(u^(-1)*B(z)). The b_(p−1)(z) equation yields B(a*z)+P0(q(a)*z)=sigma(a)B(z)+s(a)P0(z). Applying P0^(-1) shows aQ(z)−Q(a*z)=delta(a)z, where delta=q−sigma^(-1) composed with s. One common Q works for all a and z. Expanding this multiplication commutator at a*z proves delta(a*z)=a*delta(z)+z*delta(a). Delta is F-linear, so it is a typed field derivation. Rearranging its definition gives exactly the coefficient formula in the criterion.

For sufficiency let deltahat apply the original delta coefficientwise and put N=deltahat D^(p−2). Coefficientwise Leibniz gives N(aDv)−aD(Nv)=delta(a)D^(p−1)v. Both products of N with a highest-jet term vanish because 2p−3≥p. Thus G=I−N satisfies G L_q(a)=L_(q−delta)(a) G directly. Also N³=0 because 3p−6≥p; hence G^(-1)=I+N+N². At p=3 N² need not vanish and remains in the inverse. No exponential gauge or BCH expansion is required.

Let Sigma apply sigma to every coefficient. Sigma commutes with D and sends multiplication by a to multiplication by sigma(a). The coefficient formula identifies Sigma G L_q(a) with the normalized target acting on Sigma G. Therefore P=C^(-1) Sigma G is an invertible F-linear intertwiner for the original fixed phi after finite exponentiation. G is formed from delta before Sigma; changing that order would conjugate the derivation.

The consequence is a rigidity statement for a family of group actions: although phi starts in the full automorphism group of the additive parameter group, existence of an intertwiner forces phi into the scalar-semilinear subgroup. The remaining highest-jet modulus is a derivation difference after the specified scalar and field-automorphism change. The theorem does not assert that every intertwiner P is globally sigma-semilinear. The earlier arbitrary-field q-to-translation iff and the full eight-clause finite-extension family remain separate results and are preserved.

Finite-field coefficient orbit counts are further consequences requiring their own coefficient and orbit arguments; no finite-field classifier or trace criterion substitutes for this arbitrary-field fixed-phi theorem. The construction uses the existing finite exponential, logarithm, divided monomials, constants equivalence and derivation gauge, and makes no literature-priority claim.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPairClassification.fixed_automorphism_intertwining_iff`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDerivationRigidity](OddPrimeJetDerivationRigidity.md)
