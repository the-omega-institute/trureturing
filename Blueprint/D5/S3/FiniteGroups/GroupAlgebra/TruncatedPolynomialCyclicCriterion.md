# Coefficient projectivity and a unit first coefficient

## Abstract

Two intrinsic obstructions for truncated-polynomial cyclic projectivity over an arbitrary commutative base.

The actual truncated-polynomial cyclic action has two intrinsic projectivity obstructions: coefficient projectivity over the base ring and invertibility of the first operator coefficient. The proof constructs the cyclic action and a regular-module equivalence from the derivative operator; neither is assumed.

Let R and A be arbitrary commutative unital rings, in independent Lean universes, with A an R-algebra. Let p be any prime, including 2, and assume only p·1_A=0. The integer p need not vanish or be nilpotent in R. Let h be any polynomial in A[t] with constant coefficient zero, and set beta=h.coeff 1. Put P=A[X] of degree less than p, D=d/dX, N=h(D), T=1+N and Cp=Multiplicative (ZMod p). There is no degree bound on h and no field, finite-dimensional, finitely generated, free, flat, nontrivial or reduced hypothesis on A.

The equivalence has two independent obstructions: the actual R[Cp]-module P is projective precisely when A is projective as an R-module and beta is a unit of A. Projective R A is on the right side of the equivalence; it is not a typeclass premise of either public declaration. No splitting, action, cyclic basis, norm-surjectivity or projectivity conclusion is supplied as an input.

**Definition 1.1 (The actual cyclic action over an arbitrary base).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/TruncatedPolynomialCyclicCriterion.cyclicAction`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/TruncatedPolynomialCyclicCriterion.cyclicAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact public telescope is {R : Type uR} [CommRing R] {A : Type uA} [CommRing A] [Algebra R A] {p : Nat} [Fact p.Prime] (hpA : (p : A)=0) (h : A[X]) (h0 : h.coeff 0=0). The result is Representation R (Multiplicative (ZMod p)) (Polynomial.degreeLT A p). This definition constructs the actual operator action, and is followed by one substantive public iff theorem. Every retained auxiliary declaration is private and has a consumer in that proof.

The reused polynomial/operator construction differentiates the actual degreeLT submodule over A and restricts these A-linear endomorphisms to R. Closure follows from degree_derivative_le. Powers of D are the iterated formal derivatives, and iterate_derivative_eq_zero_of_degree_lt gives D^p=0. Since h=t*h.divX, h(D)^p=0 even when h has degree at least p.

The ring homomorphism Fp→A is obtained as ZMod.castHom (ringChar.dvd hpA) A and converted to an algebra structure only inside the characteristic-p calculations. This remains valid for the zero ring: its characteristic is 1, which divides p. No CharP A p is inferred, and no Fp→R map or mixed scalar tower is used. The two maps R→A and Fp→A have separate purposes.

Evaluating (1+t)^p=1+t^p from Fp[t] at N in End_A(P) proves T^p=1. For g in Cp the action is the restriction to R of T raised to the least nonnegative representative of toAdd g. The proved period removes reduction modulo p, so ZMod.val_add proves the multiplication law. In particular, ofAdd(1 : ZMod p) acts by the actual restriction of 1+h(D). This is an action of Cp; faithfulness is not asserted.

**Theorem 1.2 (Projectivity has two independent obstructions).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/TruncatedPolynomialCyclicCriterion.projective_iff_projective_coeff_and_isUnit_coeff_one`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/TruncatedPolynomialCyclicCriterion.projective_iff_projective_coeff_and_isUnit_coeff_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With exactly the preceding telescope, the conclusion is Module.Projective (MonoidAlgebra R Cp) (cyclicAction hpA h h0).asModule ↔ (Module.Projective R A ∧ IsUnit (h.coeff 1)). The proof handles arbitrary dimensions and nilpotents. Neither a field-base specialization nor a theorem that assumes coefficient projectivity replaces this statement.

The first necessity is coefficient projectivity. The public PGroupProjectiveNormRing.coefficient_projective_of_projective restricts group-algebra projectivity to R, using only the finite group. Constants A→P and constant-coefficient evaluation P→A are actual R-linear maps whose composite is the identity. Module.Projective.of_split therefore gives projectivity of A over R. No characteristic condition on R is involved.

For the second necessity, a narrow private bridge consumes the public PGroupProjectiveNormRing.orbit_section_of_projective. If v is an actual invariant vector, equivariance of its section S gives S(v)(g)=S(v)(1), by evaluating at the identity. The public orbit-sum identity then says norm(S(v)(1))=v. This is a direct finite-group consequence of the public section, not an invocation, export or copy of the owner-private norm-section theorem. The p-nilpotent group projectivity iff is not used over R.

Reindex the actual group sum by 0,...,p−1. The geometric identity over Fp[t] gives sum_(i<p)(1+t)^i=t^(p−1), with polynomial cancellation only over the field Fp. Evaluate at N to obtain rho.norm=N^(p−1), restricted to R. Because h=t*u and u(0)=beta, the difference h^(p−1)−beta^(p−1)*t^(p−1) is divisible by t^p. Evaluation at D gives N^(p−1)=beta^(p−1)*D^(p−1).

The iterated-derivative coefficient formula gives D^(p−1)q=C((p−1)!*q.coeff(p−1)): all positive output coefficients come from input indices at least p. Hence the exact unnormalised norm is rho.norm(q)=C(beta^(p−1)*(p−1)!*q.coeff(p−1)). This is the norm of the actual action, not a separately assumed operator.

Constants are fixed because h(D) kills them. Apply the finite-group bridge to C(1_A). If P is R[Cp]-projective there is q with norm(q)=C(1_A), hence beta^(p−1)*((p−1)!*q.coeff(p−1))=1_A. An explicit inverse of beta is beta^(p−2)*((p−1)!*q.coeff(p−1)). No cancellation in A or nonzero-ring argument is needed.

For sufficiency suppose beta is a unit and A is R-projective. The cyclic vector is the actual monomial v=X^(p−1). First form N^i v for 0≤i<p. Its coefficient above degree p−1−i is zero and its coefficient at that degree is delta_i=beta^i*(p−1)(p−2)...(p−i). These are coefficient bounds, not assertions of distinct polynomial degrees in the zero ring. The displayed coefficient is the leading or highest-degree term; all other terms have lower degree.

The source derives those bounds and coefficients by polynomial induction. A polynomial f(D) preserves an upper coefficient bound, and its coefficient at the bound is f(0) times the original coefficient. Write N=u(D)D: it lowers the bound by one, and multiplies the new top coefficient by beta times the previous degree. Recursion gives delta_0=1 and delta_(i+1)=beta*(p−1−i)*delta_i, without factorial division in A.

For 0<n<p the image of n in Fp is nonzero and therefore a unit. Mapping that unit to A proves each factor of delta_i is a unit, including in the zero ring. In the monomial basis, X^j↦N^(p−1−j)v is upper triangular with unit diagonal. Its determinant is a unit, so the public Matrix.toLinearEquiv supplies a bijective map. This is only a finite change of basis internal to a rank-p A-module; it is not a formalization of determinant geometry or a finite-dimensional hypothesis over R.

To identify the regular group module, send X^i to g^i in A[Cp], using the existing monoid-algebra basis reindexed by Fin p≃Cp. Compose with the public taylorLinearEquiv(-1), which sends X^i to (X−1)^i. This supplies the actual shifted basis (g−1)^i of A[Cp]. The A[Cp]-linear orbit map Phi(a)=a·v sends (g−1)^i to N^i v because g acts by 1+N. Comparing it with the triangular chain map and the reverse-index equivalence proves Phi bijective. Thus the private regularEquiv is an actual A[Cp]-module isomorphism A[Cp]≃P derived from v, not an assumed quotient presentation or a supplied cyclic basis.

The R[Cp]-equivariance is then proved for actual group generators and extended by monoid-algebra induction, using the same R-linear action. Finally Mathlib RingTheory.TensorProduct.MonoidAlgebra supplies the pushout equivalence R[Cp] tensor_R A ≃ A[Cp] over R[Cp]. The existing Module.Projective.tensorProduct instance makes this module projective when A is R-projective. It tensors actual split/free decompositions, so no flatness assumption is needed. Transport across the actual regular equivalence finishes sufficiency.

For p=2 the chain is X,NX, delta_1=beta, and the explicit inverse exponent p−2 is zero. If A is the zero ring, all coefficient bounds still hold, every diagonal entry is a unit in that ring, and both modules are zero. If R is the zero ring, a unital R-algebra A is also zero. The same statement includes infinite-dimensional and nonreduced A without a separate public telescope.

Take R=Z, A=Fp and h(t)=t. Then beta=1 is a unit, but Fp is not projective over Z: a projective module is a direct summand of a free abelian group, and is therefore torsion-free, whereas Fp is nonzero p-torsion. Thus P is not projective over Z[Cp]. This example also has p nonzero and nonnilpotent in R, so a p-nilpotent criterion over R would not apply.

For a second coefficient-projectivity obstruction, take R=Fp[epsilon]/(epsilon^2), A=R/(epsilon)=Fp, and h(t)=t. If R→A had an R-linear section, the lift x of 1 would satisfy epsilon*x=0 and x=1+a*epsilon. But epsilon*x=epsilon≠0, a contradiction. Therefore A is not R-projective even though beta=1 is a unit and R itself has characteristic p. By contrast A=R with h(t)=t gives the free rank-one regular module.

Independently, take R=Fp, A=Fp[s] and h(t)=s*t. Then A is R-projective because it is a vector space, but beta=s is a nonunit. The norm equation cannot hit C(1), so P is not R[Cp]-projective. These examples are ordinary mathematical explanations; this module does not add formalized example wrappers.

The necessity proof directly consumes the public PGroupProjectiveNormRing.coefficient_projective_of_projective and orbit_section_of_projective. It does not use that module's p-nilpotent projectivity criterion over R. Polynomial derivative, degreeLT, Taylor, triangular matrix, basis and monoid-algebra constructions come from Mathlib, as do Module.Projective.tensorProduct and Algebra.IsPushout.equiv. The new argument connects these interfaces to the actual derivative action and its two intrinsic obstructions.

The finite triangular matrix has size p over A. Its use does not impose finite generation or finite dimension on A over R. The norm and basis calculations hold with nilpotent coefficients and in the zero ring. This is an algebraic criterion for this specified action; it asserts neither a classification of all cyclic modules nor literature novelty. The examples above are ordinary mathematical explanations, not additional Lean declarations.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/TruncatedPolynomialCyclicCriterion.cyclicAction`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/TruncatedPolynomialCyclicCriterion.projective_iff_projective_coeff_and_isUnit_coeff_one`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing](PGroupProjectiveNormRing.md)
