# Physical Gram Necessity

## Abstract

Actual fixed-isometry residuals have a full occupation Gram formula and a physical memory lower bound.

The alphabet sigma is finite and nonempty. Capacities a(i) are arbitrary natural numbers. H is an arbitrary finite-dimensional complex inner-product space. Box(a) consists of occupations r with r(i) in Fin(a(i)+1); |r| is the sum of their values and M(r)=|r|!/product(i,r(i)!). All square roots below are nonnegative real square roots, included in Complex. FixedIsometry(H,sigma) denotes a total complex linear isometry from H to EuclideanSpace(Complex,sigma) tensor H.

**Theorem 1.1 (Evolution along every admissible horizon).**

$$\forall sigma: Type, \operatorname{Fintype}\left(sigma\right), \operatorname{DecidableEq}\left(sigma\right), \operatorname{Nonempty}\left(sigma\right),\ \forall H: Type, \operatorname{NormedAddCommGroup}\left(H\right), \operatorname{InnerProductSpace}\left(Complex, H\right), \operatorname{FiniteDimensional}\left(Complex, H\right),\ \forall a: sigma \to Nat,\ \forall V: \operatorname{FixedIsometry}\left(H, sigma\right),\ \forall phi: \operatorname{Box}\left(a\right) \to H,\ \operatorname{Step}\left(a, V, phi\right) \implies\ \operatorname{ResidualEvolution}\left(a, V, phi\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.residual_word_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the one-letter Step law for the same V, guarded by r nonzero. For every r and every word w with length at most |r|, wordOp(V,w,phi(r)) equals sqrt(M(r-counts(w))/M(r)) times phi(r-counts(w)) if every letter count is at most r(i), and zero otherwise. Subtraction is coordinatewise natural subtraction. Induction on w uses the multinomial erasure recurrence to telescope the legal coefficients; the first illegal letter and the illegal-tail case both give zero. The empty word is included, without imposing a transition at r=0.

**Theorem 1.2 (The complete residual Gram data).**

$$\forall sigma: Type, \operatorname{Fintype}\left(sigma\right), \operatorname{DecidableEq}\left(sigma\right), \operatorname{Nonempty}\left(sigma\right),\ \forall H: Type, \operatorname{NormedAddCommGroup}\left(H\right), \operatorname{InnerProductSpace}\left(Complex, H\right), \operatorname{FiniteDimensional}\left(Complex, H\right),\ \forall a: sigma \to Nat,\ \forall V: \operatorname{FixedIsometry}\left(H, sigma\right),\ \forall f: H,\ \forall phi: \operatorname{Box}\left(a\right) \to H,\ {\forall r: \operatorname{Box}\left(a\right),\ \operatorname{norm}\left(\operatorname{phi}\left(r\right)\right) = 1} \land \operatorname{phi}\left(0\right) = f \land \operatorname{Step}\left(a, V, phi\right) \implies\ \operatorname{NormalizedGram}\left(a, f, phi\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.stationary_normalized_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G(r,s)=inner(phi(r),phi(s)) and z(d)=inner(phi(d),f), with unit phi and phi(0)=f. When s<=r coordinatewise, G(r,s)=sqrt(M(s)M(r-s)/M(r)) z(r-s). When r<=s, the reverse formula is sqrt(M(r)M(s-r)/M(s)) conjugate(z(s-r)). Incomparable indices have zero inner product. To compute the first formula, continue both vectors for the shorter horizon |s|. The word law leaves exactly the M(s) words of occupation s; their equal contributions have coefficient sqrt(M(r-s)/M(r)) sqrt(1/M(s)). Summation gives the stated coefficient and retains the phase in z. Conjugate symmetry handles the opposite order of horizons.

The same conclusion gives G Hermitian and positive semidefinite, G(r,r)=1, z(0)=1, and rank G<=finrank(Complex,H). Define D(r,r)=sqrt(M(r)), Dinv(r,r)=1/sqrt(M(r)), and B=DGD. Positivity of M(r) gives both inverse identities. B is exactly the Gram matrix of sqrt(M(r)) times phi(r), is positive semidefinite, has B(0,0)=1, and has the same rank as G.

For nonzero r and nonzero s, inner-product preservation by the same V gives B(r,s)=sum(i,B(r-e(i),s-e(i))), retaining a summand only when both r(i) and s(i) are positive. The scaled Step coefficient follows from |r| M(r-e(i))=r(i)M(r). The stationary Gram rank theorem applied to this actual B gives rank G>=product(i,a(i)+1)-max(i,a(i)), with natural subtraction. Its conditional-kernel, polynomial-coordinate, rigidity and nullity arguments remain in that reused theorem. No recurrence at a zero residual is required.

For all-zero capacities, Box(a) has one element, G is the identity, rank G=1, and finrank(Complex,H)>=1. This is a boundary clause of the universal result.

**Theorem 1.3 (The actual preparation and its dimension bound).**

$$\forall sigma: Type, \operatorname{Fintype}\left(sigma\right), \operatorname{DecidableEq}\left(sigma\right), \operatorname{Nonempty}\left(sigma\right),\ \forall H: Type, \operatorname{NormedAddCommGroup}\left(H\right), \operatorname{InnerProductSpace}\left(Complex, H\right), \operatorname{FiniteDimensional}\left(Complex, H\right),\ \forall a: sigma \to Nat,\ \forall P: \operatorname{PhysicalPreparation}\left(a, H\right),\ \operatorname{NormalizedResiduals}\left(a, \operatorname{V}\left(P\right), \operatorname{initial}\left(P\right), \operatorname{final}\left(P\right), \operatorname{residual}\left(a, \operatorname{V}\left(P\right), \operatorname{initial}\left(P\right)\right)\right) \land\ \operatorname{ResidualEvolution}\left(a, \operatorname{V}\left(P\right), \operatorname{residual}\left(a, \operatorname{V}\left(P\right), \operatorname{initial}\left(P\right)\right)\right) \land\ \operatorname{NormalizedGram}\left(a, \operatorname{final}\left(P\right), \operatorname{residual}\left(a, \operatorname{V}\left(P\right), \operatorname{initial}\left(P\right)\right)\right) \land\ \operatorname{NatSub}\left(\prod_{i \in sigma} (\operatorname{a}\left(i\right) + 1), \operatorname{FinsetSup}\left(\operatorname{univ}\left(sigma\right), a\right)\right) \leq \operatorname{finrank}\left(Complex, H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.physical_gram_from_exact_preparation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given a PhysicalPreparation P, set phi=residual(a,P.V,P.initial). The result returns four fields: the actual NormalizedResiduals including all prefix equalities, universal ResidualEvolution, the full NormalizedGram, and product(i,a(i)+1)-max(i,a(i))<=finrank(Complex,H). The Gram calculation uses the Step and phase data extracted from P, so its vectors belong to the actual physical memory. Neither residual equations nor Gram equations are added as hypotheses on P.

For (4,2,1,1), the stationary lower bound is (5*3*2*2)-4=56. The corresponding exact target has 840 words of amplitude 1/sqrt(840). Attainment is a separate construction; the time-dependent minimum 12 concerns a different control model.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.physical_gram_from_exact_preparation`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.residual_word_formula`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.stationary_normalized_gram`
- Dependency: [D5/S3/Quantum/Algebra/StationaryGramRank](../Algebra/StationaryGramRank.md)
- Dependency: [D5/S3/Quantum/StationaryPreparation/PhysicalResiduals](PhysicalResiduals.md)
