# Fixed-output scalar PB and full vector Gram budgets

## Abstract

A scalar fixed-output PB family forces a transverse output identity. The representation has no total-response or separate P2 hypothesis. A concrete full M4 self-adjoint vector carrier, full-space positive vector-state transfer, and Hermitian row consumer are formalized; primitive spectral/support construction and the final raw-PB specialization remain open.

**Definition 1.1 (The original scalar budget).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall kappa \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \forall rho \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \forall t \in E,\; \forall k \in E,\; \forall g \in E,\; \forall x \in E,\; \forall phi \in \operatorname{LinearMap}\left(\mathbb{R}, E, \mathbb{R}\right),\; \operatorname{scalarPB}\left(J, kappa, rho, t, k, g, x, phi\right) \Leftrightarrow \operatorname{abs}\left(\operatorname{apply}\left(phi, \operatorname{smul}\left(-2, \operatorname{apply}\left(J, x, \operatorname{apply}\left(kappa, x\right) - k\right) + \operatorname{apply}\left(J, t, \operatorname{apply}\left(rho, x\right) + g\right)\right)\right)\right) \le \operatorname{sqrt}\left(\operatorname{gram}\left(J, phi, x + \operatorname{apply}\left(kappa, x\right) - k, t + \operatorname{apply}\left(rho, x\right) + g\right)\right) + \operatorname{sqrt}\left(\operatorname{gram}\left(J, phi, x - \left(\operatorname{apply}\left(kappa, x\right) - k\right), t - \left(\operatorname{apply}\left(rho, x\right) + g\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputGram.scalarPB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fixed t, k and g, kappa and rho are the known commutator and Jordan rows. At the original probe x, put h=kappa(x)-k and r=rho(x)+g. The same real-linear functional reads L=-2(J(x,h)+J(t,r)) and both budgets. The determinant is the uncentered real Gram determinant phi(J(U,U))phi(J(W,W))-phi(J(U,W)) squared. No unknown outer response is introduced.

**Definition 1.2 (A known spectral pair).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall kappa \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \forall rho \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \forall F \in \operatorname{SpectralPair}\left(J, kappa, rho\right),\; \left(\left(\left(\left(\operatorname{apply}\left(kappa, \operatorname{e}\left(F\right)\right) = \operatorname{smul}\left(\operatorname{lambda}\left(F\right), \operatorname{j}\left(F\right)\right) \land \operatorname{apply}\left(kappa, \operatorname{n}\left(F\right)\right) = 0\right) \land \operatorname{apply}\left(rho, \operatorname{e}\left(F\right)\right) = \operatorname{smul}\left(\operatorname{mu}\left(F\right), \operatorname{e}\left(F\right)\right)\right) \land \operatorname{apply}\left(rho, \operatorname{n}\left(F\right)\right) = \operatorname{smul}\left(\operatorname{mu}\left(F\right) + \operatorname{lambda}\left(F\right), \operatorname{n}\left(F\right)\right)\right) \land \operatorname{apply}\left(J, \operatorname{e}\left(F\right), \operatorname{j}\left(F\right)\right) = 0\right) \land \operatorname{apply}\left(J, \operatorname{n}\left(F\right), \operatorname{j}\left(F\right)\right) = \operatorname{j}\left(F\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputGram.SpectralPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pair consists of e, j, n and real mu, lambda satisfying the six displayed relations. In a matrix spectral pair n=2l, lambda is half the difference of the two actor eigenvalues, and mu is half their sum. These relations describe known products and commutators. They impose no condition on the unknown fixed output g.

**Definition 1.3 (A full Jordan representation).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall H \in Type,\; [\operatorname{NormedAddCommGroup}\left(H\right)][\operatorname{InnerProductSpace}\left(\mathbb{R}, H\right)]\forall R \in \operatorname{VectorModel}\left(H, J\right),\; \left(\forall a \in E,\; \operatorname{IsSymmetric}\left(\operatorname{op}\left(R, a\right)\right)\right) \land \left(\forall a \in E,\; \forall b \in E,\; \operatorname{op}\left(R, \operatorname{apply}\left(J, a, b\right)\right) = \operatorname{smul}\left(\operatorname{divide}\left(1, 2\right), \operatorname{comp}\left(\operatorname{op}\left(R, a\right), \operatorname{op}\left(R, b\right)\right) + \operatorname{comp}\left(\operatorname{op}\left(R, b\right), \operatorname{op}\left(R, a\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputGram.VectorModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real-linear operator map represents each label by a symmetric operator and represents the Jordan product by the symmetrized composition. H is the whole representation space. No restriction to the actor subspace is built into it, and no P2 field occurs.

**Definition 1.4 (One common vector reading).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall H \in Type,\; [\operatorname{NormedAddCommGroup}\left(H\right)][\operatorname{InnerProductSpace}\left(\mathbb{R}, H\right)]\forall R \in \operatorname{VectorModel}\left(H, J\right),\; \forall v \in H,\; \forall a \in E,\; \operatorname{vectorReading}\left(R, v, a\right) = \operatorname{inner}\left(v, \operatorname{op}\left(R, a, v\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputGram.vectorReading` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every vector v of the full H defines a real-linear reading. Symmetry and the represented Jordan law give vectorReading(v,J(a,b))=inner(op(a)v,op(b)v). The corresponding determinant is therefore a real Gram determinant, including degenerate and zero values.

**Definition 1.5 (The concrete M4 Jordan product).**

$$m4J = \operatorname{M4JordanProduct}\left(\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the real self-adjoint submodule of Matrix (Fin 4) (Fin 4) Complex, with literal symmetrized matrix multiplication.

**Theorem 1.6 (The concrete M4 vector model).**

$$m4VectorModel = \operatorname{VectorModel}\left(\operatorname{EuclideanSpace}\left(Complex, \operatorname{Fin}\left(4\right)\right), m4J\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4VectorModel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The operator is literal matrix action on the entire four-dimensional Euclidean space; the environment coordinate remains in the representation.

**Theorem 1.7 (Hermitian full-row reconstruction).**

$$\operatorname{HermitianRowReconstruction}\left(g, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4_full_row_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement on every off-diagonal entry of two Hermitian four-by-four matrices leaves a diagonal residual with real entries.

**Definition 1.8 (A full-space vector functional).**

$$m4VectorFunctional = \operatorname{VectorState}\left(v\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4VectorFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex-linear vector state is evaluated on the whole M4 carrier.

**Definition 1.9 (Real restriction of a complex functional).**

$$m4RealFunctional = \operatorname{RealRestriction}\left(phi\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4RealFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction to the self-adjoint real carrier takes the real part.

**Theorem 1.10 (Vector restriction identity).**

$$\operatorname{RestrictionEqualsVectorReading}\left(v, A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4RealFunctional_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For vector states, the restriction is exactly the existing vectorReading.

**Definition 1.11 (Full complex positive cone).**

$$m4PosSemidef = \operatorname{HermitianQuadraticNonnegative}\left(\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4PosSemidef` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive semidefiniteness is stated as Hermiticity plus nonnegative full-space quadratic forms, avoiding an order on Complex.

**Definition 1.12 (Full matrix positivity predicate).**

$$m4Positive = \operatorname{PositiveFunctionalOnM4}\left(\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4Positive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate quantifies over the complete positive cone.

**Theorem 1.13 (Vector states are positive).**

$$\operatorname{m4Positive}\left(\operatorname{m4VectorFunctional}\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4VectorFunctional_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic-form definition proves positivity of every full-space vector state.

**Definition 1.14 (Original actor support).**

$$m4ActorSupported = \operatorname{FourthRowAndColumnZero}\left(\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4ActorSupported` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actor-supported probes retain the original four-by-four carrier while forcing the fourth row and column to vanish.

**Theorem 1.15 (Positive-functional PB to vector PB).**

$$\operatorname{PositivePBTransfer}\left(hPB\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4_positive_pb_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the original scalar PB to a positive vector state supplies the full-space vector-reading hypothesis used by the Gram argument.

**Theorem 1.16 (The scalar PB transverse identity).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall H \in Type,\; [\operatorname{NormedAddCommGroup}\left(H\right)][\operatorname{InnerProductSpace}\left(\mathbb{R}, H\right)]\forall kappa \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \forall rho \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \forall F \in \operatorname{SpectralPair}\left(J, kappa, rho\right),\; \forall R \in \operatorname{VectorModel}\left(H, J\right),\; \forall t \in E,\; \forall k \in E,\; \forall g \in E,\; \forall xi \in H,\; \forall eta \in H,\; \forall nu \in H,\; \forall d \in \mathbb{R},\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\forall a \in E,\; \forall b \in E,\; \operatorname{apply}\left(J, a, b\right) = \operatorname{apply}\left(J, b, a\right)\right) \land \left(\forall v \in H,\; \operatorname{norm}\left(v\right) = 1 \Rightarrow \left(\forall tau \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \operatorname{scalarPB}\left(J, kappa, rho, t, k, g, \operatorname{smul}\left(tau, \operatorname{e}\left(F\right)\right) + \operatorname{smul}\left(alpha, \operatorname{n}\left(F\right)\right), \operatorname{vectorReading}\left(R, v\right)\right)\right)\right)\right) \land \left(d = 0 \Rightarrow False\right)\right) \land \left(\operatorname{lambda}\left(F\right) = 0 \Rightarrow False\right)\right) \land \operatorname{norm}\left(xi\right) = 1\right) \land \operatorname{norm}\left(eta\right) = 1\right) \land \operatorname{norm}\left(nu\right) = 1\right) \land \operatorname{op}\left(R, \operatorname{n}\left(F\right), xi\right) = 0\right) \land \operatorname{op}\left(R, \operatorname{n}\left(F\right), eta\right) = \operatorname{smul}\left(2, eta\right)\right) \land \operatorname{op}\left(R, \operatorname{j}\left(F\right), xi\right) = \operatorname{smul}\left(d, eta\right)\right) \land \operatorname{op}\left(R, \operatorname{e}\left(F\right), xi\right) = \operatorname{smul}\left(d, nu\right)\right) \land \operatorname{inner}\left(eta, nu\right) = 0\right) \land \operatorname{apply}\left(J, \operatorname{n}\left(F\right), \operatorname{smul}\left(\operatorname{mu}\left(F\right) + \operatorname{lambda}\left(F\right), \operatorname{apply}\left(J, \operatorname{n}\left(F\right), t\right)\right) - \operatorname{apply}\left(J, \operatorname{n}\left(F\right), k\right)\right) = \operatorname{smul}\left(\operatorname{mu}\left(F\right) + \operatorname{lambda}\left(F\right), \operatorname{apply}\left(J, \operatorname{n}\left(F\right), t\right)\right) - \operatorname{apply}\left(J, \operatorname{n}\left(F\right), k\right)\right) \Rightarrow \operatorname{inner}\left(nu, \operatorname{op}\left(R, g, xi\right)\right) = -\operatorname{inner}\left(eta, \operatorname{op}\left(R, \operatorname{smul}\left(\operatorname{mu}\left(F\right) + \operatorname{lambda}\left(F\right), \operatorname{apply}\left(J, \operatorname{n}\left(F\right), t\right)\right) - \operatorname{apply}\left(J, \operatorname{n}\left(F\right), k\right), xi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputGram.fixed_output_anchor_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a=mu+lambda, V=a J(n,t)-J(n,k) and Z=t+a k. Assume the original scalar PB for every unit vector reading on the full space and every probe T e+alpha n. The known support relation J(n,V)=V makes the V diagonal readings vanish on the zero and two eigenspaces of n. The relation J(n,j)=j gives the same fact for j. Both signs of nonzero lambda and d are retained.

First expand the original PB at T e+alpha n. The affine Gram shift and the leading-coefficient estimate from PBAffineFirstBudget give 2 abs(phi(lambda T j+V)) at most the sum of the square roots of Bphi(n,Z+g-lambda T e-a lambda T j) and Bphi(n,Z-g+lambda T e-a lambda T j). The expansion remains valid when a leading budget vanishes.

For unit xi, symmetry of n makes xi orthogonal to eta. Put b=1/sqrt(1+epsilon squared). The vector b(xi+epsilon eta) is unit. Its reading of lambda T j+V is exactly 2 epsilon b squared times lambda T d+inner(eta,op(V)xi). Its Gram determinant against n is exactly 4 epsilon squared b to the fourth times the squared norm of the real perpendicular projection of op(W)xi+epsilon op(W)eta. The square-root factor is exactly 2 epsilon/(1+epsilon squared). Cancel that common positive factor before taking epsilon down to zero with T fixed. The projected j term vanishes and the projected e term is d nu. Thus 2 abs(lambda T d+A) is at most norm(zplus-lambda T d nu)+norm(zminus+lambda T d nu), with A=inner(eta,op(V)xi) and zplus,zminus the projected readings of Z+g,Z-g.

The existing two-ended norm estimate now yields 2 A=inner(nu,zminus)-inner(nu,zplus). Orthogonality removes the projection and the common Z cancels, giving inner(nu,op(g)xi)=-A. All vector and operator expressions remain on the full H, including complementary environment components. The companion-axis theorem combines two such identities. A concrete four-dimensional diagonal-residual conclusion additionally requires complex polarization, the full-row reconstruction and their matrix specialization.

**Theorem 1.17 (The two-axis complex identity).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall H \in Type,\; [\operatorname{NormedAddCommGroup}\left(H\right)][\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)]\forall kappa \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \forall rho \in \operatorname{LinearMap}\left(\mathbb{R}, E, E\right),\; \forall F \in \operatorname{SpectralPair}\left(J, kappa, rho\right),\; \forall R \in \operatorname{VectorModel}\left(\operatorname{realUnderlying}\left(H\right), J\right),\; \forall t \in E,\; \forall k \in E,\; \forall g \in E,\; \forall iota \in \mathbb{C},\; \forall xi \in H,\; \forall eta \in H,\; \forall d \in \mathbb{R},\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\forall a \in E,\; \forall b \in E,\; \operatorname{apply}\left(J, a, b\right) = \operatorname{apply}\left(J, b, a\right)\right) \land \operatorname{apply}\left(kappa, \operatorname{j}\left(F\right)\right) = \operatorname{smul}\left(-\operatorname{lambda}\left(F\right), \operatorname{e}\left(F\right)\right)\right) \land \operatorname{apply}\left(rho, \operatorname{j}\left(F\right)\right) = \operatorname{smul}\left(\operatorname{mu}\left(F\right), \operatorname{j}\left(F\right)\right)\right) \land \operatorname{apply}\left(J, \operatorname{n}\left(F\right), \operatorname{e}\left(F\right)\right) = \operatorname{e}\left(F\right)\right) \land \left(\forall v \in H,\; \operatorname{norm}\left(v\right) = 1 \Rightarrow \left(\forall tau \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \operatorname{scalarPB}\left(J, kappa, rho, t, k, g, \operatorname{smul}\left(tau, \operatorname{e}\left(F\right)\right) + \operatorname{smul}\left(alpha, \operatorname{n}\left(F\right)\right), \operatorname{vectorReading}\left(R, v\right)\right) \land \operatorname{scalarPB}\left(J, kappa, rho, t, k, g, \operatorname{smul}\left(tau, \operatorname{j}\left(F\right)\right) + \operatorname{smul}\left(alpha, \operatorname{n}\left(F\right)\right), \operatorname{vectorReading}\left(R, v\right)\right)\right)\right)\right) \land \left(iota = i \lor iota = -i\right)\right) \land \left(d = 0 \Rightarrow False\right)\right) \land \left(\operatorname{lambda}\left(F\right) = 0 \Rightarrow False\right)\right) \land \operatorname{norm}\left(xi\right) = 1\right) \land \operatorname{norm}\left(eta\right) = 1\right) \land \operatorname{op}\left(R, \operatorname{n}\left(F\right), xi\right) = 0\right) \land \operatorname{op}\left(R, \operatorname{n}\left(F\right), eta\right) = \operatorname{smul}\left(2, eta\right)\right) \land \operatorname{op}\left(R, \operatorname{n}\left(F\right), \operatorname{smul}\left(-iota, eta\right)\right) = \operatorname{smul}\left(2, \operatorname{smul}\left(-iota, eta\right)\right)\right) \land \operatorname{op}\left(R, \operatorname{j}\left(F\right), xi\right) = \operatorname{smul}\left(d, eta\right)\right) \land \operatorname{op}\left(R, \operatorname{e}\left(F\right), xi\right) = \operatorname{smul}\left(d, \operatorname{smul}\left(-iota, eta\right)\right)\right) \land \operatorname{apply}\left(J, \operatorname{n}\left(F\right), \operatorname{smul}\left(\operatorname{mu}\left(F\right) + \operatorname{lambda}\left(F\right), \operatorname{apply}\left(J, \operatorname{n}\left(F\right), t\right)\right) - \operatorname{apply}\left(J, \operatorname{n}\left(F\right), k\right)\right) = \operatorname{smul}\left(\operatorname{mu}\left(F\right) + \operatorname{lambda}\left(F\right), \operatorname{apply}\left(J, \operatorname{n}\left(F\right), t\right)\right) - \operatorname{apply}\left(J, \operatorname{n}\left(F\right), k\right)\right) \Rightarrow \operatorname{complexInner}\left(eta, \operatorname{op}\left(R, g, xi\right)\right) = iota \cdot \operatorname{complexInner}\left(eta, \operatorname{op}\left(R, \operatorname{smul}\left(\operatorname{mu}\left(F\right) + \operatorname{lambda}\left(F\right), \operatorname{apply}\left(J, \operatorname{n}\left(F\right), t\right)\right) - \operatorname{apply}\left(J, \operatorname{n}\left(F\right), k\right), xi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputGram.fixed_output_two_axis_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same scalar PB for both probe families T e+alpha n and T j+alpha n. The additional known relations are kappa(j)=-lambda e, rho(j)=mu j and J(n,e)=e. The second spectral pair is constructed as (eprime,jprime,n)=(j,-e,n), keeping the same mu and lambda. Its vectors are etaprime=-nu and nuprime=eta, where nu=-iota eta and iota is either i or -i. Both vectors remain in the two eigenspace of n.

The first real identity gives Re inner(nu,g xi)=-Re inner(eta,V xi). The constructed companion gives Re inner(eta,g xi)=Re inner(nu,V xi). The complex inner product is conjugate-linear in its first entry. Since inner(nu,z)=iota inner(eta,z), the two real readings determine the real and imaginary parts of inner(eta,g xi)=iota inner(eta,V xi), for either orientation. This is a pointwise full-space identity under the displayed representation and spectral hypotheses. The concrete M4 carrier and positive-functional transfer are formalized separately. Primitive spectral/support construction, the zero-d branch, homogeneous extension and complete-row reconstruction remain additional obligations.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.SpectralPair`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.VectorModel`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.fixed_output_anchor_identity`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.fixed_output_two_axis_identity`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4ActorSupported`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4J`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4PosSemidef`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4Positive`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4RealFunctional`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4RealFunctional_vector`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4VectorFunctional`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4VectorFunctional_positive`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4VectorModel`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4_full_row_reconstruction`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.m4_positive_pb_transfer`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.scalarPB`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputGram.vectorReading`
- Dependency: [D5/S3/Quantum/Algebra/PBAffineFirstBudget](PBAffineFirstBudget.md)
