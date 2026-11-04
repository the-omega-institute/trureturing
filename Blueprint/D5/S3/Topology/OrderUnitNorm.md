# The original order-unit norm

## Abstract

A closed salient cone and its specified interior unit determine the original order norm, positive-functional mass bounds, and exact bounds for the original linear operator.

Let E be any finite-dimensional real normed vector space. Its auxiliary norm supplies the usual topology only. The data A consist of a convex cone C containing zero, a closedness proof, salience, and a specified vector u in its interior. Salience means that a vector and its negative can both belong to C only when the vector vanishes. No inner product, lattice, Jordan product, self-duality or nonzero-dimension assumption is used.

Put B equal to the vectors v for which u-v and u+v belong to C. For each v, let S(v) be the nonnegative real radii r for which r u-v and r u+v belong to C, and let n(v) be inf S(v). In particular, zero is retained among the radii. The order relation is exactly w-v in C.

**Theorem 1.1 (The norm axioms follow from the original cone).**

$$\forall E \in Types,\; RealNormedVectorSpace\left(E\right) \Rightarrow \left(\forall A \in ConeUnitData\left(E\right),\; \forall v \in E,\; 0 \le n\left(v\right) \land \left(\left(n\left(v\right) = 0 \Leftrightarrow v = 0\right) \land \left(\left(\forall a \in R,\; n\left(smul\left(a, v\right)\right) = abs\left(a\right) \cdot n\left(v\right)\right) \land \left(\forall w \in E,\; n\left(v + w\right) \le n\left(v\right) + n\left(w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrderUnitNorm.norm_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The symbols R and Types denote the real scalars and the type universe. ConeUnitData denotes precisely the original cone and unit data stated above. The displayed norm laws apply to the copy of E with norm n; this first assertion does not require finite dimension. They are proved rather than supplied as an extra hypothesis. The interior-unit assumption makes B a neighborhood of zero and hence absorbent. Each S(v) is nonempty, closed and bounded below by zero, so its infimum is attained.

The symmetric interval is convex and balanced. Its gauge equals n exactly: every positive gauge radius is an order radius, and every radius just above the attained order radius is a positive gauge radius. This includes v=0, where S(0) contains its infimum zero although the gauge uses strictly positive radii. Mathlib's gaugeSeminorm supplies the seminorm laws. At n(v)=0 the attained inequalities put v and -v in C, so salience supplies definiteness.

**Theorem 1.2 (Positive functionals and the same original operator).**

$$\forall E \in Types,\; FiniteDimensionalRealNormedSpace\left(E\right) \Rightarrow \left(\forall A \in ConeUnitData\left(E\right),\; \left(\forall v \in E,\; n\left(v\right) = gauge\left(B, v\right) \land \left(mem\left(n\left(v\right), S\left(v\right)\right) \land \left(norm\left(j\left(v\right)\right) = n\left(v\right) \land \left(norm\left(j\left(v\right)\right) \le 1 \Leftrightarrow mem\left(v, B\right)\right)\right)\right)\right) \land \left(Complete\left(Eu\right) \land \left(Continuous\left(j\right) \land \left(Continuous\left(inverse\left(j\right)\right) \land \left(\left(\forall beta \in PositiveDual,\; \left(\forall v \in E,\; abs\left(beta\left(v\right)\right) \le beta\left(u\right) \cdot n\left(v\right)\right) \land \left(\left(beta\left(u\right) = 0 \Rightarrow beta = 0\right) \land norm\left(transport\left(beta\right)\right) = beta\left(u\right)\right)\right) \land \left(\left(\forall H \in RealEndomorphisms\left(E\right),\; \left(\forall v \in E,\; Hu\left(j\left(v\right)\right) = j\left(H\left(v\right)\right) \land Hu\left(Hu\left(j\left(v\right)\right)\right) = j\left(H\left(H\left(v\right)\right)\right)\right) \land \left(\left(K = norm\left(square\left(Hu\right)\right) \land \left(K = inf\left(Set\left(c, 0 \le c \land \left(\forall v \in E,\; n\left(H\left(H\left(v\right)\right)\right) \le c \cdot n\left(v\right)\right)\right)\right) \land IsLeast\left(Set\left(c, 0 \le c \land \left(\forall v \in E,\; n\left(H\left(H\left(v\right)\right)\right) \le c \cdot n\left(v\right)\right)\right), K\right)\right)\right) \land \left(\left(\forall t \in R,\; \forall v \in E,\; exp\left(smul\left(t, Hu\right)\right)\left(j\left(v\right)\right) = j\left(exp\left(smul\left(t, H\right)\right)\left(v\right)\right)\right) \land \left(\left(H\left(u\right) = 0 \Rightarrow \left(\forall t \in R,\; exp\left(smul\left(t, H\right)\right)\left(u\right) = u\right)\right) \land \left(\left(PositiveUnitalAtEveryRealTime\left(H, C, u\right) \Rightarrow \left(\left(\forall t \in R,\; \forall v \in E,\; n\left(exp\left(smul\left(t, H\right)\right)\left(v\right)\right) = n\left(v\right)\right) \land \left(H\left(u\right) = 0 \Rightarrow \left(\left(\forall beta \in PositiveDual,\; \forall x \in Effects,\; \forall t \in R,\; abs\left(beta\left(exp\left(smul\left(t, H\right)\right)\left(H\left(H\left(x\right)\right)\right)\right)\right) \le \frac{beta\left(u\right) \cdot K}{2}\right) \land \left(\forall beta \in PositiveDual,\; \forall x \in Effects,\; square\left(abs\left(beta\left(H\left(x\right)\right)\right)\right) \le K \cdot beta\left(x\right) \cdot beta\left(u\right)\right)\right)\right)\right)\right) \land \left(\forall q \in R,\; \forall P \in Subsets\left(PositiveDual\right),\; \left(0 \le q \land \left(Closure\left(Cone\left(P\right)\right) = PositiveDual \land \left(\forall alpha \in P,\; Certificate\left(H, q, alpha\right)\right)\right)\right) \Rightarrow \left(\left(\forall beta \in PositiveDual,\; Certificate\left(H, q, beta\right)\right) \land \left(\left(\forall beta \in PositiveDual,\; \forall r \in PositiveReals,\; \forall y \in C,\; mem\left(sub\left(smul\left(r, u\right), y\right), C\right) \Rightarrow square\left(abs\left(beta\left(H\left(y\right)\right)\right)\right) \le q \cdot r \cdot beta\left(y\right) \cdot beta\left(u\right)\right) \land \left(\forall beta \in PositiveDual,\; \forall y \in C,\; beta\left(y\right) = 0 \Rightarrow beta\left(H\left(y\right)\right) = 0\right)\right)\right)\right)\right)\right)\right)\right)\right) \land PositiveUnitalInverseIsometry\left(C, u, n\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrderUnitNorm.original_order_unit_norm_interface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PositiveDual denotes all original real-linear functionals nonnegative on C, and Effects denotes all x with x and u-x in C. RealEndomorphisms denotes all original real-linear maps E to E. The notation K abbreviates the norm of the square of the transported operator, and IsLeast includes membership in the displayed bound set as well as its minimality. Here j is the canonical linear wrapping map to the copy E_u, and H_u is defined solely by H_u(j(v))=j(H(v)). The constructed copy is complete. The wrapping map and its inverse are continuous in the original finite-dimensional topology; no equality with the auxiliary ambient norm is asserted.

For every positive original real-linear functional beta, its evaluation is bounded by its mass beta(u) times n(v). Applying beta to the attained endpoint inequalities proves this without dividing by its mass. Thus mass zero forces the original functional to vanish. The operator norm of beta transported to E_u is exactly beta(u), including in dimension zero.

The square H_u squared acts on j(v) as j(H(H(v))). Its operator norm is exactly the infimum of all nonnegative c satisfying n(H(H(v))) at most c n(v) for every original v. This infimum is attained. Neither an ambient operator bound nor the square of the norm of H is substituted for this number.

A positive unital linear map contracts n. A linear equivalence whose inverse is also positive is an isometry; positivity and unitality alone do not imply isometry. Applying this conclusion to exp(tH) uses both the assumed positivity at t and at -t. Independently, H(u)=0 makes the derivative of exp(tH)u vanish on the whole real line, so the actual exponential fixes u. Conjugation by j carries the actual exponential to exp(tH_u).

Assume that every original exp(tH) is positive and fixes u. Its order norm is then preserved for every real t. If the separately supplied condition H(u)=0 also holds, an effect x in C with u-x in C has centered vector z=x-u/2 of order norm at most one half, and H(H(x))=H(H(z)). Positive-functional domination and the exact square-operator bound give the displayed all-time centered-orbit estimate.

The actual scalar orbit f(t)=beta(exp(tH)x) is twice continuously differentiable, with first derivative beta(exp(tH)Hx) and second derivative beta(exp(tH)H(Hx)). Taylor's theorem on the unoriented interval from 0 to any real s gives f(s) at most f(0)+s f'(0)+M s squared divided by two, where M=beta(u)K/2. Positivity makes this quadratic nonnegative on the entire real line. The existing quadratic discriminant theorem then gives f'(0) squared at most 2M f(0), including M=0. This proves the reverse certificate with exactly K=the operator norm of H_u squared, without division by mass or curvature. The positive-generator criterion remains separate; no full quantitative generator equivalence or optimality of K is asserted here.

For an arbitrary original preparation set P contained in the full positive dual, assume its finite nonnegative cone has closure equal to that dual. Finite-dimensionality identifies every original linear functional with its unique continuous-linear version. The closure is the usual topology on the original dual, not a replacement preparation set. A certificate with one fixed nonnegative q on P extends with exactly the same q to the full dual. Mathlib's weighted finite Cauchy-Schwarz inequality applies directly to signed evaluations with nonnegative weights and masses, including the empty sum. For each fixed effect the squared inequality describes a closed set of functionals, so it persists under closure.

For r strictly positive and y and r u-y in C, apply the effect certificate to y/r and use the original linear maps. Multiplication by r squared leaves exactly q r beta(y) beta(u). There is no positive lower mass bound or division by mass. The attained order-radius bound supplies a finite strictly positive r for every positive y. Therefore beta(y)=0 forces beta(Hy)=0 for every positive original beta. The symbols Certificate, Cone and Closure in the display mean precisely this effect certificate, finite nonnegative cone and ordinary dual-topology closure.

Order-unit norm and positive-functional mass facts are classical; the present concrete interface retains the original cone, unit, functional and linear action in one construction. It asserts no literature priority or physical realization of the mathematical exponential.

## References

- Truth anchor: `D5/S3/Topology/OrderUnitNorm.norm_core`
- Truth anchor: `D5/S3/Topology/OrderUnitNorm.original_order_unit_norm_interface`
