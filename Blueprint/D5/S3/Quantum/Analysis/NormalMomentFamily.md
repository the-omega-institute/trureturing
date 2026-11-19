# Compact full continuous-moment family

## Abstract

The actual family of positive continuous-moment maps is compact in all weak-star evaluation coordinates. Its scalar Riesz measures vary weakly continuously, and every family point has an entire complex L1 normal posterior realization on an arbitrary concrete von Neumann algebra.

**Definition 1.1 (The posterior coordinate).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.posterior`

*Formalization.* `D5/S3/Quantum/Analysis/NormalMomentFamily.posterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Interval is Set.Icc (0 : R) 1 with its actual compact metric Borel structure. posterior is the continuous complex function t maps to ofReal(t.val). Both posterior and 1-posterior are pointwise nonnegative, including the endpoints.

**Definition 1.2 (All weak-star coordinates).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.Ambient`

*Formalization.* `D5/S3/Quantum/Analysis/NormalMomentFamily.Ambient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex C-star algebra A, Ambient A is the product C(Interval,C) -> WeakDual C A. Its product topology uses every complex continuous g and, inside each weak-star dual coordinate, evaluation at every a in A. No finite coordinate set, countable dense set, sequential topology, separability hypothesis or assumed generic compact parameter space replaces this product.

**Definition 1.3 (The closed compatibility constraints).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.Compatible`

*Formalization.* `D5/S3/Quantum/Analysis/NormalMomentFamily.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For rho and sigma in StrongDual C A, Compatible rho sigma F means F(g+h)(a)=F(g)(a)+F(h)(a), F(z*g)(a)=z F(g)(a) for every g,h,z,a; F(g)(a)>=0 whenever g is pointwise nonnegative and a>=0; F(1)(a)=(rho+sigma)(a); and F(posterior)(a)=rho(a). These are all the definition data. Compactness, normality, norm bounds, scalar measures and L1 realizations are conclusions. Every such constraint is closed because all its scalar evaluations are continuous.

**Definition 1.4 (The actual moment family).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.Family`

*Formalization.* `D5/S3/Quantum/Analysis/NormalMomentFamily.Family` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Family rho sigma is exactly the subtype of Ambient A satisfying Compatible rho sigma, with the induced product weak-star topology. Complex linearity is recovered by linearMap, rather than assumed compactness or normality being stored in a structure.

**Definition 1.5 (Every genuine moment map belongs).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.ofLinearMap`

*Formalization.* `D5/S3/Quantum/Analysis/NormalMomentFamily.ofLinearMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every actual complex-linear J from C(Interval,C) to StrongDual C A that is positive on pointwise positive functions, satisfies J(1)=rho+sigma and J(posterior)=rho determines a point of Family rho sigma by its weak-star coordinates. No boundedness, normality or extra equation is required by this constructor. It is consumed by the actual endpoint witness g maps to g(1)rho+g(0)sigma. linearMap recovers precisely these continuous-dual coordinates.

**Definition 1.6 (Reconstructed genuine complex-linear map).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.linearMap`

*Formalization.* `D5/S3/Quantum/Analysis/NormalMomentFamily.linearMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every F in Family rho sigma, linearMap F is a genuine C-linear map from C(Interval,C) to StrongDual C A, obtained by applying WeakDual.toStrongDual in every coordinate. Its linearity follows by extensionality from the all-a compatibility equations. It is positive, maps 1 to rho+sigma and posterior to rho, and hence maps 1-posterior to sigma.

**Theorem 1.7 (Exact unit moment).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.unit_value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NormalMomentFamily.unit_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual Family rho sigma point F, linearMap F 1=rho+sigma. This is the existing exact compatibility equation, exposed for the consumed affine-cost computation.

**Theorem 1.8 (Exact posterior moment).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.posterior_value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NormalMomentFamily.posterior_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual Family rho sigma point F, linearMap F posterior=rho. Together with the unit equation this gives linearMap F (1-posterior)=sigma, consumed in GeneralConvexReverseTestAttainment.familyCost_eq_affine.

**Theorem 1.9 (Every exact scalar complex integral).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.integral_complex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NormalMomentFamily.integral_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Family rho sigma point F and continuous complex g, linearMap F g 1 equals integral g against scalarMeasure F. The original scalar Riesz proof is reused directly by posteriorFamily_scalarMeasure and the exact affine objective computation, without duplicating its real/imaginary decomposition.

**Definition 1.10 (Scalar finite regular Riesz measure).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.scalarMeasure`

*Formalization.* `D5/S3/Quantum/Analysis/NormalMomentFamily.scalarMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each F, restrict g maps to linearMap(F)(g)(1) to real continuous functions, and take its real part. On compact Interval this is an actual positive real linear functional on compactly supported continuous functions. scalarMeasure F is RealRMK.rieszMeasure of that functional. Mathlib supplies finiteness and regularity. Positivity makes the imaginary part vanish on every real continuous function, by decomposing that function into its positive and negative parts. RealRMK.integral_rieszMeasure and real/imaginary decomposition therefore prove the exact complex identity linearMap(F)(g)(1)=integral g d(scalarMeasure F) for every complex continuous g. The total mass is ENNReal.ofReal(Re((rho+sigma)(1))). No vector measure, vector density or RNP hypothesis is used.

**Definition 1.11 (The weakly continuous finite-measure map).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.finiteMeasure`

*Formalization.* `D5/S3/Quantum/Analysis/NormalMomentFamily.finiteMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

finiteMeasure F packages scalarMeasure F as Mathlib's FiniteMeasure Interval with its genuine topology of weak convergence. FiniteMeasure.continuous_iff_forall_continuousMap_continuous_integral reduces continuity to all real continuous test functions. Their integrals equal real parts of the corresponding weak-star coordinate evaluated at 1, which are continuous in F.

**Theorem 1.12 (Compactness, Riesz measures and whole-L1 realization).**

Lean statement: `D5/S3/Quantum/Analysis/NormalMomentFamily.compact_normal_posterior_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NormalMomentFamily.compact_normal_posterior_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H is any complete complex inner product space, with no dimension or separability restriction; M is an actual VonNeumannAlgebra H. Its actual closed star-subalgebra carrier, and inherited operator order with StarOrderedRing compatibility, use VonNeumannNormalL1.closedCarrier. rho and sigma are actual positive continuous complex-linear functionals on this carrier. Their sum S is order-normal along every nonempty upward-directed positive set with an actual least upper bound, in the exact uniform-tail sense of NormalFunctionals.IsOrderNormal. There is no faithfulness, nonzero mass, finite cost or normalized-state premise.

The actual Compatible subset of the all-coordinate Ambient product is compact and its Family subtype is nonempty. A witness is g maps to g(1)rho+g(0)sigma. For each coordinate g, decomposition into positive and negative real and imaginary parts, the reused positive-functional norm=mass identity, and domination of the sum of each pair by ||g|| times the unit give ||J(g)||<=2||g|| Re(S(1)). Thus every compatible point lies in the product of the actual weak-star compact balls with these radii. The compatibility conditions are closed; Banach-Alaoglu and unrestricted Tychonoff prove compactness of this exact subset.

The map F maps to finiteMeasure F is weakly continuous and has compact range. Every scalarMeasure F is regular, has total mass ENNReal.ofReal(Re(S(1))), and satisfies J(g)(1)=integral g dnu for every continuous complex g. These conclusions are derived, rather than supplied as family fields.

For every family point F, there exists a continuous complex-linear Gamma from the ENTIRE complex L1(scalarMeasure F) to StrongDual C M.toStarSubalgebra. It agrees exactly with linearMap F on every continuous complex g; every Gamma(h) is all-directed order-normal; for every almost-everywhere nonnegative h and positive a, Gamma(h)(a)>=0; for every complex h, Gamma(h)(1)=integral h dnu; and its operator norm is at most one. Both exact posterior identities hold: Gamma(toLp posterior)=rho and Gamma(toLp(1-posterior))=sigma. The proof applies exists_normal_L1_extension with the actual Riesz measure and derived mass identity; normality of J(1)=S suffices. The zero pair and zero measure remain in scope.

The content consists of the constructed full coordinate family, its derived uniform coordinate bound and compactness, actual scalar Riesz measures with exact complex mass identity and weak continuity, and their connected whole-L1 realizations. The argument reuses Mathlib's Banach-Alaoglu, Tychonoff and real Riesz theorems and the existing normal L1 extension, rather than rebuilding them. It claims no global literature novelty, chosen-predual identification, ultraweak equivalence or vector-valued Radon-Nikodym theorem.

This module supplies compactness and posterior realization. The consuming GeneralConvexReverseTestAttainment module addresses exact normalization and pushforward comparison for every original sigma-finite source and its entire complex L1 map, fixed-universe cost-set equality and endpoint-complete extended minimization. Those conclusions are not implicit premises of the compact family.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.Ambient`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.Compatible`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.Family`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.compact_normal_posterior_family`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.finiteMeasure`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.integral_complex`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.linearMap`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.ofLinearMap`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.posterior`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.posterior_value`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.scalarMeasure`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalMomentFamily.unit_value`
- Dependency: [D5/S3/Quantum/Analysis/VonNeumannNormalL1](VonNeumannNormalL1.md)
