# Complete Earlier Support and the Cubic Unit

## Abstract

The primary and conjugate factors of earlier golden cubic blocks, together with two and three, generate a full-degree Galois cubic radical field in which the cubic root of unity remains noncube.

**Theorem 1.1 (Full Galois degree, cubic coordinates and unit obstruction).**

$$\begin{aligned}[M_{j}:E] = 3^{2\Vert S_{j} \Vert+2},\\\forall x \in M_{j}, x^{3} \neq zeta_{3},\\\operatorname{Gal}\left(M_{j}, E\right) \sim \left(C_{3}\right)^{2\Vert S_{j} \Vert+2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GoldenCubicCompleteUnitObstruction.golden_cubic_complete_degree_and_unit_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let j be a natural number and E the cubic cyclotomic field over the rationals. In an algebraic closure of E, collect the rational primes in blocks B_i = L_(3^i)^2 + 3 for indices one less than or equal to i less than j. Call this finite union S_j. There is one choice of primary Eisenstein factors pi_p for the whole union, with prime principal ideal, norm p, pi_p congruent to one modulo three, and p congruent to one modulo three. Each factor is coprime to its conjugate, and distinct rational primes give coprime factors in all four primary and conjugate combinations.

This same choice gives the oriented product of every earlier block. The exponent at p is its original Fibonacci depth, the p-adic valuation of F_(rho(p)), where rho(p) is the entry rank. Choose cube roots of each primary factor and each conjugate factor and of two and three. Let M_j be their common generated field over E. Its degree is three to the power two times the cardinality of S_j plus two, and no element of M_j cubes to the chosen primitive cube root of unity in E. The field is Galois over E. Its automorphisms are independent rotations of these chosen cubic roots, with one coordinate modulo three for each root. The support is empty for j at most one; the two rational radicands are still present.

Principal prime-ideal valuations distinguish the primary and conjugate radicands. The valuations above two and three distinguish the remaining radicands. Each diagonal integer valuation is nonzero modulo three, every off-diagonal valuation is zero, and all rows vanish on the cubic unit. A cube equation in the unit times the radicand span forces every radicand exponent to be divisible by three. Removing their cubes would make the unit a cube in E, which would put a primitive ninth root of unity in E. Saturated base-field tests and cubic descent propagate this obstruction through the entire tower while proving each stage has degree three.

## References

- Truth anchor: `D5/S3/Factorization/Galois/GoldenCubicCompleteUnitObstruction.golden_cubic_complete_degree_and_unit_obstruction`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockNativePowerPeriods](../../Arith/Primes/GoldenCubicBlockNativePowerPeriods.md)
- Dependency: [D5/S3/Factorization/Galois/CubicRadicalTowerDegree](CubicRadicalTowerDegree.md)
- Dependency: [D5/S3/Factorization/Galois/GoldenCubicBlockCommonDiscriminants](GoldenCubicBlockCommonDiscriminants.md)
- Dependency: [D5/S3/Factorization/Galois/GoldenCubicBlockKummerTower](GoldenCubicBlockKummerTower.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/EisensteinCyclotomicBridge](../QuadraticIdeals/EisensteinCyclotomicBridge.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrimaryProduct](../QuadraticIdeals/GoldenCubicPrimaryProduct.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/InertEisensteinFrobenius](../QuadraticIdeals/InertEisensteinFrobenius.md)
