# The Kagey--Keehn Rectangular-Torus GCD Descent

## Abstract

A decorated plane lift fixed by a translated transposing right action descends to the square torus whose side is the gcd of the source periods.

**Theorem 1.1 (Every four-way transposing fixed plane descends to a gcd square).**

Lean statement: `D5/S3/Combinatorics/TorusTilings/KageyKeehnRectangularTorus.rectangular_torus_gcd_descent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TorusTilings/KageyKeehnRectangularTorus.rectangular_torus_gcd_descent` (`✓ std3`). ∎

*Resolves.* `Problems/kagey-keehn-2023-rectangular-torus` (proved) by `D5/S3/Combinatorics/TorusTilings/KageyKeehnRectangularTorus.rectangular_torus_gcd_descent`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kagey-keehn-2023-rectangular-torus","declaration_gid":"D5/S3/Combinatorics/TorusTilings/KageyKeehnRectangularTorus.rectangular_torus_gcd_descent","resolution_kind":"proved"} -->

*Citation.* Peter Kagey; William Keehn (2023). *Counting tilings of the n x m grid, cylinder, and torus*. URL: <https://arxiv.org/abs/2311.13072v1>.

*Commentary.*

For arbitrary positive natural dimensions n and m, let T be the actual right R-set of decorated tile designs, let f : ZMod n -> ZMod m -> T, and let F : Z x Z -> T be its literal periodic plane lift, F(x,y) = f([x]n,[y]m) for every pair of integers. The source quantifies over an applicable R <= D8 and over h in {r, r3, rf, r3f} belonging to R. The internal constructors are deliberately separate from those source labels: source r has A_r(x,y)=(-y,x) and uses Lean a=.r3; source r3 has A_r3(x,y)=(y,-x) and uses a=.r; source rf has A_rf(x,y)=(y,x) and uses a=.rf; source r3f has A_r3f(x,y)=(-y,-x) and uses a=.r3f. In every row rho(d) is the original design action d*h. The square constants (q-1,0), (0,q-1), (0,0), and (q-1,q-1) illustrate the source convention for a q by q representative; they do not impose a D8 action on an unequal rectangle.

Write u for the chosen integer representative of the source translation and c for the actual integral affine offset after the linear map. The decorated graph is sent by (z,d) -> (A_h(z+u)+c, d*h). Fixedness of that graph, together with uniqueness of its design label, gives exactly F(A_h(z+u)+c) = F(z)·h. Conversely, this covariance and bijectivity of the affine cell map give graph equality. Thus the theorem is instantiated with shift=u, center=c, the internal constructor in the table, and rho(d)=d·h; every allowed translation and center stays in scope, and changing u by a rectangular period is handled by the literal periodic lift.

Then g = gcd(n,m) is positive and there is a genuine function H : ZMod g -> ZMod g -> T whose plane lift is pointwise equal to F. Thus the original decorated plane is equivalent to a g by g torus with the same tile type and the identical labels at every plane cell. The statement covers equal or unequal dimensions, unit dimensions, nonprimitive presentations, and all four actions; all quotient representatives and the entire product quotient are included, and it makes no claim that the square presentation is minimal. The same T is retained: no design relabeling, orientation loss, or abstract period-only replacement occurs.

The proof records the two source periods as an additive subgroup of Z x Z. Affine covariance transports a period through each signed swap map because the ordered shift and center combine to a fixed affine translation whose constant cancels after choosing a preimage. The four cases therefore give both coordinate periods n and m. Nat.gcd_eq_gcd_ab supplies the two gcd periods by integer combinations, and canonical ZMod representatives define H; the period subgroup proves representative independence and the exact plane-lift identity. No unequal finite quotient is given a fictitious D8 action, and no color-triviality or extra source hypothesis is used.

## References

- Truth anchor: `D5/S3/Combinatorics/TorusTilings/KageyKeehnRectangularTorus.rectangular_torus_gcd_descent`
