# The Kagey--Keehn Rectangular-Torus GCD Descent

## Abstract

A decorated plane lift fixed by a translated transposing right action descends to the square torus whose side is the gcd of the source periods.

**Theorem 1.1 (Every four-way transposing fixed plane descends to a gcd square).**

Lean statement: `D5/S3/Combinatorics/KageyKeehnRectangularTorus.rectangular_torus_gcd_descent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/KageyKeehnRectangularTorus.rectangular_torus_gcd_descent` (`✓ std3`). ∎

*Resolves.* `Problems/kagey-keehn-2023-rectangular-torus` (proved) by `D5/S3/Combinatorics/KageyKeehnRectangularTorus.rectangular_torus_gcd_descent`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kagey-keehn-2023-rectangular-torus","declaration_gid":"D5/S3/Combinatorics/KageyKeehnRectangularTorus.rectangular_torus_gcd_descent","resolution_kind":"proved"} -->

*Citation.* Peter Kagey; William Keehn (2023). *Counting tilings of the n x m grid, cylinder, and torus*. URL: <https://arxiv.org/abs/2311.13072v1>.

*Commentary.*

For arbitrary positive natural dimensions n and m, let T be any type, let f be a function from ZMod n and ZMod m into T, and let F : Z x Z -> T be its literal decorated plane lift: F(x,y) = f([x]n,[y]m) for every pair of integers. Choose one of the four source right actions r, r3, rf, or r3f. Their linear coordinate maps are respectively (y,-x), (-y,x), (y,x), and (-y,-x).

For an arbitrary integer shift s, affine center c, and tile-design map rho : T -> T, assume the actual plane covariance F(A (z + s) + c) = rho(F z) for every z, where A is the selected right-action map. This keeps the source order of cyclic translation before the action. The free center c includes every affine center constant in the finite rectangular representatives, while rho retains an arbitrary decorated right action.

Then g = gcd(n,m) is positive and there is a genuine function H : ZMod g -> ZMod g -> T whose plane lift is pointwise equal to F. Thus the original decorated plane is equivalent to a g by g torus with the same tile type and the identical labels at every plane cell. The statement covers equal or unequal dimensions, unit dimensions, nonprimitive presentations, and all four actions; it makes no claim that the square presentation is minimal.

The proof records the two source periods as an additive subgroup of Z x Z. Affine covariance transports a period through each signed swap map because the ordered shift and center combine to a fixed affine translation whose constant cancels after choosing a preimage. The four cases therefore give both coordinate periods n and m. Nat.gcd_eq_gcd_ab supplies the two gcd periods by integer combinations, and canonical ZMod representatives define H; the period subgroup proves representative independence and the exact plane-lift identity. No unequal finite quotient is given a fictitious D8 action, and no color-triviality or extra source hypothesis is used.

## References

- Truth anchor: `D5/S3/Combinatorics/KageyKeehnRectangularTorus.rectangular_torus_gcd_descent`
