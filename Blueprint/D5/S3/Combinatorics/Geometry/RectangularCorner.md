# Rectangular corners of order-convex sets

## Abstract

Consecutive global minima describe and count strict global floor corners.

For all natural m and n, Point(m,n) is Fin m times Fin n with coordinatewise order. Let I be an order-convex subset and let a belong to I. LocalMin(I,a,u) means that u is a global minimum of I and u is at most a. Adjacent(I,a,u,v) means that u and v satisfy LocalMin, the first coordinate of u is smaller, and no other such minimum has first coordinate strictly between them. Corner(I,a,b) means that b is globally maximal in the non-strict lower closure of I minus I, and both coordinates of b are strictly smaller than those of a. Global extremality is retained before imposing the coordinate restrictions. The dimensions may be zero; membership of a supplies nonemptiness whenever a is present.

**Definition 1.1 (The finite rectangle).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; Point(m, n) = Fin(m) \times Fin(n)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RectangularCorner.Point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Point(m,n) is Fin m times Fin n; the order compares both coordinates.

**Definition 1.2 (Global minima below an included point).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall I \in Set(Point(m, n)),\; \forall a \in Point(m, n),\; \forall u \in Point(m, n),\; (LocalMin(I, a, u)) \Leftrightarrow ((Minimal(I, u)) \land (u \le a))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RectangularCorner.LocalMin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Minimality is taken in all of I. The additional condition u at most a selects the minima below a.

**Definition 1.3 (Consecutive minima by row).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall I \in Set(Point(m, n)),\; \forall a \in Point(m, n),\; \forall u \in Point(m, n),\; \forall v \in Point(m, n),\; (Adjacent(I, a, u, v)) \Leftrightarrow ((LocalMin(I, a, u)) \land ((LocalMin(I, a, v)) \land ((val(u_{1}) < val(v_{1})) \land (\forall w \in Point(m, n),\; (LocalMin(I, a, w)) \Rightarrow (\neg((val(u_{1}) < val(w_{1})) \land (val(w_{1}) < val(v_{1}))))))))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RectangularCorner.Adjacent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two selected global minima have increasing first coordinates and no selected global minimum strictly between those coordinates.

**Definition 1.4 (Strict global floor corners).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall I \in Set(Point(m, n)),\; \forall a \in Point(m, n),\; \forall b \in Point(m, n),\; (Corner(I, a, b)) \Leftrightarrow ((Maximal(lowerClosure(I) \setminus I, b)) \land ((val(b_{1}) < val(a_{1})) \land (val(b_{2}) < val(a_{2}))))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RectangularCorner.Corner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Maximality is taken in the entire lower closure of I minus I. Both strict coordinate inequalities are imposed afterward.

**Theorem 1.5 (Consecutive minima give an exact corner).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall I \in Set(Point(m, n)),\; (OrdConnected(I)) \Rightarrow (\forall a \in Point(m, n),\; \forall u \in Point(m, n),\; \forall v \in Point(m, n),\; \forall b \in Point(m, n),\; (a \in I) \Rightarrow ((Adjacent(I, a, u, v)) \Rightarrow ((val(b_{1}) + 1 = val(v_{1})) \Rightarrow ((val(b_{2}) + 1 = val(u_{2})) \Rightarrow (Corner(I, a, b))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RectangularCorner.adjacent_gives_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u and v be consecutive selected global minima. If b has first coordinate value one less than v and second coordinate value one less than u, then b is a strict global floor corner below a. The antichain order forces the second coordinates to decrease. Absence of an intermediate minimum excludes included points below b; order-convexity proves global maximality of b in the floor.

**Theorem 1.6 (A corner recovers consecutive minima).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall I \in Set(Point(m, n)),\; (OrdConnected(I)) \Rightarrow (\forall a \in Point(m, n),\; \forall b \in Point(m, n),\; (a \in I) \Rightarrow ((Corner(I, a, b)) \Rightarrow (\exists u \in Point(m, n),\; \exists v \in Point(m, n),\; (Adjacent(I, a, u, v)) \land ((val(b_{1}) + 1 = val(v_{1})) \land (val(b_{2}) + 1 = val(u_{2}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RectangularCorner.corner_gives_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every strict global floor corner b below a has global minima u and v below a that are consecutive by first coordinate, with b's first coordinate value plus one equal to v's and b's second coordinate value plus one equal to u's. The two immediate coordinate successors of b belong to I by global floor maximality; global minima below those successors recover u and v.

**Theorem 1.7 (The exact corner count).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall I \in Set(Point(m, n)),\; (OrdConnected(I)) \Rightarrow (\forall a \in Point(m, n),\; (a \in I) \Rightarrow (card(\{b \in Point(m, n) \mid Corner(I, a, b)\}) + 1 = card(\{u \in Point(m, n) \mid LocalMin(I, a, u)\})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RectangularCorner.rectangular_corner_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order-convex I and a in I, the number of strict global floor corners below a plus one equals the number of global minima of I at most a. The proof constructs a bijection from corners to the selected minima with their first minimum removed. Both geometric directions are used to prove the inverse and uniqueness. This general structural identity does not assert the full rowmotion homomesy conjecture, a toggle transport theorem, or an orbit identity.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/RectangularCorner.Adjacent`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RectangularCorner.Corner`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RectangularCorner.LocalMin`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RectangularCorner.Point`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RectangularCorner.adjacent_gives_corner`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RectangularCorner.corner_gives_adjacent`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RectangularCorner.rectangular_corner_card`
