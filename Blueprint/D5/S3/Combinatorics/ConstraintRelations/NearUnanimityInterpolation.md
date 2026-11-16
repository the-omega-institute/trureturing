# Finite-coordinate near-unanimity interpolation

## Abstract

A single fixed near-unanimity operation interpolates every finite coordinate set from smaller projections.

Let I be any type in universe u and X(i) any family of types in an independent universe v. Tuple(X) denotes the dependent product of the X(i). Operations(X,k) denotes the family of functions nu(i) from (Fin(k) to X(i)) to X(i). Neither I nor any X(i) is required to be finite.

For tuples r and theta and a finite coordinate set T, Agree(r,theta,T) means that r(i)=theta(i) for every i in T. For values a,b in X(i) and bad in Fin(k), OneException(a,b,bad) is the function taking value b at bad and a at every other index. Combine(nu,rows) is the tuple whose ith coordinate is nu(i) applied to the k values rows(j)(i).

The near-unanimity law and coordinatewise preservation have the following full meanings:

$\forall i \in I,\; \forall a \in \operatorname{X}\left(i\right),\; \forall b \in \operatorname{X}\left(i\right),\; \forall bad \in \operatorname{Fin}\left(k\right),\; \operatorname{nu}\left(i, \operatorname{OneException}\left(a, b, bad\right)\right) = a$

$\forall rows \in (\operatorname{Fin}\left(k\right))\to(\operatorname{Tuple}\left(X\right)),\; (\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{rows}\left(j\right) \in R) \Rightarrow (\operatorname{Combine}\left(nu, rows\right) \in R)$

**Theorem 1.1 (Interpolation on a finite coordinate set).**

$$\forall I \in \operatorname{Type}\left(u\right),\; \forall X \in (I)\to(\operatorname{Type}\left(v\right)),\; \forall k \in \operatorname{Nat}\left(\right),\; \forall nu \in \operatorname{Operations}\left(X, k\right),\; \forall R \in \operatorname{Set}\left(\operatorname{Tuple}\left(X\right)\right),\; \forall theta \in \operatorname{Tuple}\left(X\right),\; \forall F \in \operatorname{Finset}\left(I\right),\; ((3 \le k) \land ((\operatorname{NULaw}\left(nu\right)) \land ((\operatorname{Preserves}\left(nu, R\right)) \land (\forall T \in \operatorname{Finset}\left(I\right),\; ((T \subseteq F) \land (\operatorname{card}\left(T\right) < k)) \Rightarrow (\exists r \in \operatorname{Tuple}\left(X\right),\; (r \in R) \land (\operatorname{Agree}\left(r, theta, T\right))))))) \Rightarrow (\exists r \in \operatorname{Tuple}\left(X\right),\; (r \in R) \land (\operatorname{Agree}\left(r, theta, F\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/NearUnanimityInterpolation.finite_coordinate_interpolation` (`✓ std3`). ∎

*Citation.* Libor Barto; Andrei Krokhin; Ross Willard (2017). *Polymorphisms, and How to Use Them*. DOI: [10.4230/DFU.Vol7.15301.1](https://doi.org/10.4230/DFU.Vol7.15301.1). URL: <https://drops.dagstuhl.de/entities/document/10.4230/DFU.Vol7.15301.1>.

*Commentary.*

Here NULaw and Preserves denote exactly the two displayed conditions. Every small projection witness is an actual member of R. In particular T may be empty: its hypothesis requires R to be nonempty. Empty F is included. The operation has this one fixed arity k; a family of operations at all arities is not assumed. There is no assumption of symmetry, associativity or coherent choices of local witnesses.

Proof by strong induction on the finite coordinate set F. If its size is less than k, take the supplied local witness for F itself. Otherwise choose k distinct elements of F. For each chosen element, induction gives a member of R agreeing with theta after deleting that element. Closure places the coordinatewise combination of these k members in R. At any coordinate of F at most one chosen deletion can remove that coordinate. All other rows therefore have value theta there, and the near-unanimity law makes the combination equal theta at that coordinate.

Example 72, pages 34–35, of Barto, Krokhin and Willard gives the classical subpower generation mechanism for a common carrier. The proof here establishes the stated dependent-coordinate finite interpolation theorem. When I is infinite, interpolation on every finite F is not a claim that theta itself belongs to R. No compactness or infinite-coordinate extension is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/NearUnanimityInterpolation.finite_coordinate_interpolation`
