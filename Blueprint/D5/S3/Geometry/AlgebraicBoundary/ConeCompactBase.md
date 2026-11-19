# An actual positive functional and compact base

## Abstract

Positive normalization constructed from a finite real closed salient cone.

Let E be a finite-dimensional real normed vector space and C a closed convex cone containing zero, with no nonzero vector belonging to both C and -C. There exists a continuous linear functional u that is strictly positive on every nonzero element of C. The actual section consisting of the x in C with u(x)=1 is compact and convex. The functional is constructed from C; it is not an input assumption.

Intersect the original cone with the unit sphere. This set is compact. For each point x in that intersection, salience excludes -x from C. Cone separation supplies a continuous linear functional nonnegative on all of C and strictly positive at x. Its positive locus is open. A finite subcover of these loci on the compact sphere section gives finitely many such functionals. Their sum is nonnegative on the entire cone and strictly positive on every unit cone vector. Normalizing any nonzero cone vector to unit norm proves strict positivity on the entire original cone.

Compactness and convexity of the resulting actual section use the existing CircuitBalancedConfirmation base_compact and base_convex declarations with this constructed functional. The construction also permits the zero cone, whose section is empty. For a nonzero carrier and a cone with nonempty interior, choose a nonzero interior point a and normalize it to b=a/u(a). The positive dilation preserves the original cone interior. Translating the actual section by b gives the compact set K={v in ker(u): b+v belongs to C}. It has nonempty interior in ker(u). At every v, membership in the interior of K is equivalent to b+v belonging to the interior of the original cone, and membership in the entire frontier of K is equivalent to b+v belonging to the entire frontier of the original cone.

For the nontrivial direction of the interior equivalence, use the continuous projection q(y)=y-u(y)b into ker(u) and the normalization N(y)=q(y)/u(y), continuous near each point b+v since u(b+v)=1. A relative interior neighborhood in K pulls back under N to an ambient neighborhood. Intersect it with u(y)>0. The exact equality y=u(y)(b+N(y)) places that entire neighborhood in the original cone. The reverse implication uses continuity of v to b+v. Closedness then gives the exact frontier equivalence. No supplied positive functional, base, smoothness or polynomial assumption enters this construction. The polynomial degree and homogeneous-generator correspondence remains a separate obligation.

## References

- Dependency: [D5/S3/Quantum/Foundation/CircuitBalancedConfirmation](../../Quantum/Foundation/CircuitBalancedConfirmation.md)
